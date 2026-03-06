"""
ToS-Lang AI Interface — LLM Generation + Verified Execution

Flow:
    1. Human provides specification (natural language)
    2. LLM generates ToS-Lang expression
    3. Verified type checker confirms well-formedness (extracted from Coq)
    4. Verified evaluator produces result (extracted from Coq)
    5. Certificate attached: proven correct by Coq

The type checker and evaluator are EXTRACTED from Coq proofs:
    - typecheck_sound: typecheck G e = Some T -> expr_has_type G e T
    - type_safety: well-typed + multi-step -> result is well-typed
    - verified_pipeline: typecheck OK -> eval preserves type + progress

Author: Horsocrates | 2026-03-06
"""

import subprocess
import json
from typing import Optional, Any
from dataclasses import dataclass, field


# ================================================================= #
# 1. Result Types                                                     #
# ================================================================= #

@dataclass
class VerifiedResult:
    """Result from the verified pipeline."""
    status: str  # "verified" | "type_error" | "parse_error"
    expression: Optional[str] = None
    type_str: Optional[str] = None
    value: Optional[str] = None
    error: Optional[str] = None
    certificate: Optional[str] = None
    backing_theorems: list[str] = field(default_factory=list)

    def is_verified(self) -> bool:
        return self.status == "verified"

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {"status": self.status}
        if self.expression:
            d["expression"] = self.expression
        if self.type_str:
            d["type"] = self.type_str
        if self.value:
            d["value"] = self.value
        if self.error:
            d["error"] = self.error
        if self.certificate:
            d["certificate"] = self.certificate
        if self.backing_theorems:
            d["backing_theorems"] = self.backing_theorems
        return d


# ================================================================= #
# 2. ToS-Lang Verifier (calls extracted OCaml binary)                 #
# ================================================================= #

class ToSLangVerifier:
    """Interface to the verified ToS-Lang type checker + evaluator.

    Uses the tos_check binary (compiled from Coq-extracted OCaml).
    The binary's core functions are PROVEN CORRECT:
        - TypeChecker.typecheck  (proven sound by typecheck_sound)
        - Evaluator.eval_fuel    (proven type-preserving by type_safety)
        - Evaluator.classify_eval (proven correct by classify_value_correct)
    """

    def __init__(self, binary_path: str = "./tos_check"):
        self.binary = binary_path

    def verify_and_run(
        self,
        tos_source: str,
        fuel: int = 1000,
    ) -> VerifiedResult:
        """Submit ToS-Lang source for verification and execution.

        Args:
            tos_source: ToS-Lang source code string
            fuel: Maximum evaluation steps (default 1000)

        Returns:
            VerifiedResult with status, type, value, and certificate
        """
        try:
            result = subprocess.run(
                [self.binary, "--stdin", "--fuel", str(fuel)],
                input=tos_source,
                capture_output=True,
                text=True,
                timeout=30,
            )
        except FileNotFoundError:
            return VerifiedResult(
                status="error",
                error=f"Binary not found: {self.binary}. "
                      f"Build with: cd tos_lang && make",
            )
        except subprocess.TimeoutExpired:
            return VerifiedResult(
                status="error",
                error="Evaluation timed out (30s limit)",
            )

        if result.returncode == 0:
            lines = result.stdout.strip().split("\n")
            type_str = None
            value = None
            for line in lines:
                if line.startswith("Type: "):
                    type_str = line[6:]
                elif line.startswith("Value: "):
                    value = line[7:]
                elif line.startswith("Partial"):
                    value = line

            return VerifiedResult(
                status="verified",
                expression=tos_source.strip(),
                type_str=type_str,
                value=value,
                certificate=(
                    "Well-typed -> E/R/R well-formed -> "
                    "no paradox (Coq-proven)"
                ),
                backing_theorems=[
                    "TypeChecker.typecheck_sound",
                    "TypeChecker.typecheck_ann_sound",
                    "Evaluator.verified_pipeline",
                    "TypeSafety.tos_lang_main_theorem",
                    "AIInterface.ai_generation_safe",
                ],
            )
        else:
            return VerifiedResult(
                status="type_error" if "Type error" in result.stderr
                       else "parse_error",
                expression=tos_source.strip(),
                error=result.stderr.strip(),
            )


# ================================================================= #
# 3. AI Generation + Verification Loop                                #
# ================================================================= #

TOS_LANG_SYNTAX = """\
ToS-Lang syntax:
  n               -- natural number constant
  \\(x : T). e     -- lambda with type annotation
  e1 e2           -- application
  (e1, e2)        -- pair
  fst e           -- first projection
  snd e           -- second projection
  observe e n     -- process observation at step n
  resolve e       -- L5-resolution
  system L1       -- system at level 1

Types:
  Nat             -- natural numbers
  T1 -> T2        -- function type
  T1 * T2         -- pair type
  Process T       -- process type
  Layer T         -- layer type
  System L1       -- system type at level 1
"""


class ToSLangAI:
    """AI-native interface for ToS-Lang.

    Full loop:
        1. Human describes what they want (natural language)
        2. LLM generates ToS-Lang code
        3. Verified type checker confirms well-formedness
        4. Verified evaluator produces result
        5. Certificate attached: "proven correct by Coq"

    The verification step is SOUND by Coq proof:
        If typecheck_ann returns Some T, then expr_has_type holds,
        and evaluation preserves that type (ai_generation_safe).
    """

    def __init__(
        self,
        verifier: Optional[ToSLangVerifier] = None,
        max_retries: int = 2,
    ):
        self.verifier = verifier or ToSLangVerifier()
        self.max_retries = max_retries

    def _build_generation_prompt(self, spec: str) -> str:
        return f"""\
Generate a ToS-Lang expression for the following specification:

{spec}

{TOS_LANG_SYNTAX}

Output ONLY the ToS-Lang expression, nothing else.
No explanation, no markdown, no comments — just the expression."""

    def _build_retry_prompt(
        self,
        spec: str,
        previous_code: str,
        error: str,
    ) -> str:
        return f"""\
Your previous ToS-Lang expression had an error:
{error}

Previous attempt:
{previous_code}

Original specification:
{spec}

{TOS_LANG_SYNTAX}

Fix the expression. Output ONLY the corrected ToS-Lang expression."""

    async def generate_and_verify(
        self,
        spec: str,
        llm_client: Any,
        fuel: int = 1000,
    ) -> dict[str, Any]:
        """Full AI loop: spec -> generate -> verify -> result.

        Args:
            spec: Natural language specification
            llm_client: Any LLM client with async generate(prompt) method
            fuel: Maximum evaluation steps

        Returns:
            Dict with generation result, verification status, certificate
        """
        prompt = self._build_generation_prompt(spec)
        attempts: list[dict[str, Any]] = []

        for attempt in range(1, self.max_retries + 1):
            # AI generates
            response = await llm_client.generate(prompt)
            tos_source = response.strip()

            # System verifies (SOUND by Coq proof)
            result = self.verifier.verify_and_run(tos_source, fuel=fuel)
            attempts.append({
                "attempt": attempt,
                "code": tos_source,
                "result": result.to_dict(),
            })

            if result.is_verified():
                return {
                    "spec": spec,
                    "generated_code": tos_source,
                    "verified": True,
                    "attempts": attempts,
                    **result.to_dict(),
                }

            # Build retry prompt with error feedback
            prompt = self._build_retry_prompt(
                spec, tos_source, result.error or "Unknown error"
            )

        # All retries exhausted
        return {
            "spec": spec,
            "verified": False,
            "attempts": attempts,
            "error": "All retry attempts failed verification",
        }


# ================================================================= #
# 4. Standalone Demo (no LLM required)                                #
# ================================================================= #

def demo():
    """Demonstrate the verification pipeline without an LLM."""
    verifier = ToSLangVerifier()

    examples = [
        ("Identity applied to 42", r"\(x : Nat). x) 42"),
        ("Pair projection", r"fst (42, 7)"),
        ("Constant", "42"),
        ("Higher-order", r"(\(f : Nat -> Nat). f 42) (\(x : Nat). x)"),
        ("Ill-typed (should fail)", r"fst 42"),
    ]

    print("=" * 60)
    print("ToS-Lang Verified Pipeline Demo")
    print("=" * 60)

    for desc, source in examples:
        print(f"\n--- {desc} ---")
        print(f"Source: {source}")
        result = verifier.verify_and_run(source)
        print(f"Status: {result.status}")
        if result.type_str:
            print(f"Type: {result.type_str}")
        if result.value:
            print(f"Value: {result.value}")
        if result.certificate:
            print(f"Certificate: {result.certificate}")
        if result.error:
            print(f"Error: {result.error}")


if __name__ == "__main__":
    demo()
