(** * CliffordSynthesis.v — direction ① (third brick): consolidation, and the
      non-terminating side generalised beyond 3-4-5.

    Elements: the integer Chebyshev-trace sequences c s t k (NivenGeneral.v)
    Roles:    a single-qubit rational rotation as a PROCESS — terminating
              (closes → an Element; the Z₄/Clifford core) or non-terminating
              (never closes → a role-limit; outside Clifford)
    Rules:    any 2cosθ = s/t with t ≥ 2 (gcd(s,t)=1) ⟹ the rotation is a
              NON-TERMINATING process (no period) — `niven_general`; instantiated
              here for the 5-12-13 and 8-15-17 rotations (beyond 3-4-5)

    PROCESS-NATIVE CONSOLIDATION OF ① (Clifford = the finitization boundary).
    In ToS every single-qubit rational rotation is a PROCESS (its cmul-orbit, a
    ℚ-sequence under a Rule). The boundary is purely whether that process
    TERMINATES:

      TERMINATING (closes → an Element; the ℚ-finite Clifford core):
        · the real Pauli/Clifford group {±I,±X,±Z,±XZ} closes — a finite group of
          order 8 (CliffordBoundary.v);
        · the S-gate phase i = (0,1) closes at order 4 (CliffordPhaseGate.v).

      NON-TERMINATING (never closes → a role-limit; outside Clifford):
        · the 3-4-5 rotation is aperiodic (CliffordBoundary.v / NivenGeneral.v);
        · the S-vs-T cut: the T-gate phase is the non-terminating √2-process
          (CliffordPhaseGate.v);
        · GENERALLY, `niven_general`: ANY 2cosθ = s/t with t ≥ 2 gives a
          non-terminating process. This file instantiates it beyond 3-4-5 for the
          5-12-13 (s=10,t=13) and 8-15-17 (s=16,t=17) rotations.

    The conjecture (Gottesman–Knill bridge): terminating process ⟺ Clifford ⟺
    classically simulable; non-terminating ⟺ non-Clifford ⟺ where quantum
    advantage lives (and Palmer's RaQM qubit ceiling is a finitist bound on the
    accessibility of the non-terminating side).

    HONEST FRONTIER. The full capstone — "a rational circle point (a,b) is a
    TERMINATING rotation IFF (a,b) ∈ Z₄" stated on the cmul-orbit directly — needs
    a bridge from the cmul-orbit to the c s t sequence of Niven (Gaussian-integer /
    algebraic-integer machinery). niven_general already gives the t ≥ 2 ⟹ non-
    terminating half for the trace sequence; the cmul-orbit bridge is future work.

    ============ E/R/R разбор ============
      Rules (L5): t≥2 ⟹ процесс cₖ незавершающийся (niven_general); инстансы 13, 17.
      Roles (L4): поворот = процесс; ЗАВЕРШАЮЩИЙСЯ (терминус=Element, Clifford) или
                  НЕЗАВЕРШАЮЩИЙСЯ (role-limit, вне Clifford).
      Elements  : целочисленные следы cₖ (L1+P4).
    ДИАГНОСТИКА (P4): ① = классификация поворотов по завершаемости процесса.
    Завершающиеся = Z₄/Clifford-ядро; незавершающиеся (любой t≥2) = role-limits.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import stdlib.NivenGeneral.
Open Scope Z_scope.

(* ===== Non-terminating beyond 3-4-5: instances of niven_general ========= *)

(** The 5-12-13 rotation (cosθ = 5/13, so 2cosθ = 10/13) is a NON-TERMINATING
    process: its trace sequence never reaches a period. *)
Theorem rotation_5_12_13_nonterminating :
  forall k, ~ Z.divide 13 (c 10 13 (S k)).
Proof. apply niven_general; [ vm_compute; reflexivity | lia ]. Qed.

(** The 8-15-17 rotation (cosθ = 8/17, so 2cosθ = 16/17) is likewise a
    NON-TERMINATING process. *)
Theorem rotation_8_15_17_nonterminating :
  forall k, ~ Z.divide 17 (c 16 17 (S k)).
Proof. apply niven_general; [ vm_compute; reflexivity | lia ]. Qed.

(* ===== The non-terminating side of ①, consolidated ===================== *)

(** Beyond 3-4-5: more single-qubit rational rotations are non-terminating
    processes (role-limits, outside the Clifford core). The general engine is
    `niven_general` — ANY 2cosθ = s/t with t ≥ 2 is non-terminating. *)
Theorem nonterminating_rotations :
  (forall k, ~ Z.divide 13 (c 10 13 (S k))) /\
  (forall k, ~ Z.divide 17 (c 16 17 (S k))).
Proof.
  split; [ exact rotation_5_12_13_nonterminating
         | exact rotation_8_15_17_nonterminating ].
Qed.
