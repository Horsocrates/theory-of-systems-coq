(** * QubitCeiling.v — Palmer's qubit ceiling as a granular prediction ToS does NOT make.
      A granular substrate (finite resolution of the invariant set, Palmer) implies a maximum
      number of qubits whose Walsh/Hadamard state is EXACTLY representable; ToS (an unbounded
      process, not a bounded substrate) has no such ceiling.  The n-qubit Walsh normalization is
      1/√(2ⁿ): for n even = 2m it is the rational 1/2ᵐ (an Element, denominator 2ᵐ), and the
      denominator 2ᵐ GROWS unboundedly, so a granular theory with resolution ≤ Q represents it
      exactly only while 2ᵐ ≤ Q — a ceiling n_max = 2⌊log₂Q⌋ that ToS (unbounded) does not impose.
      For n odd, √(2ⁿ) is a role-limit (2ⁿ not a perfect square, via GeneralSqrt).  Same no-go as
      GranularFloor: bounded resolution ⟹ ceiling; unbounded process ⟹ none.

    Elements: the denominators 2ᵐ; the even-n perfect-square normalizations 2^(2m)=(2ᵐ)²;
              concrete powers 2,4,8,16 (L1 + P4)
    Roles:    Element side = an exactly-representable Walsh state (n even, denominator 2ᵐ ≤ Q);
              role-limit = odd-n √2 amplitudes and the n→∞ unbounded-denominator process
    Rules:    n even = 2m ⟹ √(2ⁿ)=2ᵐ rational (perfect-square normalization); n odd ⟹ role-limit;
              the denominator 2ᵐ is unbounded, so a granular resolution Q is exceeded at some m

    THE DEEP POINT — Palmer's ceiling is a granular theory's; ToS does not make it.  For n even
    the Walsh normalization is exactly rational because 2^(2m) = (2ᵐ)² is a perfect square
    (`even_walsh_perfect_square`); for n odd it is a role-limit because 2^(2m+1) = 2·(2ᵐ)² is NOT
    a perfect square (`odd_walsh_role_limit`, reducing to GranularFloor/GeneralSqrt: k²=2·j² ⟹ √2
    rational).  The even-n amplitude has denominator 2ᵐ, which is UNBOUNDED (`qubit_ceiling`: for
    any granular resolution Q there is an m with 2ᵐ > Q) — so a granular theory has a qubit ceiling
    (beyond it the state is not exactly representable), while ToS (the denominator is an unbounded
    process, P4) has none.  The even/odd split is GeneralSqrt (2ⁿ a perfect square ⟺ n even).  So
    "is there a qubit ceiling?" reduces to "is the substrate granular (bounded) or a process
    (unbounded)?" — Palmer says granular (ceiling), ToS says process (no ceiling).  Element = an
    exactly-representable state; role-limit = the unbounded process it never bounds.

    ============ E/R/R разбор ============
      Rules (L5): n чётно=2m ⟹ √(2ⁿ)=2ᵐ рационально (2^(2m)=(2ᵐ)² полный квадрат); n нечётно ⟹
                  role-limit (2^(2m+1)=2·(2ᵐ)² не квадрат); знаменатель 2ᵐ неограничен ⟹ превосходит Q.
      Roles (L4): Element = точно-представимое состояние Уолша (n чётно, 2ᵐ≤Q); role-limit = нечётно-n
                  √2-амплитуды и процесс n→∞. Гранулярный субстрат ⟹ потолок; ToS-процесс ⟹ нет.
      Elements  : знаменатели 2ᵐ; чётно-n полно-квадратные нормировки; степени 2,4,8,16 (L1+P4).
    ДИАГНОСТИКА (P4): потолок кубитов Палмера = предсказание ГРАНУЛЯРНОЙ теории; ToS его НЕ делает (2ᵐ —
    неограниченный процесс, не ограниченный субстрат). Тот же no-go, что GranularFloor. Чётно/нечётный разлом =
    GeneralSqrt. ToS с Гизином (неограниченный процесс), против Палмера (гранулярный потолок).

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import stdlib.GeneralSqrt.
From ToS Require Import stdlib.GranularFloor.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Powers of two (the Walsh-amplitude denominators)                       *)
(* ===================================================================== *)

Fixpoint pow2 (m : nat) : Z :=
  match m with O => 1 | S m' => 2 * pow2 m' end.

Lemma pow2_succ : forall m, pow2 (S m) = 2 * pow2 m.
Proof. reflexivity. Qed.

Lemma pow2_pos : forall m, 0 < pow2 m.
Proof. induction m as [| m IH]; [ reflexivity | rewrite pow2_succ; lia ]. Qed.

(** The additive law 2^(a+b) = 2^a · 2^b, hence 2^(2m) = (2^m)². *)
Lemma pow2_add : forall a b, pow2 (a + b) = pow2 a * pow2 b.
Proof.
  induction a as [| a IH]; intros b.
  - rewrite Nat.add_0_l. change (pow2 0) with 1. ring.
  - rewrite Nat.add_succ_l, (pow2_succ (a + b)), (pow2_succ a), IH. ring.
Qed.

Lemma pow2_double : forall m, pow2 (m + m) = pow2 m * pow2 m.
Proof. intros m. apply pow2_add. Qed.

(** The denominator grows at least linearly, hence is unbounded. *)
Lemma pow2_lower : forall m, 1 + Z.of_nat m <= pow2 m.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - rewrite pow2_succ, Nat2Z.inj_succ. pose proof (pow2_pos m). lia.
Qed.

(* ===================================================================== *)
(*  Even-qubit Walsh: an Element (perfect-square normalization)            *)
(* ===================================================================== *)

(** ★ For n = 2m qubits, 2ⁿ = 2^(2m) is a PERFECT SQUARE (2ᵐ)², so √(2ⁿ) = 2ᵐ is rational — the
    Walsh amplitude 1/2ᵐ is an Element, exactly representable. *)
Lemma even_walsh_perfect_square : forall m : nat, exists r : Z, pow2 (m + m) = r * r.
Proof. intros m. exists (pow2 m). apply pow2_double. Qed.

(* ===================================================================== *)
(*  Odd-qubit Walsh: a role-limit (√2-flavoured, via GeneralSqrt)          *)
(* ===================================================================== *)

(** ★ For n = 2m+1 qubits, 2ⁿ = 2·(2ᵐ)² is NOT a perfect square, so √(2ⁿ) is a role-limit: a
    rational k with k² = 2^(2m+1) would give (k/2ᵐ)² = 2, i.e. √2 rational (GranularFloor). *)
Lemma odd_walsh_role_limit : forall (m : nat) (k : Z), k * k <> pow2 (S (m + m)).
Proof.
  intros m k Heq.
  assert (Hns2 : forall j : Z, j * j <> 2) by (intros j; apply (not_square_strict j 1 2); lia).
  apply (nonsquare_gap_nonzero 2 k (pow2 m) Hns2 (pow2_pos m)).
  rewrite Heq, pow2_succ, pow2_double. ring.
Qed.

(* ===================================================================== *)
(*  THE QUBIT CEILING: 2ᵐ exceeds any granular resolution Q               *)
(* ===================================================================== *)

(** ★ The even-qubit Walsh denominator 2ᵐ is UNBOUNDED: for any granular resolution Q there is an
    m with 2ᵐ > Q.  So a granular theory (resolution ≤ Q) cannot exactly represent the (2m)-qubit
    Walsh state beyond that m — a qubit CEILING; ToS (the denominator is an unbounded process)
    imposes none. *)
Theorem qubit_ceiling : forall Q : Z, exists m : nat, Q < pow2 m.
Proof.
  intros Q. exists (Z.to_nat (Z.max 0 Q)).
  pose proof (pow2_lower (Z.to_nat (Z.max 0 Q))) as Hlo.
  rewrite Z2Nat.id in Hlo by lia. lia.
Qed.

(** Concrete denominators: 2¹=2, 2²=4, 2³=8, 2⁴=16 — a granular theory with resolution Q=10
    caps the exactly-representable Walsh denominator at 2³=8 (n=6 qubits); ToS does not. *)
Lemma pow2_concrete : pow2 1 = 2 /\ pow2 2 = 4 /\ pow2 3 = 8 /\ pow2 4 = 16.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Palmer's qubit ceiling, split by the finitization boundary:
      (a) EVEN n — the Walsh normalization is an Element (perfect square 2^(2m)=(2ᵐ)²,
          `even_walsh_perfect_square`);
      (b) ODD n — it is a role-limit (2^(2m+1) not a perfect square, `odd_walsh_role_limit`,
          reducing to GeneralSqrt);
      (c) CEILING — the denominator 2ᵐ is unbounded (`qubit_ceiling`): a granular theory has a
          qubit ceiling (resolution Q exceeded at some m), ToS does not.  So the ceiling is a
          granular prediction; ToS (unbounded process) does not make it. *)
Theorem qubit_ceiling_synthesis :
  (forall m : nat, exists r : Z, pow2 (m + m) = r * r)
  /\ (forall (m : nat) (k : Z), k * k <> pow2 (S (m + m)))
  /\ (forall Q : Z, exists m : nat, Q < pow2 m).
Proof.
  split; [ exact even_walsh_perfect_square | ].
  split; [ exact odd_walsh_role_limit | exact qubit_ceiling ].
Qed.
