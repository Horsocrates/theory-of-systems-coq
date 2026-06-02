(** * ProcessDiscreteTrig.v — Discrete orthogonality from explicit root-of-unity
      hypotheses: where the trigonometric boundary lies (Part VII, Batch 3 / proposal D)

    Elements: abstract character values χ k j ∈ ℚ; N sample points; finite sums
    Roles:    χ k = the k-th discrete character; the hypotheses = the algebraic content
              of roots of unity; orthogonality = role-relation among characters
    Rules:    GIVEN χ₀ = 1, the homomorphism χ_k·χ_{k'} = χ_{k+k'}, and the vanishing
              geometric sum Σ_j χ_m(j) = 0 (0 < m < N) — discrete orthogonality is a
              finite ℚ-theorem: Σ_j χ_k(j)·χ_{k'}(j) = N·[k+k'≡0]

    A "boundary formaliser" (per the GPT plan review). It does NOT construct sin, cos,
    complex exponentials, or Euler's formula — those are the transcendental P4 boundary
    of the trigonometric Fourier transform. Instead it makes PRECISE which algebraic
    hypotheses (a multiplicative character law + a vanishing geometric sum) turn
    trigonometric/DFT orthogonality into a finite, exact ℚ-statement. The transcendental
    facts about e^{2πik/N} are exactly the content of these named hypotheses; everything
    downstream is rational and 0 axioms.

    HONEST FRONTIER: the values χ k j = e^{2πikj/N} (or cos/sin) and the proof that they
    SATISFY these hypotheses need complex numbers / transcendental analysis — NOT built
    here. This file isolates the boundary, it does not cross it.

    ============ E/R/R разбор ============
      Rules (L5): χ₀=1, χ_k·χ_{k'}=χ_{k+k'}, Σ_j χ_m=0 (0<m<N) ⟹ ортогональность Σχ_kχ_{k'}=N·[k+k'≡0].
      Roles (L4): χ_k=роль-характер; гипотезы=алгебраическое содержание корней единицы.
      Elements  : абстрактные значения χ k j∈ℚ, N точек, конечные суммы (L1+P4).
    ДИАГНОСТИКА: дано алгебраические гипотезы — ортогональность точна над ℚ (0 акс);
    сами значения e^{2πik/N}/cos/sin и проверка гипотез — комплексные/трансцендентные (граница).

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.       (* q_sum_ext *)
From ToS Require Import process.ProcessCanonicalCommutator. (* q_sum_const *)

Open Scope Q_scope.

Section DiscreteChar.

Variable N : nat.
Variable chi : nat -> nat -> Q.   (* chi k j = the k-th character at sample point j *)

(* The three hypotheses encapsulate the algebraic content of roots of unity. *)
Hypothesis chi_0 : forall j, chi 0%nat j == 1.
Hypothesis chi_hom : forall k k' j, chi k j * chi k' j == chi (k + k')%nat j.
Hypothesis chi_sum_zero : forall m, (0 < m)%nat -> (m < N)%nat ->
  q_sum (fun j => chi m j) N == 0.

(** Zero frequency sums to N (it is the constant 1). *)
Lemma char_sum_full : q_sum (fun j => chi 0%nat j) N == inject_Z (Z.of_nat N).
Proof.
  transitivity (q_sum (fun _ : nat => 1) N).
  - apply q_sum_ext. intro j. apply chi_0.
  - rewrite (q_sum_const 1 N). ring.
Qed.

(** Discrete orthogonality: a finite ℚ-theorem under the named hypotheses. *)
Theorem discrete_orthogonality : forall k k', (k + k' < N)%nat ->
  q_sum (fun j => chi k j * chi k' j) N
  == (if (k + k' =? 0)%nat then inject_Z (Z.of_nat N) else 0).
Proof.
  intros k k' Hkk.
  transitivity (q_sum (fun j => chi (k + k')%nat j) N).
  { apply q_sum_ext. intro j. apply chi_hom. }
  destruct (k + k')%nat as [|s] eqn:E.
  - simpl. exact char_sum_full.
  - simpl. apply chi_sum_zero; lia.
Qed.

End DiscreteChar.

Print Assumptions discrete_orthogonality.
