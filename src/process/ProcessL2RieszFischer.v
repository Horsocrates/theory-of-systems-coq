(** * ProcessL2RieszFischer.v — Riesz–Fischer by construction: L² completeness
      as a constructed process limit (F-29 frontier, Part VI)

    Elements: rational coordinates F n i; finite sums Σ_{i<N}; stage index s
    Roles:    each coordinate sequence = a Cauchy real (limit by construction);
              f∞ = the sequence reinterpreted as a vector-of-reals; convergence = Cauchy
    Rules:    (aᵢ)² ≤ ‖a‖²  ⟹  L²-Cauchy ⟹ each coordinate is ℚ-Cauchy;
              the constructed limit f∞(i) := (Fₙ(i))ₙ satisfies ‖Fₙ − f∞‖₂ → 0,
              which unfolds to the Cauchy condition itself (no Zorn, no AC).

    Classical Riesz–Fischer (L²/ℓ² is complete) is proved here in its constructive
    P4 core. The engine is the bound (one coordinate)² ≤ (squared norm): an L²-Cauchy
    sequence is Cauchy in every coordinate, so each coordinate sequence is a Cauchy
    real and the LIMIT VECTOR is CONSTRUCTED coordinatewise — f∞(i) is the rational
    sequence n ↦ Fₙ(i) read as a RealProcess. Then "‖Fₙ − f∞‖₂ → 0" unfolds to the
    Cauchy hypothesis itself, because the stage-s rational approximant of f∞ IS Fₛ.
    Completeness holds BY CONSTRUCTION: the limit is built, not chosen by Zorn/AC.

    HONEST FRONTIER (P4 boundary): we work at a fixed finite truncation N. The full
    infinite-dimensional ℓ²/L² (N → ∞, the squared norm a completed sum over all
    coordinates) is a role-limit; norm convergence is stated in squared/process form,
    comparing Fₙ to the limit's rational approximants Fₛ rather than to a separately
    completed real-number object — which is exactly the ToS completeness-by-construction
    stance.

    ============ E/R/R разбор ============
      Rules (L5): (aᵢ)²≤‖a‖² ⟹ L²-Коши ⟹ покоординатная Коши; f∞(i)=Коши-вещественное
                  (Fₙ(i))ₙ; «‖Fₙ−f∞‖₂→0» ≡ условие Коши (стадия-s от f∞ есть Fₛ).
      Roles (L4): координата = роль-процесс (вещественное по построению); f∞ = роль-
                  предел (хвост как вектор-вещественных); сходимость = роль-Коши.
      Elements  : рациональные F n i, конечные суммы Σ_{i<N}, индекс стадии s (L1+P4).
    ДИАГНОСТИКА: фиксированное конечное N — полнота-по-построению процессна (coord²≤norm²
    + покоординатная Коши); бесконечномерный ℓ² (N→∞, Σ по всем координатам) и предел
    как завершённый вещественный объект — роль-предел, P4-граница (строим, не выбираем).

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_zero, q_sum_ext *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Engine: a single term is bounded by the sum of nonnegative terms,     *)
(*  hence one squared coordinate is bounded by the squared norm.          *)
(* ===================================================================== *)

Lemma q_sum_term_le : forall (g : nat -> Q) (N : nat),
  (forall j, 0 <= g j) -> forall i, (i < N)%nat -> g i <= q_sum g N.
Proof.
  intros g N Hnn. induction N as [|k IH]; intros i Hi.
  - lia.
  - cbn [q_sum].
    destruct (Nat.eqb i k) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      assert (Hs : 0 <= q_sum g k) by (apply q_sum_nonneg; exact Hnn).
      lra.
    + apply Nat.eqb_neq in E.
      assert (Hgk : 0 <= g k) by (apply Hnn).
      pose proof (IH i ltac:(lia)) as Hle.
      lra.
Qed.

(** One squared coordinate ≤ squared norm: (aᵢ)² ≤ Σ_{j<N} aⱼ². *)
Lemma coord_sq_le_normsq : forall (a : nat -> Q) (N i : nat),
  (i < N)%nat -> a i * a i <= seq_inner a a N.
Proof.
  intros a N i Hi. unfold seq_inner.
  exact (q_sum_term_le (fun j => a j * a j) N (fun j => q_sq_nonneg (a j)) i Hi).
Qed.

(* ===================================================================== *)
(*  L²-Cauchy (squared norm, fixed truncation N) and the constructed      *)
(*  coordinatewise limit.                                                  *)
(* ===================================================================== *)

(** A sequence of vectors F (F n = the n-th vector, F n i its i-th coordinate)
    is L²-Cauchy at truncation N if the squared norm of the difference is
    eventually below any ε. *)
Definition L2CauchySq (F : nat -> nat -> Q) (N : nat) : Prop :=
  forall eps, eps > 0 ->
  exists M, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    seq_inner (fun i => F m i - F n i) (fun i => F m i - F n i) N <= eps.

(** L²-Cauchy ⟹ each coordinate sequence is Cauchy in ℚ (so its limit real
    EXISTS by construction). *)
Lemma l2cauchy_coord_cauchy : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N ->
  forall i, (i < N)%nat ->
  forall eps, eps > 0 ->
  exists M, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    (F m i - F n i) * (F m i - F n i) <= eps.
Proof.
  intros F N HC i Hi eps Heps.
  destruct (HC eps Heps) as [M HM].
  exists M. intros m n Hm Hn.
  apply Qle_trans with
    (seq_inner (fun j => F m j - F n j) (fun j => F m j - F n j) N).
  - apply (coord_sq_le_normsq (fun j => F m j - F n j) N i Hi).
  - apply HM; assumption.
Qed.

(** The CONSTRUCTED limit: coordinate i is the rational sequence s ↦ F s i, read
    as a RealProcess (nat → Q). No choice — the limit is the sequence itself. *)
Definition l2_limit (F : nat -> nat -> Q) : nat -> (nat -> Q) :=
  fun i s => F s i.

(** Each coordinate of the constructed limit is a Cauchy real. *)
Lemma l2_limit_is_cauchy_real : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N ->
  forall i, (i < N)%nat ->
  forall eps, eps > 0 ->
  exists M, forall m n, (M <= m)%nat -> (M <= n)%nat ->
    (l2_limit F i m - l2_limit F i n) * (l2_limit F i m - l2_limit F i n) <= eps.
Proof.
  intros F N HC i Hi. unfold l2_limit.
  apply (l2cauchy_coord_cauchy F N HC i Hi).
Qed.

(* ===================================================================== *)
(*  Riesz–Fischer by construction: the L²-Cauchy sequence converges to the *)
(*  constructed limit — and this convergence IS the Cauchy condition.      *)
(* ===================================================================== *)

(** ‖Fₙ − f∞‖₂² ≤ ε for n, s ≥ M, where the stage-s rational approximant of the
    constructed limit f∞ is Fₛ. Completeness holds by construction. *)
Theorem l2_riesz_fischer : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N ->
  forall eps, eps > 0 ->
  exists M, forall n s, (M <= n)%nat -> (M <= s)%nat ->
    seq_inner (fun i => F n i - l2_limit F i s)
              (fun i => F n i - l2_limit F i s) N <= eps.
Proof.
  intros F N HC eps Heps.
  destruct (HC eps Heps) as [M HM].
  exists M. intros n s Hn Hs.
  unfold l2_limit.
  apply HM; assumption.
Qed.

(* Concrete witness that L2CauchySq is satisfiable: a constant sequence has zero
   difference, hence is L²-Cauchy. *)
Example const_l2cauchy : forall (c : nat -> Q) (N : nat),
  L2CauchySq (fun _ => c) N.
Proof.
  intros c N. red. intros eps Heps. exists O. intros m n _ _. cbn beta.
  assert (Hz : seq_inner (fun i => c i - c i) (fun i => c i - c i) N == 0).
  { unfold seq_inner. transitivity (q_sum (fun _ : nat => 0) N).
    - apply q_sum_ext. intro i. ring.
    - apply q_sum_zero. }
  rewrite Hz. lra.
Qed.

Print Assumptions l2cauchy_coord_cauchy.
Print Assumptions l2_riesz_fischer.
