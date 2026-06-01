(** * ProcessL2BesselGeneral.v — Inner-product linearity over a finite orthonormal
      expansion, and general Bessel inequality (F-29 frontier, Part VI)

    Elements: coefficients cₖ; basis coordinates eₖ(m); finite double sums
    Roles:    ⟨h, Σcₖeₖ⟩ distributed over the expansion; swap = inner-product ∘ Σ
    Rules:    ⟨h, Σ_{k<K} cₖ eₖ⟩ = Σ_{k<K} cₖ ⟨h, eₖ⟩  (linearity over the expansion)

    The crux that unlocks general Bessel / Parseval is the LINEARITY of the inner
    product over a finite orthonormal expansion: pairing h with a finite combination
    Σ_{k<K} cₖ eₖ equals Σ_{k<K} cₖ ⟨h, eₖ⟩. On process-L² this is a double sum that
    commutes (q_sum_swap / discrete Fubini). From it, with orthonormality, follows
    Bessel's inequality Σ_{k<K} ⟨eₖ,f⟩² ≤ ‖f‖² for a general orthonormal system.

    HONEST FRONTIER: the INFINITE expansion (a full basis) is a role-limit; Parseval
    EQUALITY (completeness criterion), the full Riesz–Fischer with a constructed
    limit, and the diagonalisation of an arbitrary compact operator remain beyond.

    ============ E/R/R разбор ============
      Rules (L5): ⟨h,Σcₖeₖ⟩=Σcₖ⟨h,eₖ⟩ (через q_sum_swap); Σ⟨eₖ,f⟩²≤‖f‖² (с ON).
      Roles (L4): ⟨h,Σcₖeₖ⟩ = значение скаляра по разложению; Бессель = энергия по K
                  направлениям ≤ полной.
      Elements  : cₖ, координаты eₖ(m), конечные двойные суммы (L1+P4).
    ДИАГНОСТИКА: коммутация скаляра с КОНЕЧНЫМ разложением — процессный факт (Фубини);
    бесконечное разложение (полный базис) = роль-предел (граница).

    STATUS: 10 Qed, 0 Admitted, 0 axioms (general Bessel PROVEN)
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_swap, q_sum_scale, q_sum_ext *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)
From ToS Require Import process.ProcessL2Bessel.        (* seq_inner_residual_identity *)
From ToS Require Import process.ProcessDCT.             (* q_sum_minus *)

Open Scope Q_scope.

(** Symmetry of the inner product. *)
Lemma seq_inner_sym : forall a b N, seq_inner a b N == seq_inner b a N.
Proof.
  intros a b N. unfold seq_inner. apply q_sum_ext. intro i. ring.
Qed.

(** Congruence: the inner product respects pointwise equality of its arguments. *)
Lemma seq_inner_ext : forall a a' b b' N,
  (forall m, a m == a' m) -> (forall m, b m == b' m) ->
  seq_inner a b N == seq_inner a' b' N.
Proof.
  intros a a' b b' N Ha Hb. unfold seq_inner. apply q_sum_ext.
  intro i. rewrite (Ha i), (Hb i). reflexivity.
Qed.

(** Linearity in the second argument over a difference. *)
Lemma seq_inner_sub_r : forall h a b N,
  seq_inner h (fun m => a m - b m) N == seq_inner h a N - seq_inner h b N.
Proof.
  intros h a b N. unfold seq_inner.
  transitivity (q_sum (fun m => h m * a m - h m * b m) N).
  - apply q_sum_ext. intro m. ring.
  - symmetry. apply q_sum_minus.
Qed.

(** Residual-norm identity in inner-product form:
    ‖F − c·E‖² = ‖F‖² − 2c⟨E,F⟩ + c²‖E‖². *)
Lemma seq_inner_resid : forall F E c N,
  seq_inner (fun m => F m - c * E m) (fun m => F m - c * E m) N
  == seq_inner F F N - 2 * c * seq_inner E F N + c * c * seq_inner E E N.
Proof.
  intros F E c N. unfold seq_inner. apply seq_inner_residual_identity.
Qed.

(* ===================================================================== *)
(*  CRUX: inner product is linear over a finite orthonormal expansion.    *)
(*    ⟨h, Σ_{k<K} cₖ eₖ⟩ = Σ_{k<K} cₖ ⟨h, eₖ⟩                            *)
(* ===================================================================== *)

Lemma inner_proj_swap :
  forall (e : nat -> nat -> Q) (coef h : nat -> Q) (K N : nat),
  seq_inner h (fun m => q_sum (fun k => coef k * e k m) K) N
  == q_sum (fun k => coef k * seq_inner h (e k) N) K.
Proof.
  intros e coef h K N. unfold seq_inner.
  (* distribute h m into the inner k-sum *)
  transitivity (q_sum (fun m => q_sum (fun k => h m * (coef k * e k m)) K) N).
  { apply q_sum_ext. intro m. symmetry. apply q_sum_scale. }
  (* swap the order of summation (m ↔ k) *)
  transitivity (q_sum (fun k => q_sum (fun m => h m * (coef k * e k m)) N) K).
  { apply (q_sum_swap (fun m k => h m * (coef k * e k m)) N K). }
  (* pull coef k out of the m-sum *)
  apply q_sum_ext. intro k.
  transitivity (q_sum (fun m => coef k * (h m * e k m)) N).
  { apply q_sum_ext. intro m. ring. }
  apply q_sum_scale.
Qed.

(** Bounded extensionality for finite sums. *)
Lemma q_sum_ext_bounded : forall (g h : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> g i == h i) -> q_sum g N == q_sum h N.
Proof.
  intros g h N. induction N as [|k IH]; intro H; cbn [q_sum].
  - reflexivity.
  - rewrite (H k ltac:(lia)).
    rewrite IH; [ reflexivity | intros i Hi; apply H; lia ].
Qed.

(* ===================================================================== *)
(*  Orthonormal system: the projection residual is orthogonal to the      *)
(*  next basis vector, and general Bessel follows.                         *)
(* ===================================================================== *)

Section ON.

Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).

(** ⟨e_K, Σ_{k<K} cₖ eₖ⟩ = 0 : the K-th vector is orthogonal to the span of the
    first K. *)
Lemma proj_ortho : forall (coef : nat -> Q) (K : nat),
  seq_inner (e K) (fun m => q_sum (fun k => coef k * e k m) K) N == 0.
Proof.
  intros coef K.
  rewrite (inner_proj_swap e coef (e K) K N).
  transitivity (q_sum (fun _ : nat => 0) K).
  - apply q_sum_ext_bounded. intros k Hk.
    rewrite (Hon K k).
    assert (Hneq : Nat.eqb K k = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq. ring.
  - apply q_sum_zero.
Qed.

Variable f : nat -> Q.

(** The residual keeps the K-th coefficient: ⟨e_K, f − P_K⟩ = ⟨e_K, f⟩. *)
Lemma coef_e_resid : forall K,
  seq_inner (e K) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner (e K) f N.
Proof.
  intro K.
  rewrite (seq_inner_sub_r (e K) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_ortho (fun k => seq_inner (e k) f N) K). ring.
Qed.

(** Residual-norm identity: ‖f − P_K‖² = ‖f‖² − Σ_{k<K} ⟨eₖ,f⟩². *)
Lemma resid_norm : forall K,
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner f f N - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K.
Proof.
  induction K as [|K IH].
  - transitivity (seq_inner f f N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + cbn [q_sum]; ring.
  - transitivity
      (seq_inner (fun m => (f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                            - seq_inner (e K) f N * e K m)
                 (fun m => (f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                            - seq_inner (e K) f N * e K m) N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + rewrite (seq_inner_resid
                 (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                 (e K) (seq_inner (e K) f N) N).
      rewrite IH.
      rewrite (coef_e_resid K).
      rewrite (Hon K K), Nat.eqb_refl.
      cbn [q_sum]. ring.
Qed.

(** General Bessel inequality: Σ_{k<K} ⟨eₖ,f⟩² ≤ ‖f‖². *)
Theorem bessel_general : forall K,
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N.
Proof.
  intro K.
  pose proof (resid_norm K) as Hrn.
  assert (Hnn : 0 <= seq_inner
                       (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                       (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  { unfold seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg. }
  rewrite Hrn in Hnn. lra.
Qed.

End ON.

Print Assumptions inner_proj_swap.
Print Assumptions proj_ortho.
Print Assumptions bessel_general.
