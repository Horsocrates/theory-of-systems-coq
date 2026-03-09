(* ========================================================================= *)
(*        BORNRULE — Born Rule and Measurement Probabilities                *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                 *)
(*                                                                          *)
(*  The Born rule: the probability of measuring a state |s1⟩ in state |s2⟩  *)
(*  is |⟨s1|s2⟩|², and the expectation value of an observable A in state   *)
(*  |s⟩ is ⟨s|A|s⟩.                                                       *)
(*                                                                          *)
(*  Elements: born_prob, born_expectation, transition amplitudes            *)
(*  Roles:    probability → measurement prediction in quantum mechanics    *)
(*  Rules:    0 ≤ P ≤ 1 (from Cauchy-Schwarz), orthogonal → P = 0         *)
(*  Status:   probability | expectation | amplitude                        *)
(*                                                                          *)
(*  STATUS: 13 Qed, 0 Admitted                                             *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.

(* ========================================================================= *)
(*  SECTION 1: Born Probability                                             *)
(* ========================================================================= *)

(** Born probability: |⟨s1|s2⟩|² at step k.
    This is the probability amplitude squared for the transition s1 → s2. *)
Definition born_prob_at {dim} (s1 s2 : QState dim) (k : nat) : Q :=
  state_ip_at s1 s2 k * state_ip_at s1 s2 k.

(** Born probability is nonneg *)
Lemma born_nonneg : forall {dim} (s1 s2 : QState dim) k,
  0 <= born_prob_at s1 s2 k.
Proof.
  intros dim s1 s2 k. unfold born_prob_at.
  set (x := state_ip_at s1 s2 k).
  destruct (Qlt_le_dec 0 x).
  - apply Qmult_le_0_compat; lra.
  - setoid_replace (x * x) with ((-x) * (-x)) by ring.
    apply Qmult_le_0_compat; lra.
Qed.

(** Born probability respects Cauchy-Schwarz bound:
    |⟨s1|s2⟩|² ≤ ⟨s1|s1⟩ · ⟨s2|s2⟩ *)
Theorem born_cauchy_schwarz : forall {dim} (s1 s2 : QState dim) k,
  born_prob_at s1 s2 k <= state_ip_at s1 s1 k * state_ip_at s2 s2 k.
Proof.
  intros dim s1 s2 k. unfold born_prob_at.
  apply state_cauchy_schwarz.
Qed.

(** Born probability is symmetric: |⟨s1|s2⟩|² = |⟨s2|s1⟩|² *)
Lemma born_symmetric : forall {dim} (s1 s2 : QState dim) k,
  born_prob_at s1 s2 k == born_prob_at s2 s1 k.
Proof.
  intros dim s1 s2 k. unfold born_prob_at.
  assert (Hcomm := state_ip_comm s1 s2 k).
  rewrite Hcomm. reflexivity.
Qed.

(** Self-transition probability: |⟨s|s⟩|² = ⟨s|s⟩² ≥ 0 *)
Lemma born_self_nonneg : forall {dim} (s : QState dim) k,
  0 <= born_prob_at s s k.
Proof.
  intros dim s k. apply born_nonneg.
Qed.

(** Orthogonal states have zero transition probability *)
Lemma born_orthogonal_at : forall dim i j k,
  (i < dim)%nat -> (j < dim)%nat -> i <> j ->
  born_prob_at (basis_state dim i) (basis_state dim j) k == 0.
Proof.
  intros dim i j k Hi Hj Hij. unfold born_prob_at.
  rewrite basis_orthogonal_direct; [ring | exact Hi | exact Hj | exact Hij].
Qed.

(** Basis self-transition probability is 1 *)
Lemma born_self_basis : forall dim j k,
  (j < dim)%nat ->
  born_prob_at (basis_state dim j) (basis_state dim j) k == 1.
Proof.
  intros dim j k Hj. unfold born_prob_at.
  rewrite basis_self_ip; [ring | exact Hj].
Qed.

(** Born probability process is Cauchy *)
Theorem born_prob_cauchy : forall {dim} (s1 s2 : QState dim),
  is_cauchy (born_prob_at s1 s2).
Proof.
  intros dim s1 s2.
  unfold born_prob_at.
  apply cauchy_mul_is_cauchy.
  - exact (state_ip_cauchy s1 s2).
  - exact (state_ip_cauchy s1 s2).
Qed.

(** Born probability as CauchySeq *)
Definition born_prob {dim} (s1 s2 : QState dim) : CauchySeq :=
  mkCauchy (born_prob_at s1 s2) (born_prob_cauchy s1 s2).

(* ========================================================================= *)
(*  SECTION 2: Expectation Value                                            *)
(* ========================================================================= *)

(** Expectation value of observable A in state s at step k:
    ⟨s|A|s⟩ = dot_product(s(k), A(k)·s(k)) *)
Definition born_expectation_at {dim} (A : QObservable dim) (s : QState dim) (k : nat) : Q :=
  dot_product (state_at s k) (obs_action_at A s k).

(** Helper: identity action gives the same vector *)
Lemma id_mat_vec_mul : forall dim (v : QVec dim),
  qv_eq (mat_vec_mul (id_mat dim) v) v.
Proof.
  intros dim v i Hi.
  rewrite mat_vec_mul_nth; [| exact Hi].
  unfold mat_row, id_mat. simpl.
  rewrite (nth_map_general (fun i => basis_vec dim i) (seq 0 dim) 0%nat (qv_zero dim));
    [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  apply dot_basis_extracts. exact Hi.
Qed.

(** Dot product respects pointwise Qeq in second argument *)
Lemma dot_product_qv_eq_r : forall {n} (u v w : QVec n),
  qv_eq v w -> dot_product u v == dot_product u w.
Proof.
  intros n u v w Hvw. unfold dot_product.
  apply fold_left_Qplus_Qeq.
  - rewrite !map2_length; [reflexivity |
      rewrite (qv_length u), (qv_length w); reflexivity |
      rewrite (qv_length u), (qv_length v); reflexivity].
  - intros i. destruct (Nat.lt_ge_cases i n) as [Hi | Hi].
    + assert (Hiu : (i < length (qv_data u))%nat)
        by (rewrite (qv_length u); exact Hi).
      assert (Hiv : (i < length (qv_data v))%nat)
        by (rewrite (qv_length v); exact Hi).
      assert (Hlen_uv : length (qv_data u) = length (qv_data v))
        by (rewrite (qv_length u), (qv_length v); reflexivity).
      assert (Hlen_uw : length (qv_data u) = length (qv_data w))
        by (rewrite (qv_length u), (qv_length w); reflexivity).
      rewrite nth_map2_Qeq; [| exact Hiu | exact Hlen_uv].
      rewrite nth_map2_Qeq; [| exact Hiu | exact Hlen_uw].
      apply Qmult_comp; [reflexivity |].
      unfold qv_nth in Hvw. apply Hvw. exact Hi.
    + (* i >= n: both nths are out of bounds, return defaults 0 *)
      assert (Hiuv : (i >= length (map2 Qmult (qv_data u) (qv_data v)))%nat).
      { rewrite map2_length; [rewrite (qv_length u); lia |
          rewrite (qv_length u), (qv_length v); reflexivity]. }
      assert (Hiuw : (i >= length (map2 Qmult (qv_data u) (qv_data w)))%nat).
      { rewrite map2_length; [rewrite (qv_length u); lia |
          rewrite (qv_length u), (qv_length w); reflexivity]. }
      rewrite !nth_overflow; [reflexivity | lia | lia].
Qed.

(** Expectation value of identity observable is the norm squared *)
Lemma expectation_identity : forall dim (s : QState dim) k,
  born_expectation_at (id_observable dim) s k == state_ip_at s s k.
Proof.
  intros dim s k. unfold born_expectation_at, state_ip_at.
  apply dot_product_qv_eq_r.
  unfold obs_action_at, obs_at. simpl.
  apply id_mat_vec_mul.
Qed.

(** Expectation value is nonneg for identity (= norm squared) *)
Lemma expectation_id_nonneg : forall dim (s : QState dim) k,
  0 <= born_expectation_at (id_observable dim) s k.
Proof.
  intros dim s k. rewrite expectation_identity.
  apply state_ip_nonneg.
Qed.

(** Expectation value of diagonal observable on basis state *)
Lemma expectation_diag_basis : forall {dim} (eigenvals : QVec dim) j k,
  (j < dim)%nat ->
  born_expectation_at (diag_observable eigenvals) (basis_state dim j) k ==
  qv_nth eigenvals j.
Proof.
  intros dim eigenvals j k Hj.
  unfold born_expectation_at.
  (* dot_product (state_at (basis_state dim j) k)
     (obs_action_at (diag_observable eigenvals) (basis_state dim j) k) == ... *)
  (* Use: diag action on basis = eigenvalue * basis *)
  apply Qeq_trans with
    (dot_product (state_at (basis_state dim j) k)
      (qv_scale (qv_nth eigenvals j) (state_at (basis_state dim j) k))).
  - apply dot_product_qv_eq_r.
    intros i Hi.
    (* LHS: obs_action_at component *)
    rewrite (diag_action_basis eigenvals j k i Hj Hi).
    (* RHS: qv_scale component *)
    rewrite qv_scale_nth; [| exact Hi].
    rewrite basis_state_at.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    + subst i. rewrite basis_vec_same; [ring | exact Hj].
    + rewrite basis_vec_diff; [ring | exact Hi | exact Hneq].
  - rewrite basis_state_at.
    rewrite dot_product_scale_r.
    change (dot_product (basis_vec dim j) (basis_vec dim j)) with
      (state_ip_at (basis_state dim j) (basis_state dim j) k).
    rewrite (basis_self_ip dim j k Hj). ring.
Qed.

(** Expectation value process is Cauchy *)
Theorem born_expectation_cauchy : forall {dim} (A : QObservable dim) (s : QState dim),
  is_cauchy (born_expectation_at A s).
Proof.
  intros dim A s. unfold born_expectation_at.
  unfold obs_action_at.
  apply process_ip_cauchy.
  - intros i Hi. exact (qs_cauchy dim s i Hi).
  - intros i Hi.
    (* Goal: is_cauchy (fun k => qv_nth (mat_vec_mul (obs_at A k) (state_at s k)) i) *)
    (* Each component == dot_product (mat_row (obs_at A k) i) (state_at s k) *)
    (* which is process_ip (fun k => mat_row (obs_at A k) i) (fun k => state_at s k) *)
    set (pip := process_ip (fun k => mat_row (obs_at A k) i)
                            (fun k => state_at s k)).
    assert (Hcauchy : is_cauchy pip).
    { unfold pip. apply process_ip_cauchy.
      - intros j Hj. exact (obs_cauchy dim A i j Hi Hj).
      - intros j Hj. exact (qs_cauchy dim s j Hj). }
    (* Transfer via pointwise Qeq: mat_vec_mul_nth *)
    intros eps Heps.
    destruct (Hcauchy eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    assert (Heq_m : qv_nth (mat_vec_mul (obs_at A m) (state_at s m)) i ==
                    dot_product (mat_row (obs_at A m) i) (state_at s m))
      by (apply mat_vec_mul_nth; exact Hi).
    assert (Heq_n : qv_nth (mat_vec_mul (obs_at A n) (state_at s n)) i ==
                    dot_product (mat_row (obs_at A n) i) (state_at s n))
      by (apply mat_vec_mul_nth; exact Hi).
    assert (Hdiff : qv_nth (mat_vec_mul (obs_at A m) (state_at s m)) i -
                    qv_nth (mat_vec_mul (obs_at A n) (state_at s n)) i ==
                    pip m - pip n).
    { unfold pip, process_ip. apply Qplus_comp.
      - exact Heq_m.
      - apply Qopp_comp. exact Heq_n. }
    assert (Habs := Qabs_wd _ _ Hdiff).
    apply Qle_lt_trans with (Qabs (pip m - pip n)).
    + apply Qeq_Qle. exact Habs.
    + exact (HN m n Hm Hn).
Qed.

(** Expectation value as CauchySeq *)
Definition born_expectation {dim} (A : QObservable dim) (s : QState dim) : CauchySeq :=
  mkCauchy (born_expectation_at A s) (born_expectation_cauchy A s).

(** Summary:
    BornRule: Born probability and expectation values.
    - Born probability: born_prob_at, born_nonneg, born_cauchy_schwarz,
      born_symmetric, born_self_nonneg
    - Basis properties: born_orthogonal_at, born_self_basis
    - Born process: born_prob_cauchy, born_prob (CauchySeq)
    - Expectation: born_expectation_at, expectation_identity,
      expectation_id_nonneg, expectation_diag_basis
    - Helpers: id_mat_vec_mul, dot_product_qv_eq_r
    - Expectation process: born_expectation_cauchy, born_expectation (CauchySeq)
*)
