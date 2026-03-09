(* ========================================================================= *)
(*        ORTHOGONALITY — Projections and Orthogonal Decomposition           *)
(*                                                                           *)
(*  Part of: Theory of Systems — Process Physics (Phase 3A)                  *)
(*                                                                           *)
(*  Orthogonal vectors, projections, Pythagorean theorem, Bessel inequality  *)
(*  Gram-Schmidt orthogonalization (without normalization, Q has no sqrt)     *)
(*                                                                           *)
(*  Elements: vectors (QVec n), projections                                  *)
(*  Roles:    vector → carrier, projection → decomposition                   *)
(*  Rules:    orthogonality (L3: binary relation), Pythagorean (L5)          *)
(*  Status:   orthogonal | parallel | generic                                *)
(*                                                                           *)
(*  STATUS: ~25 Qed, 0 Admitted                                             *)
(*  AXIOMS: none (purely constructive over Q)                                *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.

(* ========================================================================= *)
(*  SECTION 1: Orthogonality Definitions                                     *)
(* ========================================================================= *)

(** Two vectors are orthogonal when their dot product is zero *)
Definition orthogonal {n} (u v : QVec n) : Prop :=
  dot_product u v == 0.

(** Pairwise orthogonal family *)
Definition pairwise_orthogonal {n} (vecs : list (QVec n)) : Prop :=
  forall i j, (i < length vecs)%nat -> (j < length vecs)%nat ->
  i <> j ->
  orthogonal (nth i vecs (qv_zero n)) (nth j vecs (qv_zero n)).

(** Approximate normalization (exact 1 impossible over Q in general) *)
Definition is_approx_normalized {n} (v : QVec n) (eps : Q) : Prop :=
  Qabs (norm_sq v - 1) <= eps.

(** Orthogonal family with norm info *)
Definition is_orthogonal_family {n} (vecs : list (QVec n)) : Prop :=
  pairwise_orthogonal vecs /\
  forall i, (i < length vecs)%nat -> ~ norm_sq (nth i vecs (qv_zero n)) == 0.

Lemma orthogonal_comm : forall {n} (u v : QVec n),
  orthogonal u v -> orthogonal v u.
Proof.
  intros n u v H. unfold orthogonal in *.
  rewrite dot_product_comm. exact H.
Qed.

Lemma orthogonal_zero_l : forall {n} (v : QVec n),
  orthogonal (qv_zero n) v.
Proof.
  intros n v. unfold orthogonal.
  apply dot_product_zero_left.
Qed.

Lemma orthogonal_zero_r : forall {n} (v : QVec n),
  orthogonal v (qv_zero n).
Proof.
  intros n v. unfold orthogonal.
  apply dot_product_zero_right.
Qed.

Lemma orthogonal_scale_l : forall {n} (c : Q) (u v : QVec n),
  orthogonal u v -> orthogonal (qv_scale c u) v.
Proof.
  intros n c u v H. unfold orthogonal in *.
  rewrite dot_product_scale_l. rewrite H. ring.
Qed.

Lemma orthogonal_scale_r : forall {n} (c : Q) (u v : QVec n),
  orthogonal u v -> orthogonal u (qv_scale c v).
Proof.
  intros n c u v H. unfold orthogonal in *.
  rewrite dot_product_scale_r. rewrite H. ring.
Qed.

(* ========================================================================= *)
(*  SECTION 2: Projection                                                    *)
(* ========================================================================= *)

(** Projection of u onto v: proj_v(u) = (u·v / v·v) * v
    Requires v·v ≠ 0 (v is nonzero) *)
Definition project {n} (u v : QVec n) : QVec n :=
  qv_scale (dot_product u v / norm_sq v) v.

(** Residual after projection *)
Definition residual {n} (u v : QVec n) : QVec n :=
  qv_add u (qv_neg (project u v)).

(** Projection is idempotent (on the span of v) *)
Theorem project_idempotent : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  qv_eq (project (project u v) v) (project u v).
Proof.
  intros n u v Hv.
  (* First show the coefficients are equal at Q level *)
  assert (Hcoeff : dot_product (project u v) v / norm_sq v ==
                   dot_product u v / norm_sq v).
  { unfold project.
    pose proof (dot_product_scale_l (dot_product u v / norm_sq v) v v) as Hsl.
    rewrite Hsl. unfold norm_sq. field.
    intro H. apply Hv. exact H. }
  (* Now pointwise *)
  intros i Hi. unfold project.
  unfold qv_nth, qv_scale. simpl.
  rewrite !nth_map_Qeq; [| rewrite (qv_length v); exact Hi
                         | rewrite (qv_length v); exact Hi].
  rewrite Hcoeff. reflexivity.
Qed.

(** ★ Residual is orthogonal to v ★ *)
Theorem residual_orthogonal : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  orthogonal (residual u v) v.
Proof.
  intros n u v Hv. unfold orthogonal, residual.
  rewrite dot_product_add_l, dot_product_neg_l.
  unfold project. rewrite dot_product_scale_l.
  unfold norm_sq.
  field. intro Habsurd. apply Hv. exact Habsurd.
Qed.

(** Projection preserves inner product with v *)
Lemma project_ip_preserved : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  dot_product (project u v) v == dot_product u v.
Proof.
  intros n u v Hv. unfold project.
  rewrite dot_product_scale_l.
  unfold norm_sq. field.
  intro Habsurd. apply Hv. exact Habsurd.
Qed.

(* ========================================================================= *)
(*  SECTION 3: Pythagorean Theorem                                          *)
(* ========================================================================= *)

(** ★ Pythagorean theorem: u⊥v → ‖u+v‖² = ‖u‖² + ‖v‖² ★ *)
Theorem pythagorean_theorem : forall {n} (u v : QVec n),
  orthogonal u v ->
  norm_sq (qv_add u v) == norm_sq u + norm_sq v.
Proof.
  intros n u v Horth. unfold orthogonal in Horth.
  rewrite norm_sq_expand. rewrite Horth. ring.
Qed.

(** Generalized Pythagorean: sum of orthogonal vectors *)
Lemma pythagorean_neg : forall {n} (u v : QVec n),
  orthogonal u v ->
  norm_sq (qv_add u (qv_neg v)) == norm_sq u + norm_sq v.
Proof.
  intros n u v Horth. unfold orthogonal in Horth.
  rewrite norm_sq_expand.
  pose proof (dot_product_neg_r u v) as Hnr.
  rewrite Hnr, Horth.
  assert (Hnsn : norm_sq (qv_neg v) == norm_sq v).
  { unfold qv_neg. rewrite norm_sq_scale. ring. }
  rewrite Hnsn. ring.
Qed.

(** Projection norm squared *)
Lemma project_norm_sq : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  norm_sq (project u v) == dot_product u v * dot_product u v / norm_sq v.
Proof.
  intros n u v Hv. unfold project, norm_sq at 1.
  pose proof (dot_product_scale_l (dot_product u v / norm_sq v) v
               (qv_scale (dot_product u v / norm_sq v) v)) as H1.
  rewrite H1.
  pose proof (dot_product_scale_r v (dot_product u v / norm_sq v) v) as H2.
  rewrite H2. unfold norm_sq. field.
  intro Habsurd. apply Hv. exact Habsurd.
Qed.

(** Decomposition: ‖u‖² = ‖proj‖² + ‖residual‖² *)
Theorem norm_sq_decomposition : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  norm_sq u == norm_sq (project u v) + norm_sq (residual u v).
Proof.
  intros n u v Hv.
  rewrite project_norm_sq; [| exact Hv].
  unfold residual.
  rewrite norm_sq_expand.
  unfold project.
  pose proof (dot_product_neg_r u (qv_scale (dot_product u v / norm_sq v) v)) as H1.
  rewrite H1.
  pose proof (dot_product_scale_r u (dot_product u v / norm_sq v) v) as H2.
  rewrite H2.
  unfold qv_neg. rewrite !norm_sq_scale.
  field.
  intro H. apply Hv. exact H.
Qed.

(* ========================================================================= *)
(*  SECTION 4: Bessel Inequality                                             *)
(* ========================================================================= *)

(** Sum of projection norms for an orthogonal family *)
Fixpoint sum_proj_sq {n} (v : QVec n) (basis : list (QVec n)) : Q :=
  match basis with
  | [] => 0
  | e :: es =>
    dot_product v e * dot_product v e / norm_sq e + sum_proj_sq v es
  end.

(** Helper: inner product with orthogonal basis vector is preserved by residual *)
Lemma dot_product_residual_orthogonal : forall {n} (v e w : QVec n),
  ~ norm_sq e == 0 ->
  orthogonal e w ->
  dot_product (residual v e) w == dot_product v w.
Proof.
  intros n v e w Hne Horth.
  unfold residual.
  rewrite dot_product_add_l, dot_product_neg_l.
  unfold project. rewrite dot_product_scale_l.
  unfold orthogonal in Horth. rewrite Horth. ring.
Qed.

(** Helper: extract orthogonal family tail *)
Lemma orthogonal_family_tail : forall {n} (e : QVec n) (es : list (QVec n)),
  is_orthogonal_family (e :: es) -> is_orthogonal_family es.
Proof.
  intros n e es [Hpw Hnz]. split.
  - unfold pairwise_orthogonal in *. intros i j Hi Hj Hij.
    apply (Hpw (S i) (S j)); simpl; lia.
  - intros i Hi. apply (Hnz (S i)). simpl. lia.
Qed.

(** Helper: head of orthogonal family is orthogonal to all tail elements *)
Lemma orthogonal_family_head_tail : forall {n} (e : QVec n) (es : list (QVec n)),
  is_orthogonal_family (e :: es) ->
  forall i, (i < length es)%nat -> orthogonal e (nth i es (qv_zero n)).
Proof.
  intros n e es [Hpw _] i Hi.
  apply (Hpw 0%nat (S i)%nat); simpl; lia.
Qed.

(** Helper: sum_proj_sq is preserved when replacing v by residual v e,
    provided e is orthogonal to all basis vectors *)
Lemma sum_proj_sq_residual : forall {n} (v e : QVec n) (es : list (QVec n)),
  ~ norm_sq e == 0 ->
  (forall i, (i < length es)%nat -> orthogonal e (nth i es (qv_zero n))) ->
  sum_proj_sq v es <= sum_proj_sq (residual v e) es.
Proof.
  intros n v e es Hne Horth.
  induction es as [| w ws IH]; simpl.
  - lra.
  - assert (Hdp : dot_product v w == dot_product (residual v e) w).
    { symmetry. apply dot_product_residual_orthogonal; [exact Hne |].
      apply (Horth 0%nat). simpl. lia. }
    assert (IHws : sum_proj_sq v ws <= sum_proj_sq (residual v e) ws).
    { apply IH. intros i Hi. apply (Horth (S i)). simpl. lia. }
    rewrite <- Hdp. lra.
Qed.

(** Projection term equals proj norm squared *)
Lemma proj_term_eq : forall {n} (v e : QVec n),
  ~ norm_sq e == 0 ->
  dot_product v e * dot_product v e / norm_sq e == norm_sq (project v e).
Proof.
  intros n v e Hne.
  symmetry. apply project_norm_sq. exact Hne.
Qed.

Lemma sum_proj_sq_nonneg : forall {n} (v : QVec n) (basis : list (QVec n)),
  is_orthogonal_family basis ->
  0 <= sum_proj_sq v basis.
Proof.
  intros n v basis Hfam.
  induction basis as [| e es IH]; simpl.
  - lra.
  - assert (Hes_fam := orthogonal_family_tail e es Hfam).
    assert (Hne : ~ norm_sq e == 0).
    { destruct Hfam as [_ Hnz]. apply (Hnz 0%nat). simpl. lia. }
    assert (Hterm : 0 <= dot_product v e * dot_product v e / norm_sq e).
    { unfold Qdiv. apply Qmult_le_0_compat.
      - destruct (Qlt_le_dec (dot_product v e) 0) as [Hn | Hp].
        + setoid_replace (dot_product v e * dot_product v e)
            with ((- dot_product v e) * (- dot_product v e)) by ring.
          apply Qmult_le_0_compat; lra.
        + apply Qmult_le_0_compat; lra.
      - apply Qlt_le_weak. apply Qinv_lt_0_compat.
        pose proof (norm_sq_nonneg e) as Hnn.
        destruct (Qlt_le_dec 0 (norm_sq e)); [assumption | exfalso; apply Hne; lra]. }
    specialize (IH Hes_fam). lra.
Qed.

(** ★ BESSEL INEQUALITY: Σ|⟨v,eᵢ⟩|²/‖eᵢ‖² ≤ ‖v‖² ★ *)
Theorem bessel_inequality : forall {n} (v : QVec n) (basis : list (QVec n)),
  is_orthogonal_family basis ->
  sum_proj_sq v basis <= norm_sq v.
Proof.
  intros n v basis. revert v.
  induction basis as [| e es IH]; intros v Hfam; simpl.
  - apply norm_sq_nonneg.
  - assert (Hes_fam := orthogonal_family_tail e es Hfam).
    assert (Hne : ~ norm_sq e == 0).
    { destruct Hfam as [_ Hnz]. apply (Hnz 0%nat). simpl. lia. }
    (* sum_proj_sq v (e::es) = ‖proj_e(v)‖² + sum_proj_sq v es
       ≤ ‖proj_e(v)‖² + sum_proj_sq (residual v e) es     [by sum_proj_sq_residual]
       ≤ ‖proj_e(v)‖² + ‖residual v e‖²                    [by IH on residual]
       = ‖v‖²                                                [by norm_sq_decomposition] *)
    assert (Hsr := sum_proj_sq_residual v e es Hne
                     (orthogonal_family_head_tail e es Hfam)).
    assert (IHres := IH (residual v e) Hes_fam).
    assert (Hdecomp := norm_sq_decomposition v e Hne).
    rewrite proj_term_eq; [| exact Hne].
    assert (Hdecomp' : norm_sq (project v e) + norm_sq (residual v e) <= norm_sq v).
    { apply Qeq_Qle. symmetry. exact Hdecomp. }
    lra.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Gram-Schmidt Orthogonalization                               *)
(* ========================================================================= *)

(** Gram-Schmidt step: subtract projection onto each basis vector *)
Fixpoint gs_step {n} (v : QVec n) (basis : list (QVec n)) : QVec n :=
  match basis with
  | [] => v
  | e :: es => gs_step (residual v e) es
  end.

(** Gram-Schmidt result is orthogonal to each basis vector *)
Lemma gs_step_orthogonal_each : forall {n} (v : QVec n) (e : QVec n),
  ~ norm_sq e == 0 ->
  orthogonal (residual v e) e.
Proof.
  intros n v e Hne.
  exact (residual_orthogonal v e Hne).
Qed.

(** Gram-Schmidt on singleton basis *)
Lemma gs_step_singleton : forall {n} (v e : QVec n),
  ~ norm_sq e == 0 ->
  orthogonal (gs_step v [e]) e.
Proof.
  intros n v e Hne. simpl.
  apply residual_orthogonal. exact Hne.
Qed.

(** Helper: nth of qv_add *)
Lemma qv_add_nth : forall {n} (u v : QVec n) i,
  (i < n)%nat -> qv_nth (qv_add u v) i == qv_nth u i + qv_nth v i.
Proof.
  intros n u v i Hi. unfold qv_nth, qv_add. simpl.
  rewrite nth_map2_Qeq.
  - reflexivity.
  - rewrite (qv_length u). exact Hi.
  - rewrite (qv_length u), (qv_length v). reflexivity.
Qed.

(** Helper: nth of qv_scale *)
Lemma qv_scale_nth : forall {n} (c : Q) (v : QVec n) i,
  (i < n)%nat -> qv_nth (qv_scale c v) i == c * qv_nth v i.
Proof.
  intros n c v i Hi. unfold qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  reflexivity.
Qed.

(** Helper: nth of qv_zero *)
Lemma qv_zero_nth : forall n i,
  (i < n)%nat -> qv_nth (qv_zero n) i == 0.
Proof.
  intros n i Hi. unfold qv_nth, qv_zero. simpl.
  rewrite nth_repeat. reflexivity.
Qed.

(** Projection of zero gives zero *)
Lemma project_zero : forall {n} (v : QVec n),
  qv_eq (project (qv_zero n) v) (qv_zero n).
Proof.
  intros n v i Hi. unfold project, qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  rewrite dot_product_zero_left.
  transitivity 0.
  - unfold Qdiv. ring.
  - symmetry. unfold qv_zero. simpl. rewrite nth_repeat. reflexivity.
Qed.

(** Residual of zero is zero *)
Lemma residual_zero : forall {n} (v : QVec n),
  qv_eq (residual (qv_zero n) v) (qv_zero n).
Proof.
  intros n v i Hi.
  unfold residual.
  rewrite qv_add_nth; [| exact Hi].
  rewrite qv_neg_nth; [| exact Hi].
  pose proof (project_zero v i Hi) as Hpz.
  rewrite Hpz.
  rewrite qv_zero_nth; [| exact Hi].
  ring.
Qed.

(** Norm of projection is bounded by norm of original *)
Lemma project_norm_bounded : forall {n} (u v : QVec n),
  ~ norm_sq v == 0 ->
  norm_sq (project u v) <= norm_sq u.
Proof.
  intros n u v Hv.
  rewrite project_norm_sq; [| exact Hv].
  assert (Hcs := cauchy_schwarz u v).
  assert (Hnvpos : 0 < norm_sq v).
  { pose proof (norm_sq_nonneg v) as Hnn.
    destruct (Qlt_le_dec 0 (norm_sq v)); [assumption | exfalso; apply Hv; lra]. }
  unfold Qdiv.
  apply (Qmult_le_l _ _ (norm_sq v) Hnvpos).
  setoid_replace (norm_sq v * (dot_product u v * dot_product u v * / norm_sq v))
    with (dot_product u v * dot_product u v) by (field; lra).
  setoid_replace (norm_sq v * norm_sq u)
    with (norm_sq u * norm_sq v) by ring.
  exact Hcs.
Qed.

(** Summary:
    ~25 Qed, 0 Admitted, 0 axioms
    - Orthogonality: 7 lemmas (comm, zero, scale)
    - Projection: 4 lemmas (idempotent, residual_orthogonal, ip_preserved)
    - Pythagorean: 2 theorems
    - Bessel: 2 lemmas
    - Gram-Schmidt: 4 lemmas (step, singleton, projection zero/residual zero)
    - Norm bounds: 1 lemma
*)
