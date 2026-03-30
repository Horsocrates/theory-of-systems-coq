(** * L2Space.v — L² Inner Product Space for Finite Q-Vectors

    Theory of Systems — Analysis / Spectral Theory Step 3

    L² inner product and norm for finite-dimensional vectors over Q,
    with linearity, symmetry, and Cauchy-Schwarz verified concretely.

    Elements: vectors (list Q), inner product, norm squared, pointwise ops
    Roles:    l2_inner -> bilinear form, l2_norm_sq -> quadratic form,
              vec_scale -> scalar action, vec_add/vec_sub -> vector space ops
    Rules:    bilinearity of inner product (L5: verified by structural induction)
    Status:   verified | concrete_checked

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: VECTOR OPERATIONS                                              *)
(* ========================================================================= *)

Fixpoint l2_inner (u v : list Q) : Q :=
  match u, v with
  | [], _ | _, [] => 0
  | a :: us, b :: vs => a * b + l2_inner us vs
  end.

Definition l2_norm_sq (u : list Q) : Q := l2_inner u u.

Fixpoint vec_add (u v : list Q) : list Q :=
  match u, v with
  | [], _ | _, [] => []
  | a :: us, b :: vs => (a + b) :: vec_add us vs
  end.

Fixpoint vec_scale (c : Q) (u : list Q) : list Q :=
  match u with
  | [] => []
  | x :: xs => (c * x) :: vec_scale c xs
  end.

Fixpoint vec_sub (u v : list Q) : list Q :=
  match u, v with
  | [], _ | _, [] => []
  | a :: us, b :: vs => (a - b) :: vec_sub us vs
  end.

(* ========================================================================= *)
(* SECTION 2: BASIC PROPERTIES                                               *)
(* ========================================================================= *)

Lemma sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q.
  destruct (Qlt_le_dec q 0).
  - assert (Hnq : 0 <= -q) by lra.
    assert (H : (-q) * (-q) == q * q) by ring.
    rewrite <- H.
    assert (H2 : 0 == 0 * (-q)) by ring. rewrite H2.
    apply Qmult_le_compat_r; lra.
  - assert (H2 : 0 == 0 * q) by ring. rewrite H2.
    apply Qmult_le_compat_r; lra.
Qed.

(* 1 *)
Lemma l2_inner_nil_l : forall v, l2_inner [] v == 0.
Proof. destruct v; reflexivity. Qed.

(* 2 *)
Lemma l2_inner_nil_r : forall u, l2_inner u [] == 0.
Proof. induction u as [| x xs IH]; simpl; lra. Qed.

(* 3 *)
Lemma l2_inner_comm : forall u v, l2_inner u v == l2_inner v u.
Proof.
  induction u as [| x xs IH]; intro v.
  - simpl. assert (H := l2_inner_nil_r v). lra.
  - destruct v as [| y ys].
    + simpl. assert (H := l2_inner_nil_r (x :: xs)). simpl in H. lra.
    + simpl. specialize (IH ys). rewrite IH. ring.
Qed.

(* 4 *)
Lemma l2_norm_sq_nonneg : forall u, 0 <= l2_norm_sq u.
Proof.
  induction u as [| x xs IH].
  - unfold l2_norm_sq. simpl. lra.
  - unfold l2_norm_sq. simpl.
    assert (Hx : 0 <= x * x) by apply sq_nonneg.
    unfold l2_norm_sq in IH. lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: LINEARITY                                                      *)
(* ========================================================================= *)

(* 5 *)
Lemma l2_inner_scale_l : forall c u v,
  l2_inner (vec_scale c u) v == c * l2_inner u v.
Proof.
  intros c u. induction u as [| x xs IH]; intro v.
  - simpl. destruct v; simpl; ring.
  - destruct v as [| y ys].
    + simpl. ring.
    + simpl. rewrite IH. ring.
Qed.

(* 6 *)
Lemma l2_inner_scale_r : forall c u v,
  l2_inner u (vec_scale c v) == c * l2_inner u v.
Proof.
  intros c u v.
  rewrite l2_inner_comm.
  rewrite l2_inner_scale_l.
  rewrite l2_inner_comm. ring.
Qed.

(* 7 *)
Lemma l2_inner_add_l : forall u1 u2 v,
  length u1 = length u2 ->
  l2_inner (vec_add u1 u2) v == l2_inner u1 v + l2_inner u2 v.
Proof.
  intros u1. induction u1 as [| a us IH]; intros u2 v Hlen.
  - destruct u2; [| simpl in Hlen; discriminate].
    simpl. destruct v; simpl; lra.
  - destruct u2 as [| b bs]; [simpl in Hlen; discriminate |].
    destruct v as [| c cs].
    + simpl. lra.
    + simpl. simpl in Hlen.
      assert (Hlen' : length us = length bs) by lia.
      rewrite (IH bs cs Hlen'). ring.
Qed.

(* 8 *)
Lemma l2_inner_sub_l : forall u v w,
  length u = length v ->
  l2_inner (vec_sub u v) w == l2_inner u w - l2_inner v w.
Proof.
  intros u. induction u as [| x xs IH]; intros v w Hlen.
  - destruct v; [| simpl in Hlen; discriminate].
    simpl. destruct w; simpl; lra.
  - destruct v as [| y ys]; [simpl in Hlen; discriminate |].
    destruct w as [| z ws].
    + simpl. lra.
    + simpl. simpl in Hlen.
      assert (Hlen' : length xs = length ys) by lia.
      rewrite (IH ys ws Hlen'). ring.
Qed.

(* ========================================================================= *)
(* SECTION 4: NORM PROPERTIES                                                *)
(* ========================================================================= *)

(* 9 *)
Lemma l2_norm_sq_scale : forall c u,
  l2_norm_sq (vec_scale c u) == c * c * l2_norm_sq u.
Proof.
  intros c u. unfold l2_norm_sq.
  rewrite l2_inner_scale_l. rewrite l2_inner_scale_r. ring.
Qed.

(* 10 *)
Lemma l2_norm_sq_add : forall u v,
  length u = length v ->
  l2_norm_sq (vec_add u v) ==
    l2_norm_sq u + (2 # 1) * l2_inner u v + l2_norm_sq v.
Proof.
  unfold l2_norm_sq.
  induction u as [| a us IH]; intros v Hlen.
  - destruct v; [| simpl in Hlen; discriminate].
    simpl. lra.
  - destruct v as [| b vs]; [simpl in Hlen; discriminate |].
    simpl. simpl in Hlen.
    assert (Hlen' : length us = length vs) by lia.
    specialize (IH vs Hlen').
    rewrite IH. ring.
Qed.

(* ========================================================================= *)
(* SECTION 5: CONCRETE VERIFICATIONS                                         *)
(* ========================================================================= *)

(* 11 *)
Lemma l2_inner_orthogonal_basis : l2_inner [1;0] [0;1] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 12 *)
Lemma l2_norm_sq_345 : l2_norm_sq [3;4] == 25.
Proof. vm_compute. reflexivity. Qed.

(* 13 *)
Lemma l2_inner_symmetric_ortho : l2_inner [1;1] [1;-(1)] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 14 *)
Lemma l2_norm_sq_unit : l2_norm_sq [1;0] == 1.
Proof. vm_compute. reflexivity. Qed.

(* 15 *)
Lemma l2_norm_sq_zero : l2_norm_sq [] == 0.
Proof. vm_compute. reflexivity. Qed.

(* 16 *)
Lemma l2_inner_self_positive :
  l2_inner [2;3] [2;3] == 13.
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(* SECTION 6: CAUCHY-SCHWARZ (CONCRETE 2D)                                   *)
(* ========================================================================= *)

(* 17: Cauchy-Schwarz for concrete 2D vectors *)
Lemma l2_cauchy_schwarz_2d :
  forall a b c d : Q,
  (a * c + b * d) * (a * c + b * d) <=
  (a * a + b * b) * (c * c + d * d).
Proof.
  intros a b c d.
  (* Use identity: ‖u‖²‖v‖² - ⟨u,v⟩² = (ad - bc)² ≥ 0 *)
  assert (Hid : (a * a + b * b) * (c * c + d * d) -
                (a * c + b * d) * (a * c + b * d) ==
                (a * d - b * c) * (a * d - b * c)) by ring.
  assert (Hnn : 0 <= (a * d - b * c) * (a * d - b * c))
    by apply sq_nonneg.
  lra.
Qed.

(* 18: Cauchy-Schwarz for list vectors of equal length *)
Lemma l2_cauchy_schwarz_concrete :
  l2_inner [1;2] [3;4] * l2_inner [1;2] [3;4] <=
  l2_norm_sq [1;2] * l2_norm_sq [3;4].
Proof. vm_compute. discriminate. Qed.
