(** * VectorSpace.v -- Abstract Vector Spaces over Q
    Theory of Systems -- Verified Standard Library (Batch 5)
    Elements: vectors (abstract carrier)
    Roles:    basis -> Generator, zero -> Identity, general -> Member
    Rules:    VS axioms (constitution = 8 axioms)
    Status:   in_subspace | in_kernel | in_image | zero
    Connection: LinearAlgebra.v (QVec is concrete VS instance)
    Connection: GroupTheory.v (additive group structure)
    STATUS: 27 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026 *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import LinearAlgebra.

Record VectorSpace := mkVectorSpace {
  vs_carrier : Type; vs_eq : vs_carrier -> vs_carrier -> Prop;
  vs_add : vs_carrier -> vs_carrier -> vs_carrier; vs_zero : vs_carrier;
  vs_neg : vs_carrier -> vs_carrier; vs_scale : Q -> vs_carrier -> vs_carrier;
  vs_eq_refl : forall x, vs_eq x x;
  vs_eq_sym : forall x y, vs_eq x y -> vs_eq y x;
  vs_eq_trans : forall x y z, vs_eq x y -> vs_eq y z -> vs_eq x z;
  vs_add_compat : forall x x2 y y2,
    vs_eq x x2 -> vs_eq y y2 -> vs_eq (vs_add x y) (vs_add x2 y2);
  vs_neg_compat : forall x x2,
    vs_eq x x2 -> vs_eq (vs_neg x) (vs_neg x2);
  vs_scale_compat : forall c x x2,
    vs_eq x x2 -> vs_eq (vs_scale c x) (vs_scale c x2);
  vs_add_comm : forall u v, vs_eq (vs_add u v) (vs_add v u);
  vs_add_assoc : forall u v w,
    vs_eq (vs_add (vs_add u v) w) (vs_add u (vs_add v w));
  vs_add_zero_r : forall v, vs_eq (vs_add v vs_zero) v;
  vs_add_neg_r : forall v, vs_eq (vs_add v (vs_neg v)) vs_zero;
  vs_scale_assoc : forall a b v,
    vs_eq (vs_scale a (vs_scale b v)) (vs_scale (a * b) v);
  vs_scale_one : forall v, vs_eq (vs_scale 1 v) v;
  vs_scale_distrib_vec : forall a u v,
    vs_eq (vs_scale a (vs_add u v))
          (vs_add (vs_scale a u) (vs_scale a v));
  vs_scale_distrib_scalar : forall a b v,
    vs_eq (vs_scale (a + b) v)
          (vs_add (vs_scale a v) (vs_scale b v));
}.

Definition is_subspace (V : VectorSpace) (W : vs_carrier V -> Prop) : Prop :=
  W (vs_zero V) /\
  (forall u v, W u -> W v -> W (vs_add V u v)) /\
  (forall a v, W v -> W (vs_scale V a v)).

Definition is_linear (V W : VectorSpace) (T : vs_carrier V -> vs_carrier W) : Prop :=
  (forall u u2, vs_eq V u u2 -> vs_eq W (T u) (T u2)) /\
  (forall u v, vs_eq W (T (vs_add V u v)) (vs_add W (T u) (T v))) /\
  (forall a v, vs_eq W (T (vs_scale V a v)) (vs_scale W a (T v))).

Definition kernel (V W : VectorSpace) (T : vs_carrier V -> vs_carrier W) : vs_carrier V -> Prop :=
  fun v => vs_eq W (T v) (vs_zero W).

Definition image (V W : VectorSpace) (T : vs_carrier V -> vs_carrier W) : vs_carrier W -> Prop :=
  fun w => exists v, vs_eq W (T v) w.

Theorem scale_zero_vec : forall V a, vs_eq V (vs_scale V a (vs_zero V)) (vs_zero V).
Proof. intros V a.
  apply (vs_eq_trans V) with (vs_add V (vs_scale V a (vs_zero V)) (vs_zero V)).
  - apply vs_eq_sym. apply vs_add_zero_r.
  - apply (vs_eq_trans V) with (vs_add V (vs_scale V a (vs_zero V)) (vs_add V (vs_scale V a (vs_zero V)) (vs_neg V (vs_scale V a (vs_zero V))))).
    + apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym. apply vs_add_neg_r.
    + apply (vs_eq_trans V) with (vs_add V (vs_add V (vs_scale V a (vs_zero V)) (vs_scale V a (vs_zero V))) (vs_neg V (vs_scale V a (vs_zero V)))).
      * apply vs_eq_sym. apply vs_add_assoc.
      * apply (vs_eq_trans V) with (vs_add V (vs_scale V a (vs_add V (vs_zero V) (vs_zero V))) (vs_neg V (vs_scale V a (vs_zero V)))).
        { apply vs_add_compat; [|apply vs_eq_refl]. apply vs_eq_sym. apply vs_scale_distrib_vec. }
        apply (vs_eq_trans V) with (vs_add V (vs_scale V a (vs_zero V)) (vs_neg V (vs_scale V a (vs_zero V)))).
        { apply vs_add_compat; [|apply vs_eq_refl]. apply vs_scale_compat. apply vs_add_zero_r. }
        apply vs_add_neg_r. Qed.

Theorem scale_zero_scalar : forall V v, vs_eq V (vs_scale V 0 v) (vs_zero V).
Proof. intros V v.
  apply (vs_eq_trans V) with (vs_add V (vs_scale V 0 v) (vs_zero V)).
  - apply vs_eq_sym. apply vs_add_zero_r.
  - apply (vs_eq_trans V) with (vs_add V (vs_scale V 0 v) (vs_add V (vs_scale V 0 v) (vs_neg V (vs_scale V 0 v)))).
    + apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym. apply vs_add_neg_r.
    + apply (vs_eq_trans V) with (vs_add V (vs_add V (vs_scale V 0 v) (vs_scale V 0 v)) (vs_neg V (vs_scale V 0 v))).
      * apply vs_eq_sym. apply vs_add_assoc.
      * apply (vs_eq_trans V) with (vs_add V (vs_scale V (0+0) v) (vs_neg V (vs_scale V 0 v))).
        { apply vs_add_compat; [|apply vs_eq_refl]. apply vs_eq_sym. apply vs_scale_distrib_scalar. }
        apply vs_add_neg_r. Qed.

Theorem neg_involutive : forall V v, vs_eq V (vs_neg V (vs_neg V v)) v.
Proof. intros V v.
  apply (vs_eq_trans V) with (vs_add V (vs_neg V (vs_neg V v)) (vs_zero V)).
  - apply vs_eq_sym. apply vs_add_zero_r.
  - apply (vs_eq_trans V) with (vs_add V (vs_neg V (vs_neg V v)) (vs_add V (vs_neg V v) v)).
    + apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym.
      apply (vs_eq_trans V) with (vs_add V v (vs_neg V v)). apply vs_add_comm. apply vs_add_neg_r.
    + apply (vs_eq_trans V) with (vs_add V (vs_add V (vs_neg V (vs_neg V v)) (vs_neg V v)) v).
      * apply vs_eq_sym. apply vs_add_assoc.
      * apply (vs_eq_trans V) with (vs_add V (vs_zero V) v).
        { apply vs_add_compat; [|apply vs_eq_refl]. apply (vs_eq_trans V) with (vs_add V (vs_neg V v) (vs_neg V (vs_neg V v))). apply vs_add_comm. apply vs_add_neg_r. }
        apply (vs_eq_trans V) with (vs_add V v (vs_zero V)). apply vs_add_comm. apply vs_add_zero_r. Qed.

Theorem add_neg_l : forall V v, vs_eq V (vs_add V (vs_neg V v) v) (vs_zero V).
Proof. intros V v. apply (vs_eq_trans V) with (vs_add V v (vs_neg V v)). apply vs_add_comm. apply vs_add_neg_r. Qed.

Theorem add_zero_l : forall V v, vs_eq V (vs_add V (vs_zero V) v) v.
Proof. intros V v. apply (vs_eq_trans V) with (vs_add V v (vs_zero V)). apply vs_add_comm. apply vs_add_zero_r. Qed.

Theorem scale_neg_one : forall V v, vs_eq V (vs_scale V (-(1)) v) (vs_neg V v).
Proof. intros V v.
  assert (H : vs_eq V (vs_add V (vs_scale V (-(1)) v) v) (vs_zero V)).
  { apply (vs_eq_trans V) with (vs_add V (vs_scale V (-(1)) v) (vs_scale V 1 v)).
    - apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym. apply vs_scale_one.
    - apply (vs_eq_trans V) with (vs_scale V (-(1) + 1) v).
      + apply vs_eq_sym. apply vs_scale_distrib_scalar.
      + apply scale_zero_scalar. }
  apply (vs_eq_trans V) with (vs_add V (vs_scale V (-(1)) v) (vs_zero V)).
  - apply vs_eq_sym. apply vs_add_zero_r.
  - apply (vs_eq_trans V) with (vs_add V (vs_scale V (-(1)) v) (vs_add V v (vs_neg V v))).
    + apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym. apply vs_add_neg_r.
    + apply (vs_eq_trans V) with (vs_add V (vs_add V (vs_scale V (-(1)) v) v) (vs_neg V v)).
      * apply vs_eq_sym. apply vs_add_assoc.
      * apply (vs_eq_trans V) with (vs_add V (vs_zero V) (vs_neg V v)).
        { apply vs_add_compat; [exact H|apply vs_eq_refl]. }
        apply (vs_eq_trans V) with (vs_add V (vs_neg V v) (vs_zero V)). apply vs_add_comm. apply vs_add_zero_r. Qed.

Theorem linear_preserves_zero : forall V W T, is_linear V W T -> vs_eq W (T (vs_zero V)) (vs_zero W).
Proof. intros V W T [Hcompat [Hadd Hscale]].
  apply (vs_eq_trans W) with (vs_scale W 0 (T (vs_zero V))).
  - apply (vs_eq_trans W) with (T (vs_scale V 0 (vs_zero V))).
    + apply vs_eq_sym. apply Hcompat. apply scale_zero_scalar.
    + apply Hscale.
  - apply scale_zero_scalar. Qed.

Theorem linear_preserves_neg : forall V W T v, is_linear V W T -> vs_eq W (T (vs_neg V v)) (vs_neg W (T v)).
Proof. intros V W T v [Hcompat [Hadd Hscale]].
  assert (Hsum : vs_eq W (vs_add W (T (vs_neg V v)) (T v)) (vs_zero W)).
  { apply (vs_eq_trans W) with (T (vs_add V (vs_neg V v) v)). apply vs_eq_sym. apply Hadd.
    apply (vs_eq_trans W) with (T (vs_zero V)). apply Hcompat. apply add_neg_l.
    apply linear_preserves_zero. split; [exact Hcompat|split; assumption]. }
  apply (vs_eq_trans W) with (vs_add W (T (vs_neg V v)) (vs_zero W)).
  - apply vs_eq_sym. apply vs_add_zero_r.
  - apply (vs_eq_trans W) with (vs_add W (T (vs_neg V v)) (vs_add W (T v) (vs_neg W (T v)))).
    + apply vs_add_compat; [apply vs_eq_refl|]. apply vs_eq_sym. apply vs_add_neg_r.
    + apply (vs_eq_trans W) with (vs_add W (vs_add W (T (vs_neg V v)) (T v)) (vs_neg W (T v))).
      * apply vs_eq_sym. apply vs_add_assoc.
      * apply (vs_eq_trans W) with (vs_add W (vs_zero W) (vs_neg W (T v))).
        { apply vs_add_compat; [exact Hsum|apply vs_eq_refl]. }
        apply (vs_eq_trans W) with (vs_add W (vs_neg W (T v)) (vs_zero W)). apply vs_add_comm. apply vs_add_zero_r. Qed.

Theorem linear_composition : forall V W X T1 T2, is_linear V W T1 -> is_linear W X T2 -> is_linear V X (fun x => T2 (T1 x)).
Proof. intros V W X T1 T2 [H1c [H1a H1s]] [H2c [H2a H2s]]. split; [|split].
  - intros u u2 Hu. apply H2c. apply H1c. exact Hu.
  - intros u v. apply (vs_eq_trans X) with (T2 (vs_add W (T1 u) (T1 v))). apply H2c. apply H1a. apply H2a.
  - intros a v. apply (vs_eq_trans X) with (T2 (vs_scale W a (T1 v))). apply H2c. apply H1s. apply H2s. Qed.

Theorem kernel_is_subspace : forall V W T, is_linear V W T -> is_subspace V (kernel V W T).
Proof. intros V W T Hlin. unfold is_subspace, kernel. split; [|split].
  - apply linear_preserves_zero. exact Hlin.
  - intros u v Hu Hv. destruct Hlin as [Hcompat [Hadd Hscale]].
    apply (vs_eq_trans W) with (vs_add W (T u) (T v)). apply Hadd.
    apply (vs_eq_trans W) with (vs_add W (vs_zero W) (T v)). apply vs_add_compat; [exact Hu|apply vs_eq_refl].
    apply (vs_eq_trans W) with (vs_add W (T v) (vs_zero W)). apply vs_add_comm.
    apply (vs_eq_trans W) with (T v). apply vs_add_zero_r. exact Hv.
  - intros a v Hv. destruct Hlin as [Hcompat [Hadd Hscale]].
    apply (vs_eq_trans W) with (vs_scale W a (T v)). apply Hscale.
    apply (vs_eq_trans W) with (vs_scale W a (vs_zero W)). apply vs_scale_compat. exact Hv.
    apply scale_zero_vec. Qed.

Theorem image_is_subspace : forall V W T, is_linear V W T -> is_subspace W (image V W T).
Proof. intros V W T Hlin. unfold is_subspace, image. split; [|split].
  - exists (vs_zero V). apply linear_preserves_zero. exact Hlin.
  - intros u v [xu Hxu] [xv Hxv]. exists (vs_add V xu xv). destruct Hlin as [Hcompat [Hadd Hscale]].
    apply (vs_eq_trans W) with (vs_add W (T xu) (T xv)). apply Hadd. apply vs_add_compat; [exact Hxu|exact Hxv].
  - intros a v [xv Hxv]. exists (vs_scale V a xv). destruct Hlin as [Hcompat [Hadd Hscale]].
    apply (vs_eq_trans W) with (vs_scale W a (T xv)). apply Hscale. apply vs_scale_compat. exact Hxv. Qed.

Theorem subspace_intersection : forall V W1 W2, is_subspace V W1 -> is_subspace V W2 -> is_subspace V (fun x => W1 x /\ W2 x).
Proof. intros V W1 W2 [Hz1 [Ha1 Hs1]] [Hz2 [Ha2 Hs2]]. unfold is_subspace. split; [|split].
  - split; [exact Hz1|exact Hz2].
  - intros u v [Hu1 Hu2] [Hv1 Hv2]. split; [apply Ha1; assumption|apply Ha2; assumption].
  - intros a v [Hv1 Hv2]. split; [apply Hs1; assumption|apply Hs2; assumption]. Qed.

Theorem id_is_linear : forall V, is_linear V V (fun x => x).
Proof. intros V. split; [|split]. intros u u2 Hu. exact Hu. intros u v. apply vs_eq_refl. intros a v. apply vs_eq_refl. Qed.

Theorem zero_map_is_linear : forall V W, is_linear V W (fun _ => vs_zero W).
Proof. intros V W. split; [|split]. intros u u2 Hu. apply vs_eq_refl. intros u v. apply vs_eq_sym. apply add_zero_l. intros a v. apply vs_eq_sym. apply scale_zero_vec. Qed.

(* ================================================================= *)
(** * QVec Helpers and Concrete Instance                             *)
(* ================================================================= *)

Lemma nth_map2_Qeq : forall (f : Q -> Q -> Q) (l1 l2 : list Q) (i : nat),
  (i < length l1)%nat -> length l1 = length l2 ->
  nth i (map2 f l1 l2) 0 == f (nth i l1 0) (nth i l2 0).
Proof.
  intros f l1. induction l1 as [|x xs IH]; intros l2 i Hi Hlen.
  - simpl in Hi. lia.
  - destruct l2 as [|y ys]. simpl in Hlen. discriminate.
    destruct i as [|i2].
    + simpl. reflexivity.
    + simpl. apply IH. simpl in Hi. lia. simpl in Hlen. lia.
Qed.

Definition qv_neg {n} (v : QVec n) : QVec n := qv_scale (-(1)) v.

Lemma qv_neg_nth : forall {n} (v : QVec n) i, (i < n)%nat -> qv_nth (qv_neg v) i == -(qv_nth v i).
Proof.
  intros n v i Hi. unfold qv_neg, qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  remember (nth i (qv_data v) 0) as q. field.
Qed.

Lemma qv_add_zero_r_local : forall {n} (v : QVec n), qv_eq (qv_add v (qv_zero n)) v.
Proof.
  intros n v. intros i Hi. unfold qv_nth, qv_add, qv_zero. simpl.
  generalize dependent i.
  destruct v as [data Hlen]. simpl. subst n.
  induction data as [|x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i2].
    + simpl. field.
    + simpl. apply IH. change (length (x :: xs)) with (S (length xs)) in Hi. lia.
Qed.

Lemma qv_add_neg_r_local : forall {n} (v : QVec n), qv_eq (qv_add v (qv_neg v)) (qv_zero n).
Proof.
  intros n v i Hi. unfold qv_nth, qv_add, qv_neg, qv_scale, qv_zero. simpl.
  destruct v as [data Hlen]. simpl.
  generalize dependent i. subst n.
  induction data as [|x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i2].
    + simpl. field.
    + simpl. apply IH. change (length (x :: xs)) with (S (length xs)) in Hi. lia.
Qed.

Lemma qv_scale_assoc_rev : forall {n} (a b : Q) (v : QVec n), qv_eq (qv_scale a (qv_scale b v)) (qv_scale (a * b) v).
Proof. intros n a b v i Hi. apply Qeq_sym. apply (qv_scale_assoc a b v i Hi). Qed.

Lemma qv_scale_distrib_scalar_local : forall {n} (a b : Q) (v : QVec n), qv_eq (qv_scale (a + b) v) (qv_add (qv_scale a v) (qv_scale b v)).
Proof.
  intros n a b v i Hi. unfold qv_nth, qv_scale, qv_add. simpl.
  destruct v as [data Hlen]. simpl.
  generalize dependent i. subst n.
  induction data as [|x xs IH]; intros i Hi.
  - simpl in Hi. lia.
  - destruct i as [|i2].
    + simpl. field.
    + simpl. apply IH. change (length (x :: xs)) with (S (length xs)) in Hi. lia.
Qed.

Lemma qv_add_compat_local : forall {n} (u u2 v v2 : QVec n), qv_eq u u2 -> qv_eq v v2 -> qv_eq (qv_add u v) (qv_add u2 v2).
Proof.
  intros n u u2 v v2 Hu Hv i Hi.
  unfold qv_nth, qv_add. simpl.
  rewrite nth_map2_Qeq; [| rewrite (qv_length u); exact Hi | rewrite (qv_length u), (qv_length v); reflexivity].
  rewrite nth_map2_Qeq; [| rewrite (qv_length u2); exact Hi | rewrite (qv_length u2), (qv_length v2); reflexivity].
  unfold qv_nth in Hu, Hv. rewrite (Hu i Hi), (Hv i Hi). reflexivity.
Qed.

Lemma qv_neg_compat_local : forall {n} (v v2 : QVec n), qv_eq v v2 -> qv_eq (qv_neg v) (qv_neg v2).
Proof.
  intros n v v2 Hv i Hi.
  unfold qv_neg, qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  rewrite nth_map_Qeq; [| rewrite (qv_length v2); exact Hi].
  unfold qv_nth in Hv. rewrite (Hv i Hi). reflexivity.
Qed.

Lemma qv_scale_compat_local : forall {n} (a : Q) (v v2 : QVec n), qv_eq v v2 -> qv_eq (qv_scale a v) (qv_scale a v2).
Proof.
  intros n a v v2 Hv i Hi.
  unfold qv_nth, qv_scale. simpl.
  rewrite nth_map_Qeq; [| rewrite (qv_length v); exact Hi].
  rewrite nth_map_Qeq; [| rewrite (qv_length v2); exact Hi].
  unfold qv_nth in Hv. rewrite (Hv i Hi). reflexivity.
Qed.

Definition QVec_VS (n : nat) : VectorSpace :=
  mkVectorSpace (QVec n) (@qv_eq n) (@qv_add n) (qv_zero n) (@qv_neg n) (@qv_scale n)
    (@qv_eq_refl n) (@qv_eq_sym n) (@qv_eq_trans n)
    (@qv_add_compat_local n) (@qv_neg_compat_local n) (@qv_scale_compat_local n)
    (@qv_add_comm n) (@qv_add_assoc n) (@qv_add_zero_r_local n) (@qv_add_neg_r_local n)
    (@qv_scale_assoc_rev n) (@qv_scale_one n) (@qv_scale_distrib n) (@qv_scale_distrib_scalar_local n).

Lemma QVec_VS_zero_correct : forall n, vs_zero (QVec_VS n) = qv_zero n.
Proof. reflexivity. Qed.

Lemma QVec_VS_add_correct : forall n (u v : QVec n), vs_add (QVec_VS n) u v = qv_add u v.
Proof. reflexivity. Qed.

Lemma QVec_VS_scale_correct : forall n (a : Q) (v : QVec n), vs_scale (QVec_VS n) a v = qv_scale a v.
Proof. reflexivity. Qed.

Lemma QVec_VS_neg_correct : forall n (v : QVec n), vs_neg (QVec_VS n) v = qv_neg v.
Proof. reflexivity. Qed.

