(** * Lattice.v — Lattice Theory and Knaster-Tarski Fixed Point

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: lattice members (ordered values)
    Roles:    meet -> Greatest Lower Bound, join -> Least Upper Bound
    Rules:    partial order + meet/join laws (constitution = lattice axioms)
    Status:   top | bottom | comparable | incomparable

    Connection: L5Resolution.v (total orders are lattices)
    Connection: FixedPoint.v (Banach contraction vs Knaster-Tarski)

    STATUS: 30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
From ToS Require Import TheoryOfSystems_Core_ERR.

(* ================================================================= *)
(*  PART I: PARTIAL ORDER                                             *)
(* ================================================================= *)

Record PartialOrder := mkPartialOrder {
  po_carrier : Type;
  po_le : po_carrier -> po_carrier -> Prop;
  po_refl : forall x, po_le x x;
  po_antisym : forall x y, po_le x y -> po_le y x -> x = y;
  po_trans : forall x y z, po_le x y -> po_le y z -> po_le x z;
}.

(* ================================================================= *)
(*  PART II: LATTICE                                                  *)
(* ================================================================= *)

Record Lattice := mkLattice {
  lat_po : PartialOrder;
  lat_meet : po_carrier lat_po -> po_carrier lat_po -> po_carrier lat_po;
  lat_join : po_carrier lat_po -> po_carrier lat_po -> po_carrier lat_po;
  (* meet is glb *)
  lat_meet_lb_l : forall x y, po_le lat_po (lat_meet x y) x;
  lat_meet_lb_r : forall x y, po_le lat_po (lat_meet x y) y;
  lat_meet_greatest : forall x y z,
    po_le lat_po z x -> po_le lat_po z y -> po_le lat_po z (lat_meet x y);
  (* join is lub *)
  lat_join_ub_l : forall x y, po_le lat_po x (lat_join x y);
  lat_join_ub_r : forall x y, po_le lat_po y (lat_join x y);
  lat_join_least : forall x y z,
    po_le lat_po x z -> po_le lat_po y z -> po_le lat_po (lat_join x y) z;
}.

(* ================================================================= *)
(*  PART III: COMPLETE LATTICE                                        *)
(* ================================================================= *)

Record CompleteLattice := mkCompleteLattice {
  cl_lat : Lattice;
  cl_sup : (po_carrier (lat_po cl_lat) -> Prop) -> po_carrier (lat_po cl_lat);
  cl_inf : (po_carrier (lat_po cl_lat) -> Prop) -> po_carrier (lat_po cl_lat);
  cl_sup_ub : forall S x, S x -> po_le (lat_po cl_lat) x (cl_sup S);
  cl_sup_least : forall S u,
    (forall x, S x -> po_le (lat_po cl_lat) x u) ->
    po_le (lat_po cl_lat) (cl_sup S) u;
  cl_inf_lb : forall S x, S x -> po_le (lat_po cl_lat) (cl_inf S) x;
  cl_inf_greatest : forall S l,
    (forall x, S x -> po_le (lat_po cl_lat) l x) ->
    po_le (lat_po cl_lat) l (cl_inf S);
}.

(* ================================================================= *)
(*  PART IV: MONOTONICITY AND FIXED POINTS                            *)
(* ================================================================= *)

Definition is_monotone (L : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat L)) -> po_carrier (lat_po (cl_lat L))) :=
  forall x y, po_le (lat_po (cl_lat L)) x y ->
              po_le (lat_po (cl_lat L)) (f x) (f y).

Definition is_fixed_point (L : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat L)) -> po_carrier (lat_po (cl_lat L)))
  (x : po_carrier (lat_po (cl_lat L))) :=
  f x = x.

Definition is_pre_fixed_point (L : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat L)) -> po_carrier (lat_po (cl_lat L)))
  (x : po_carrier (lat_po (cl_lat L))) :=
  po_le (lat_po (cl_lat L)) (f x) x.

Definition is_post_fixed_point (L : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat L)) -> po_carrier (lat_po (cl_lat L)))
  (x : po_carrier (lat_po (cl_lat L))) :=
  po_le (lat_po (cl_lat L)) x (f x).

(* Shorthand notations for readability *)
Section LatticeTheorems.

Variable L : Lattice.

Let C := po_carrier (lat_po L).
Let le := po_le (lat_po L).
Let meet := lat_meet L.
Let join := lat_join L.

(* ================================================================= *)
(*  PART V: LATTICE THEOREMS (Qed 1-8)                               *)
(* ================================================================= *)

(** 1. Meet is commutative *)
Lemma meet_comm : forall (x y : C), meet x y = meet y x.
Proof.
  intros x y.
  apply (po_antisym (lat_po L)).
  - apply (lat_meet_greatest L).
    + apply (lat_meet_lb_r L).
    + apply (lat_meet_lb_l L).
  - apply (lat_meet_greatest L).
    + apply (lat_meet_lb_r L).
    + apply (lat_meet_lb_l L).
Qed.

(** 2. Join is commutative *)
Lemma join_comm : forall (x y : C), join x y = join y x.
Proof.
  intros x y.
  apply (po_antisym (lat_po L)).
  - apply (lat_join_least L).
    + apply (lat_join_ub_r L).
    + apply (lat_join_ub_l L).
  - apply (lat_join_least L).
    + apply (lat_join_ub_r L).
    + apply (lat_join_ub_l L).
Qed.

(** 3. Meet is associative *)
Lemma meet_assoc : forall (x y z : C),
  meet (meet x y) z = meet x (meet y z).
Proof.
  intros x y z.
  apply (po_antisym (lat_po L)).
  - apply (lat_meet_greatest L).
    + apply (po_trans (lat_po L)) with (meet x y).
      * apply (lat_meet_lb_l L).
      * apply (lat_meet_lb_l L).
    + apply (lat_meet_greatest L).
      * apply (po_trans (lat_po L)) with (meet x y).
        -- apply (lat_meet_lb_l L).
        -- apply (lat_meet_lb_r L).
      * apply (lat_meet_lb_r L).
  - apply (lat_meet_greatest L).
    + apply (lat_meet_greatest L).
      * apply (lat_meet_lb_l L).
      * apply (po_trans (lat_po L)) with (meet y z).
        -- apply (lat_meet_lb_r L).
        -- apply (lat_meet_lb_l L).
    + apply (po_trans (lat_po L)) with (meet y z).
      * apply (lat_meet_lb_r L).
      * apply (lat_meet_lb_r L).
Qed.

(** 4. Join is associative *)
Lemma join_assoc : forall (x y z : C),
  join (join x y) z = join x (join y z).
Proof.
  intros x y z.
  apply (po_antisym (lat_po L)).
  - apply (lat_join_least L).
    + apply (lat_join_least L).
      * apply (lat_join_ub_l L).
      * apply (po_trans (lat_po L)) with (join y z).
        -- apply (lat_join_ub_l L).
        -- apply (lat_join_ub_r L).
    + apply (po_trans (lat_po L)) with (join y z).
      * apply (lat_join_ub_r L).
      * apply (lat_join_ub_r L).
  - apply (lat_join_least L).
    + apply (po_trans (lat_po L)) with (join x y).
      * apply (lat_join_ub_l L).
      * apply (lat_join_ub_l L).
    + apply (lat_join_least L).
      * apply (po_trans (lat_po L)) with (join x y).
        -- apply (lat_join_ub_r L).
        -- apply (lat_join_ub_l L).
      * apply (lat_join_ub_r L).
Qed.

(** 5. Meet is idempotent *)
Lemma meet_idempotent : forall (x : C), meet x x = x.
Proof.
  intros x.
  apply (po_antisym (lat_po L)).
  - apply (lat_meet_lb_l L).
  - apply (lat_meet_greatest L);
    apply (po_refl (lat_po L)).
Qed.

(** 6. Join is idempotent *)
Lemma join_idempotent : forall (x : C), join x x = x.
Proof.
  intros x.
  apply (po_antisym (lat_po L)).
  - apply (lat_join_least L);
    apply (po_refl (lat_po L)).
  - apply (lat_join_ub_l L).
Qed.

(** 7. Absorption law 1: meet x (join x y) = x *)
Lemma absorption_1 : forall (x y : C), meet x (join x y) = x.
Proof.
  intros x y.
  apply (po_antisym (lat_po L)).
  - apply (lat_meet_lb_l L).
  - apply (lat_meet_greatest L).
    + apply (po_refl (lat_po L)).
    + apply (lat_join_ub_l L).
Qed.

(** 8. Absorption law 2: join x (meet x y) = x *)
Lemma absorption_2 : forall (x y : C), join x (meet x y) = x.
Proof.
  intros x y.
  apply (po_antisym (lat_po L)).
  - apply (lat_join_least L).
    + apply (po_refl (lat_po L)).
    + apply (lat_meet_lb_l L).
  - apply (lat_join_ub_l L).
Qed.

End LatticeTheorems.

(* ================================================================= *)
(*  PART VI: KNASTER-TARSKI (Qed 9-11)                               *)
(* ================================================================= *)

(** 9. Knaster-Tarski Fixed Point Theorem (existential version):
    Every monotone function on a complete lattice has a fixed point. *)
Theorem knaster_tarski : forall (CL : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat CL)) -> po_carrier (lat_po (cl_lat CL))),
  is_monotone CL f ->
  exists p, is_fixed_point CL f p.
Proof.
  intros CL f Hmono.
  (* Use infimum of pre-fixed points: p = inf {x | f(x) <= x} *)
  pose (PO := lat_po (cl_lat CL)).
  pose (Pre := fun x : po_carrier PO => po_le PO (f x) x).
  pose (p := cl_inf CL Pre).
  exists p.
  unfold is_fixed_point.
  apply (po_antisym PO).
  - (* f(p) <= p: p = inf Pre, so for all q in Pre, p <= q, hence f(p) <= f(q) <= q,
       so f(p) is a lower bound of Pre, hence f(p) <= inf Pre = p. *)
    apply (cl_inf_greatest CL Pre (f p)).
    intros q Hq.
    apply (po_trans PO) with (f q).
    + apply Hmono. apply (cl_inf_lb CL Pre q Hq).
    + exact Hq.
  - (* p <= f(p): since f(p) <= p (shown above), f(f(p)) <= f(p) by mono,
       so f(p) is in Pre, hence p = inf Pre <= f(p). *)
    apply (cl_inf_lb CL Pre (f p)).
    unfold Pre. apply Hmono.
    apply (cl_inf_greatest CL Pre (f p)).
    intros q Hq.
    apply (po_trans PO) with (f q).
    + apply Hmono. apply (cl_inf_lb CL Pre q Hq).
    + exact Hq.
Qed.

(** 10. Knaster-Tarski LFP: inf of pre-fixed points is the least fixed point *)
Theorem knaster_tarski_lfp : forall (CL : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat CL)) -> po_carrier (lat_po (cl_lat CL))),
  is_monotone CL f ->
  let PO := lat_po (cl_lat CL) in
  let Pre := fun x => po_le PO (f x) x in
  let p := cl_inf CL Pre in
  is_fixed_point CL f p /\ (forall q, is_pre_fixed_point CL f q -> po_le PO p q).
Proof.
  intros CL f Hmono PO Pre p.
  assert (Hp_pre : po_le PO (f p) p).
  { apply (cl_inf_greatest CL Pre (f p)).
    intros q Hq. unfold Pre in Hq.
    apply (po_trans PO) with (f q).
    - apply Hmono. apply (cl_inf_lb CL Pre q Hq).
    - exact Hq.
  }
  assert (Hp_post : po_le PO p (f p)).
  { apply (cl_inf_lb CL Pre (f p)).
    unfold Pre. apply Hmono. exact Hp_pre.
  }
  split.
  - unfold is_fixed_point.
    apply (po_antisym PO); assumption.
  - intros q Hq.
    apply (cl_inf_lb CL Pre q). exact Hq.
Qed.

(** 11. Knaster-Tarski GFP: sup of post-fixed points is the greatest fixed point *)
Theorem knaster_tarski_gfp : forall (CL : CompleteLattice)
  (f : po_carrier (lat_po (cl_lat CL)) -> po_carrier (lat_po (cl_lat CL))),
  is_monotone CL f ->
  let PO := lat_po (cl_lat CL) in
  let Post := fun x => po_le PO x (f x) in
  let q := cl_sup CL Post in
  is_fixed_point CL f q /\ (forall p, is_post_fixed_point CL f p -> po_le PO p q).
Proof.
  intros CL f Hmono PO Post q.
  assert (Hq_post : po_le PO q (f q)).
  { apply (cl_sup_least CL Post (f q)).
    intros x Hx. unfold Post in Hx.
    apply (po_trans PO) with (f x).
    - exact Hx.
    - apply Hmono. apply (cl_sup_ub CL Post x Hx).
  }
  assert (Hq_pre : po_le PO (f q) q).
  { apply (cl_sup_ub CL Post (f q)).
    unfold Post. apply Hmono. exact Hq_post.
  }
  split.
  - unfold is_fixed_point.
    apply (po_antisym PO); assumption.
  - intros p Hp.
    apply (cl_sup_ub CL Post p). exact Hp.
Qed.

(* ================================================================= *)
(*  PART VII: BOOL INSTANCES (Qed 12-13)                              *)
(* ================================================================= *)

Definition bool_le (a b : bool) : Prop := implb a b = true.

Lemma bool_po_refl : forall a, bool_le a a.
Proof. intros a. unfold bool_le. destruct a; simpl; reflexivity. Qed.

Lemma bool_po_antisym : forall a b, bool_le a b -> bool_le b a -> a = b.
Proof.
  intros a b H1 H2. unfold bool_le in *.
  destruct a, b; simpl in *; auto; discriminate.
Qed.

Lemma bool_po_trans : forall a b c, bool_le a b -> bool_le b c -> bool_le a c.
Proof.
  intros a b c H1 H2. unfold bool_le in *.
  destruct a, b, c; simpl in *; auto; discriminate.
Qed.

Definition bool_po : PartialOrder := mkPartialOrder
  bool bool_le bool_po_refl bool_po_antisym bool_po_trans.

(** 12. Bool lattice: meet = andb, join = orb *)
Lemma bool_meet_lb_l : forall x y, bool_le (andb x y) x.
Proof. intros x y. unfold bool_le. destruct x, y; simpl; reflexivity. Qed.

Lemma bool_meet_lb_r : forall x y, bool_le (andb x y) y.
Proof. intros x y. unfold bool_le. destruct x, y; simpl; reflexivity. Qed.

Lemma bool_meet_greatest : forall x y z,
  bool_le z x -> bool_le z y -> bool_le z (andb x y).
Proof.
  intros x y z. unfold bool_le. destruct x, y, z; simpl; auto.
Qed.

Lemma bool_join_ub_l : forall x y, bool_le x (orb x y).
Proof. intros x y. unfold bool_le. destruct x, y; simpl; reflexivity. Qed.

Lemma bool_join_ub_r : forall x y, bool_le y (orb x y).
Proof. intros x y. unfold bool_le. destruct x, y; simpl; reflexivity. Qed.

Lemma bool_join_least : forall x y z,
  bool_le x z -> bool_le y z -> bool_le (orb x y) z.
Proof.
  intros x y z. unfold bool_le. destruct x, y, z; simpl; auto.
Qed.

(** 12. Bool lattice construction *)
Definition bool_lattice : Lattice := mkLattice
  bool_po andb orb
  bool_meet_lb_l bool_meet_lb_r bool_meet_greatest
  bool_join_ub_l bool_join_ub_r bool_join_least.

(** 13. Bool lattice: false is bottom *)
Lemma bool_false_bottom : forall b, bool_le false b.
Proof. intros b. unfold bool_le. destruct b; simpl; reflexivity. Qed.

(* ================================================================= *)
(*  PART VIII: NAT INSTANCE (Qed 14)                                  *)
(* ================================================================= *)

Lemma nat_po_refl : forall x : nat, x <= x.
Proof. intros. lia. Qed.

Lemma nat_po_antisym : forall x y : nat, x <= y -> y <= x -> x = y.
Proof. intros. lia. Qed.

Lemma nat_po_trans : forall x y z : nat, x <= y -> y <= z -> x <= z.
Proof. intros. lia. Qed.

(** 14. Nat partial order construction *)
Definition nat_po : PartialOrder := mkPartialOrder
  nat Nat.le nat_po_refl nat_po_antisym nat_po_trans.

(* ================================================================= *)
(*  PART IX: ADDITIONAL STRUCTURAL LEMMAS (Qed 15-20)                *)
(* ================================================================= *)

(** 15. le iff meet: x <= y <-> meet x y = x *)
Lemma le_iff_meet : forall (La : Lattice) (x y : po_carrier (lat_po La)),
  po_le (lat_po La) x y <-> lat_meet La x y = x.
Proof.
  intros La x y. split.
  - intros Hle.
    apply (po_antisym (lat_po La)).
    + apply (lat_meet_lb_l La).
    + apply (lat_meet_greatest La).
      * apply (po_refl (lat_po La)).
      * exact Hle.
  - intros Heq.
    rewrite <- Heq.
    apply (lat_meet_lb_r La).
Qed.

(** 16. le iff join: x <= y <-> join x y = y *)
Lemma le_iff_join : forall (La : Lattice) (x y : po_carrier (lat_po La)),
  po_le (lat_po La) x y <-> lat_join La x y = y.
Proof.
  intros La x y. split.
  - intros Hle.
    apply (po_antisym (lat_po La)).
    + apply (lat_join_least La).
      * exact Hle.
      * apply (po_refl (lat_po La)).
    + apply (lat_join_ub_r La).
  - intros Heq.
    rewrite <- Heq.
    apply (lat_join_ub_l La).
Qed.

(** 17. Meet is monotone in the left argument *)
Lemma meet_monotone_l : forall (La : Lattice) (x y z : po_carrier (lat_po La)),
  po_le (lat_po La) x y ->
  po_le (lat_po La) (lat_meet La x z) (lat_meet La y z).
Proof.
  intros La x y z Hle.
  apply (lat_meet_greatest La).
  - apply (po_trans (lat_po La)) with x.
    + apply (lat_meet_lb_l La).
    + exact Hle.
  - apply (lat_meet_lb_r La).
Qed.

(** 18. Join is monotone in the left argument *)
Lemma join_monotone_l : forall (La : Lattice) (x y z : po_carrier (lat_po La)),
  po_le (lat_po La) x y ->
  po_le (lat_po La) (lat_join La x z) (lat_join La y z).
Proof.
  intros La x y z Hle.
  apply (lat_join_least La).
  - apply (po_trans (lat_po La)) with y.
    + exact Hle.
    + apply (lat_join_ub_l La).
  - apply (lat_join_ub_r La).
Qed.

(** 19. Fixed point of identity is every element *)
Lemma id_fixed_point : forall (CL : CompleteLattice)
  (x : po_carrier (lat_po (cl_lat CL))),
  is_fixed_point CL (fun a => a) x.
Proof.
  intros CL x. unfold is_fixed_point. reflexivity.
Qed.

(** 20. Identity is monotone *)
Lemma id_is_monotone : forall (CL : CompleteLattice),
  is_monotone CL (fun a => a).
Proof.
  intros CL. unfold is_monotone. intros x y Hle. exact Hle.
Qed.
