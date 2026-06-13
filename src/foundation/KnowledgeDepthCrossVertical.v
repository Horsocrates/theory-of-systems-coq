(** * KnowledgeDepthCrossVertical.v — cross-vertical comparison is PARTIAL, mediated by a shared
      node (deepening of KnowledgeDepth's honest stop "no cross-vertical scale")

    Direction C (honest deepening).  KnowledgeDepth.v kept only the within-vertical partial order
    "deeper/shallower" and STOPPED honestly: no numeric depth measure across verticals, tiers of one
    vertical comparable, different verticals not.  That stop can be SHARPENED: across verticals,
    comparison is not simply absent — it is PARTIAL, possible ONLY through a SHARED node, and even
    then only locally (each branch comparable to the shared node, the branches not to each other).
    There is still NO global numeric scale.

    The encompassing relation `enc` (y encompasses x = x is a deeper sub-tier of y) is a PARTIAL
    order; comparability = enc-connectedness.  Within one vertical (a chain) it is linear (every
    pair comparable) — the KnowledgeDepth order.  Across two verticals sharing a node s: both
    branches are comparable to s, yet two tiers on different branches above s stay INCOMPARABLE.
    So a shared node mediates only partially; comparison is a partial order, never total.

    (Parallel to KnowledgeCollective: cross-vertical comparison, like collective composition, needs
    a shared node — and even then is partial.)

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) within a vertical (a chain) comparison is LINEAR — every two tiers comparable;
      (2) ACROSS verticals comparison runs only through a SHARED node;
      (3) even a shared node gives only PARTIAL comparability (each branch to the node, the branches
          not to each other);
      (4) there is NO global numeric scale.
    Roles (L4): enc = the partial order "encompasses / deeper"; a vertical = a chain (linear within);
      a shared node = the mediator of comparison; comparable = enc-connectedness.
    Elements (L1+P4): tiers; verticals (chains of tiers); the shared node.
    P4 diagnostic (could it be otherwise?):
      Cross-vertical comparison is FORCED to be partial: comparable is reflexive and symmetric but
      NOT total (incomparable pairs exist); a shared node mediates (both branches comparable to it)
      but the branches stay incomparable; no total order.  This sharpens KnowledgeDepth's "no
      cross-vertical scale": not "incomparable outright", but "partially comparable through a shared
      node".
    Honesty wall:
      "deeper / shallower" is a PARTIAL order, not a number; no global numeric depth across verticals;
      "science deepens" stays an organizational reading, not a theorem.  The shared-node mediation is
      structural; it does not manufacture a cross-vertical metric.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat.

(* ===================================================================== *)
(*  PART I — the encompassing partial order; comparability = connectedness *)
(* ===================================================================== *)

Section CrossVertical.
Context {Tier : Type}.
Variable enc : Tier -> Tier -> Prop.   (* enc x y : y encompasses x (x a deeper sub-tier of y) *)
Hypothesis enc_refl  : forall t, enc t t.
Hypothesis enc_trans : forall a b c, enc a b -> enc b c -> enc a c.
Hypothesis enc_antisym : forall a b, enc a b -> enc b a -> a = b.

(** Two tiers are comparable iff one encompasses the other (enc-connected). *)
Definition comparable (t1 t2 : Tier) : Prop := enc t1 t2 \/ enc t2 t1.

Lemma comparable_refl : forall t, comparable t t.
Proof. intro t. left. apply enc_refl. Qed.

Lemma comparable_sym : forall t1 t2, comparable t1 t2 -> comparable t2 t1.
Proof. intros t1 t2 [H | H]; [ right | left ]; exact H. Qed.

(** ★ A SHARED node mediates: if a node s encompasses both t1 and t2, each branch is comparable to
    s.  (s is the common reference through which the verticals can be compared at all.) *)
Theorem shared_node_mediates : forall t1 t2 s,
  enc t1 s -> enc t2 s -> comparable t1 s /\ comparable t2 s.
Proof. intros t1 t2 s H1 H2. split; left; assumption. Qed.

End CrossVertical.

(* ===================================================================== *)
(*  PART II — a concrete two-branch DAG: shared node, branches incomparable *)
(*  s = 0 encompasses a1 = 1 and a2 = 2 (two verticals meeting at 0)        *)
(* ===================================================================== *)

Definition enc_c (x y : nat) : Prop := x = y \/ (y = 0 /\ (x = 1 \/ x = 2)).

Lemma enc_c_refl : forall t, enc_c t t.
Proof. intro t. left. reflexivity. Qed.

Lemma enc_c_trans : forall a b c, enc_c a b -> enc_c b c -> enc_c a c.
Proof.
  intros a b c Hab Hbc. destruct Hab as [E | [Eb Ha]].
  - subst b. exact Hbc.
  - subst b. destruct Hbc as [E0 | [Ec H0]].
    + subst c. right. split; [ reflexivity | exact Ha ].
    + destruct H0; discriminate.
Qed.

Lemma enc_c_antisym : forall a b, enc_c a b -> enc_c b a -> a = b.
Proof.
  intros a b Hab Hba. destruct Hab as [E | [Eb Ha]]; [ exact E | ].
  subst b. exfalso. destruct Ha as [Ha | Ha]; subst a;
    destruct Hba as [E0 | [Ea H0]]; discriminate.
Qed.

Definition comp_c := comparable enc_c.

(** ★★ The gem: a SHARED node (0) makes each branch comparable to it, YET the two branches (1 and 2)
    are MUTUALLY INCOMPARABLE.  A shared node mediates only partially — it does not collapse the two
    verticals into one scale. *)
Theorem shared_but_incomparable :
  comp_c 1 0 /\ comp_c 2 0 /\ ~ comp_c 1 2.
Proof.
  unfold comp_c, comparable, enc_c. split; [ | split ].
  - left. right. split; [ reflexivity | left; reflexivity ].
  - left. right. split; [ reflexivity | right; reflexivity ].
  - intros [H | H]; destruct H as [E | [E _]]; discriminate.
Qed.

(** ★ No global total order: there exist incomparable tiers — there is no cross-vertical numeric
    scale. *)
Theorem cross_not_total : exists t1 t2, ~ comp_c t1 t2.
Proof. exists 1, 2. exact (proj2 (proj2 shared_but_incomparable)). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Cross-vertical comparison is PARTIAL: a shared node makes both branches comparable to it,
    yet the branches stay mutually incomparable (shared_but_incomparable); comparison is not total
    (cross_not_total); comparable is reflexive (when enc is) and symmetric — a partial order, never a
    global scale. *)
Theorem cross_vertical_partial :
  (comp_c 1 0 /\ comp_c 2 0 /\ ~ comp_c 1 2)
  /\ (exists t1 t2, ~ comp_c t1 t2)
  /\ (forall (Tier : Type) (enc : Tier -> Tier -> Prop),
        (forall t, enc t t) -> forall t, comparable enc t t)
  /\ (forall (Tier : Type) (enc : Tier -> Tier -> Prop) (t1 t2 : Tier),
        comparable enc t1 t2 -> comparable enc t2 t1).
Proof.
  split; [ exact shared_but_incomparable | ].
  split; [ exact cross_not_total | ].
  split.
  - intros Tier enc Hrefl t. left. apply Hrefl.
  - intros Tier enc t1 t2 H. exact (comparable_sym enc t1 t2 H).
Qed.

Print Assumptions cross_vertical_partial.
Print Assumptions shared_but_incomparable.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Cross-vertical comparison is PARTIAL, mediated by a shared node.  enc      *)
(*  (encompasses) is a partial order (enc_c_refl/trans/antisym witness);      *)
(*  comparability = enc-connectedness (comparable_refl/sym).  A shared node    *)
(*  mediates (shared_node_mediates), but two branches above it stay           *)
(*  incomparable (shared_but_incomparable) and there is no total order        *)
(*  (cross_not_total) — no global numeric depth scale.  Deepens               *)
(*  KnowledgeDepth's honest stop "no cross-vertical scale": partial through a  *)
(*  shared node, not incomparable outright.  Parallel to KnowledgeCollective  *)
(*  (composition needs a shared node).                                       *)
(* ========================================================================= *)
