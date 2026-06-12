(** * LevelNatIso.v — F-12: the Core Level hierarchy IS Peano/nat (on the L1/LS type the repo uses)

    Closes FORMALIZATION-BACKLOG F-12. The standalone L5_NatFromHierarchy.v proved the
    nat-isomorphism + order on a SEPARATE copy (LBase/LSucc); its theorems were not
    literally about the Core type Level (L1/LS) that the book and repository use. Here the
    Peano/order facts are proved ON Core, and the two types are machine-identified by an
    explicit isomorphism.

    Elements: the Core levels L1, LS (TheoryOfSystems_Core_ERR) -- the actual finite levels
              used everywhere; the standalone LBase/LSucc is a foreign copy.
    Roles:    level_to_nat = the counting role (level |-> position, L1 = 0); nat_to_level its
              inverse. Level and nat are one Peano structure, two presentations. level_lt is
              the strict order = nat < under the iso.
    Rules:    the iso is FORCED by the constructor shape (base + unary successor = the initial
              algebra of X |-> 1 + X = nat). Round-trips level_nat_level / nat_level_nat are
              constitutive; "LS is S" is definitional; the order rule
              level_lt l1 l2 <-> level_to_nat l1 < level_to_nat l2 holds BOTH ways (the
              standalone had only level_lt_size, one direction).
    P4:       could the iso be otherwise? NO -- Level is nat up to renaming. The two separate
              Coq declarations were a formal-system artifact, not a real difference; F-12
              removes it (proofs on Core + explicit type iso Core.Level <~> standalone.Level).
              Ties to MetaPairStrength (level_lt is well-founded = the Element/terminating side
              of H1) and P1 (irreflexivity).

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.
From ToS Require Import TheoryOfSystems_Core_ERR.   (* Core Level (L1/LS), level_lt, level_depth *)
From ToS Require foundation.L5_NatFromHierarchy.    (* Require WITHOUT Import (avoid name clash) *)

(* ================================================================== *)
(*  Part I: the Peano bijection  Core.Level <-> nat   (L1 = 0)         *)
(* ================================================================== *)

Fixpoint level_to_nat (l : Level) : nat :=
  match l with L1 => O | LS l' => S (level_to_nat l') end.

Fixpoint nat_to_level (n : nat) : Level :=
  match n with O => L1 | S n' => LS (nat_to_level n') end.

Lemma level_nat_level : forall l, nat_to_level (level_to_nat l) = l.
Proof. induction l; simpl; [ reflexivity | rewrite IHl; reflexivity ]. Qed.

Lemma nat_level_nat : forall n, level_to_nat (nat_to_level n) = n.
Proof. induction n; simpl; [ reflexivity | rewrite IHn; reflexivity ]. Qed.

(** "LS is S": the successor constructor IS nat successor under the count. *)
Lemma level_to_nat_LS : forall l, level_to_nat (LS l) = S (level_to_nat l).
Proof. reflexivity. Qed.

(** Peano companions. *)
Lemma LS_injective : forall l1 l2, LS l1 = LS l2 -> l1 = l2.
Proof. intros l1 l2 H. injection H. auto. Qed.

Lemma L1_not_LS : forall l, L1 <> LS l.
Proof. discriminate. Qed.

Lemma level_to_nat_injective : forall l1 l2,
  level_to_nat l1 = level_to_nat l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- (level_nat_level l1), <- (level_nat_level l2), H. reflexivity.
Qed.

(* ================================================================== *)
(*  Part II: level_lt IS nat < under the iso (BOTH directions)         *)
(* ================================================================== *)

Lemma level_lt_to_nat : forall l1 l2,
  level_lt l1 l2 -> (level_to_nat l1 < level_to_nat l2)%nat.
Proof.
  intros l1 l2; revert l1; induction l2 as [| l2' IH]; intros l1 H.
  - simpl in H. contradiction.
  - simpl in H. destruct H as [Heq | Hlt].
    + subst. simpl. lia.
    + apply IH in Hlt. simpl. lia.
Qed.

Lemma nat_lt_to_level_lt : forall l1 l2,
  (level_to_nat l1 < level_to_nat l2)%nat -> level_lt l1 l2.
Proof.
  intros l1 l2; revert l1; induction l2 as [| l2' IH]; intros l1 H.
  - simpl in H. lia.
  - simpl. simpl in H.
    destruct (Nat.eq_dec (level_to_nat l1) (level_to_nat l2')) as [Heq | Hne].
    + left. apply level_to_nat_injective. exact Heq.
    + right. apply IH. lia.
Qed.

Theorem level_lt_iff_nat_lt : forall l1 l2,
  level_lt l1 l2 <-> (level_to_nat l1 < level_to_nat l2)%nat.
Proof. split; [ apply level_lt_to_nat | apply nat_lt_to_level_lt ]. Qed.

(* ================================================================== *)
(*  Part III: irreflexivity (= P1) and transitivity, ON Core via iso   *)
(* ================================================================== *)

(** = P1_no_self_membership / level_lt_irrefl (Core), re-named and re-derived through
    the iso to exhibit it AS nat-order irreflexivity. *)
Lemma hierarchy_irrefl : forall l, ~ level_lt l l.
Proof. intros l H. apply level_lt_to_nat in H. lia. Qed.

(** Transitivity via the order iso (Core already has level_lt_trans; this names it as
    a consequence of nat transitivity under the iso). *)
Lemma level_lt_trans_via_nat : forall l1 l2 l3,
  level_lt l1 l2 -> level_lt l2 l3 -> level_lt l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  apply level_lt_to_nat in H1; apply level_lt_to_nat in H2.
  apply nat_lt_to_level_lt. lia.
Qed.

(* ================================================================== *)
(*  Part IV: bridge to Core's level_depth (the 1-based ToS number)     *)
(* ================================================================== *)

(** The two depth conventions differ by one: level_depth (Core, L1 = 1) = S of the
    0-based Peano count. So the ToS "level number" is the Peano position + 1. *)
Lemma level_depth_eq : forall l, level_depth l = S (level_to_nat l).
Proof. induction l; simpl; [ reflexivity | rewrite IHl; reflexivity ]. Qed.

(* ================================================================== *)
(*  Part V: explicit type iso  Core.Level <~> standalone.Level         *)
(* ================================================================== *)

Definition core_to_hier (l : Level) : L5_NatFromHierarchy.Level :=
  L5_NatFromHierarchy.nat_to_level (level_to_nat l).

Definition hier_to_core (h : L5_NatFromHierarchy.Level) : Level :=
  nat_to_level (L5_NatFromHierarchy.level_to_nat h).

Lemma core_hier_core : forall l, hier_to_core (core_to_hier l) = l.
Proof.
  intro l. unfold hier_to_core, core_to_hier.
  rewrite L5_NatFromHierarchy.nat_level_nat. apply level_nat_level.
Qed.

Lemma hier_core_hier : forall h, core_to_hier (hier_to_core h) = h.
Proof.
  intro h. unfold core_to_hier, hier_to_core.
  rewrite nat_level_nat. apply L5_NatFromHierarchy.level_nat_level.
Qed.

(* ================================================================== *)
(*  Synthesis: the Core Level hierarchy is Peano, and synchronized      *)
(* ================================================================== *)

Theorem core_level_is_peano :
  (forall l, nat_to_level (level_to_nat l) = l)                              (* bijection -> *)
  /\ (forall n, level_to_nat (nat_to_level n) = n)                           (* bijection <- *)
  /\ (forall l, level_to_nat (LS l) = S (level_to_nat l))                    (* LS is S *)
  /\ (forall l1 l2, level_lt l1 l2 <-> (level_to_nat l1 < level_to_nat l2)%nat) (* order iso *)
  /\ (forall l, ~ level_lt l l)                                             (* P1 / irrefl *)
  /\ (forall l, hier_to_core (core_to_hier l) = l)                          (* type sync -> *)
  /\ (forall h, core_to_hier (hier_to_core h) = h).                         (* type sync <- *)
Proof.
  split; [ exact level_nat_level | ].
  split; [ exact nat_level_nat | ].
  split; [ exact level_to_nat_LS | ].
  split; [ exact level_lt_iff_nat_lt | ].
  split; [ exact hierarchy_irrefl | ].
  split; [ exact core_hier_core | exact hier_core_hier ].
Qed.

Print Assumptions core_level_is_peano.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  15 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The Core Level type (L1/LS) is Peano/nat: bijection, "LS is S", order iso  *)
(*  level_lt <-> nat < (both ways), irreflexivity = P1, depth = position+1;    *)
(*  and Core.Level <~> standalone L5_NatFromHierarchy.Level explicitly. F-12.  *)
(* ========================================================================= *)
