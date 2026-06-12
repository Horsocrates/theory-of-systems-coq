(** * MetaPairStrength.v — Disentangling the two meta-roles: L5/order yields N, L4/grounding yields anti-regress

    Develops GroundedOrderedStructure.v, whose P4 diagnostic (i) notes in PROSE that
    well-foundedness is STRONGER than bare strictness. Here that becomes a THEOREM
    and a MAP of which logical demand rides on which half of the meta-pair.

    Elements: one relation R (the dep edge); two strengths on it — strict_order
              (irreflexive + transitive) and well_founded; a descent f : nat -> U.
    Roles:    strict_order isolates the L5/Порядок role; well_founded isolates the
              L4/ЗДО role. has_infinite_descent R = a NON-terminating process
              (role-limit); ~has_infinite_descent = termination (Element side).
    Rules:    L5/order ALONE yields N — asymmetry and no mediated cycle (clos_trans
              collapses on a transitive R). L4/well-foundedness yields anti-regress
              (no infinite descent). They SEPARATE: a strict (even total) order need
              not be well-founded — counter-model (Z, <), f n = -n. So finite descent
              is the genuine surplus of L4, not of L5.
    P4 diagnostic: well_founded = finite descent = termination = the Element/P4 side
              of the finitization boundary H1. On the SAME order <, nat (well-founded)
              terminates while Z (not) descends forever — exactly the H1 boundary. The
              ToS Level hierarchy (level_lt) is the canonical well-founded model, so
              P1_no_self_membership is the meta-pair's no_self_ground instance and the
              hierarchy admits no infinite regress of levels.

    Honest scope: every fact is standard order theory (a strict order is cycle-free;
    Z is not well-founded; well_founded => no infinite descent). The contribution is
    the E/R/R disentanglement L4<->L5, the separating counter-model, and the H1 bridge.
    No new logic; A=A is NOT derived (see GroundedOrderedStructure header).

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Relations Wellfounded Arith Wf_nat ZArith Lia.
From ToS Require Import foundation.GroundedOrderedStructure.
From ToS Require Import TheoryOfSystems_Core_ERR.

(* ================================================================== *)
(*  Part I: the two strengths, as predicates                          *)
(* ================================================================== *)

Definition strict_order {U : Type} (R : U -> U -> Prop) : Prop :=
  (forall x, ~ R x x) /\ (forall x y z, R x y -> R y z -> R x z).

Definition has_infinite_descent {U : Type} (R : U -> U -> Prop) : Prop :=
  exists f : nat -> U, forall n : nat, R (f (S n)) (f n).

(* ================================================================== *)
(*  Part II: L5/Порядок (strict order) ALONE yields N — no well-found *)
(* ================================================================== *)

Section OrderYieldsN.
  Context {U : Type} (R : U -> U -> Prop) (SO : strict_order R).

  Lemma so_irr   : forall x, ~ R x x.                  Proof. apply SO. Qed.
  Lemma so_trans : forall x y z, R x y -> R y z -> R x z. Proof. apply SO. Qed.

  (** Asymmetry: from irreflexivity + transitivity, not from foundedness. *)
  Theorem order_asym : forall x y, R x y -> ~ R y x.
  Proof. intros x y Hxy Hyx. exact (so_irr x (so_trans x y x Hxy Hyx)). Qed.

  (** A transitive relation absorbs its own transitive closure. *)
  Lemma clos_trans_collapses : forall x y, clos_trans U R x y -> R x y.
  Proof.
    intros x y H. induction H as [a b Hab | a b c Hab IHab Hbc IHbc].
    - exact Hab.
    - exact (so_trans a b c IHab IHbc).
  Qed.

  (** No cycle of any length — N read on the order positions, from L5 alone. *)
  Theorem order_no_mediated_cycle : forall x, ~ clos_trans U R x x.
  Proof. intros x H. exact (so_irr x (clos_trans_collapses x x H)). Qed.
End OrderYieldsN.

(* ================================================================== *)
(*  Part III: the SEPARATION — L5/order does NOT buy anti-regress      *)
(*  counter-model (Z, <): a strict TOTAL order with infinite descent   *)
(* ================================================================== *)

Definition Zdesc (n : nat) : Z := (- Z.of_nat n)%Z.

Lemma Zdesc_step : forall n, (Zdesc (S n) < Zdesc n)%Z.
Proof. intro n. unfold Zdesc. rewrite Nat2Z.inj_succ. lia. Qed.

Theorem Zlt_strict_order : strict_order Z.lt.
Proof.
  split.
  - exact Z.lt_irrefl.
  - intros x y z Hxy Hyz. exact (Z.lt_trans x y z Hxy Hyz).
Qed.

Theorem Zlt_has_infinite_descent : has_infinite_descent Z.lt.
Proof. exists Zdesc. exact Zdesc_step. Qed.

(** ★ The honest price of L4: anti-regress (finite descent) is NOT a consequence of
    L5/order.  A strict order can descend forever. *)
Theorem order_does_not_give_anti_regress :
  exists (V : Type) (R : V -> V -> Prop), strict_order R /\ has_infinite_descent R.
Proof.
  exists Z. exists Z.lt. split; [ exact Zlt_strict_order | exact Zlt_has_infinite_descent ].
Qed.

(* ================================================================== *)
(*  Part IV: L4/ЗДО (well-foundedness) yields anti-regress; H1 bridge  *)
(* ================================================================== *)

(** Well-foundedness = no infinite descent (the file's no_infinite_descent, in the
    descent vocabulary). This is the L4 surplus that L5 lacks (Part III). *)
Theorem wf_no_infinite_descent :
  forall (U : Type) (R : U -> U -> Prop), well_founded R -> ~ has_infinite_descent R.
Proof. intros U R WF [f Hf]. exact (no_infinite_descent U R WF f Hf). Qed.

(** Element side of H1: nat with < is well-founded — every descent terminates. *)
Theorem nat_lt_terminates : ~ has_infinite_descent lt.
Proof. apply wf_no_infinite_descent. exact lt_wf. Qed.

(** ★ The finitization boundary H1, read on the SAME order <: nat (well-founded)
    terminates; Z (not well-founded) descends forever. L4 well-foundedness IS the
    termination / finite-actuality (P4) condition on a grounding order. *)
Theorem finitization_boundary_on_order :
  (~ has_infinite_descent lt) /\ has_infinite_descent Z.lt.
Proof. split; [ exact nat_lt_terminates | exact Zlt_has_infinite_descent ]. Qed.

(* ================================================================== *)
(*  Part V (C): the ToS Level hierarchy is the canonical meta-pair model *)
(* ================================================================== *)

(** level_lt strictly decreases level_depth, hence is well-founded. *)
Theorem level_lt_wf : well_founded level_lt.
Proof. apply (well_founded_lt_compat Level level_depth). exact level_lt_depth. Qed.

(** ★ P1 (no self-membership) recovered as the meta-pair's no_self_ground demand
    on the ToS hierarchy — same Prop as Core's P1_no_self_membership. *)
Theorem P1_from_meta_pair : forall L : Level, ~ (L << L).
Proof. exact (no_self_ground Level level_lt level_lt_wf). Qed.

(** No infinite regress of levels — finite descent on the actual ToS hierarchy. *)
Theorem no_infinite_level_regress :
  forall f : nat -> Level, ~ (forall n : nat, level_lt (f (S n)) (f n)).
Proof. exact (no_infinite_descent Level level_lt level_lt_wf). Qed.

(** The full meta-pair, instantiated on the ToS Level hierarchy. *)
Theorem tos_hierarchy_models_meta_pair :
  (forall L, ~ level_lt L L)
  /\ (forall L M, level_lt L M -> ~ level_lt M L)
  /\ (forall L M, level_lt L M -> L <> M)
  /\ (forall L, ~ clos_trans Level level_lt L L)
  /\ (forall f : nat -> Level, ~ (forall n, level_lt (f (S n)) (f n))).
Proof. exact (meta_pair_demands Level level_lt level_lt_wf). Qed.

(* ================================================================== *)
(*  Part VI: capstone — the disentanglement                            *)
(* ================================================================== *)

(** ★★★ The two meta-roles separate: L5/Порядок buys N (cycle-freedom),
    L4/ЗДО buys anti-regress (finite descent); neither reduces to the other,
    and the ToS Level hierarchy realizes both as a well-founded model. *)
Theorem meta_pair_strength_capstone :
  (* L5/order ALONE yields N *)
  (forall (U : Type) (R : U -> U -> Prop), strict_order R ->
     (forall x y, R x y -> ~ R y x) /\ (forall x, ~ clos_trans U R x x))
  (* but L5/order does NOT yield anti-regress *)
  /\ (exists (V : Type) (R : V -> V -> Prop), strict_order R /\ has_infinite_descent R)
  (* L4/well-foundedness yields anti-regress *)
  /\ (forall (U : Type) (R : U -> U -> Prop), well_founded R -> ~ has_infinite_descent R)
  (* the ToS hierarchy realizes both — a well-founded grounding order *)
  /\ well_founded level_lt.
Proof.
  split; [ | split; [ | split ] ].
  - intros U R SO. split; [ exact (order_asym R SO) | exact (order_no_mediated_cycle R SO) ].
  - exact order_does_not_give_anti_regress.
  - exact wf_no_infinite_descent.
  - exact level_lt_wf.
Qed.

Print Assumptions meta_pair_strength_capstone.
Print Assumptions tos_hierarchy_models_meta_pair.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  17 Qed, 0 Admitted, 0 axioms.                                             *)
(*  L5/Порядок (strict order) |- N (cycle-freedom); L4/ЗДО (well-founded)     *)
(*  |- anti-regress (finite descent); separated by (Z,<). Finite descent =    *)
(*  termination = Element/P4 side of H1; the ToS Level hierarchy is the       *)
(*  canonical well-founded model, with P1 = no_self_ground instance.          *)
(* ========================================================================= *)
