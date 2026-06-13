(** * ERRBeingAndStatus.v — остаток §9.6 + §9.7: two prose markers of the ToS core given actual
      structure — the THREE LEVELS OF BEING (a presupposition ladder) and STATUS as a DERIVED concept.

    Two claims the core states only as prose / a True-marker are here made theorems.  Both are MODEST
    (the value is precision, not depth): they replace empty markers with real predicate structure.

    PART A — THREE LEVELS OF BEING (replaces Core_ERR's `three_levels_of_being := True`, lines 474-485).
      Existence (absolute) < Belonging (relational) < Functioning (active) — a LADDER of presupposition:
      functioning presupposes belonging (a role is only fulfilled by a member, the L5 order),
      belonging presupposes existence; and the levels are STRICTLY nested (an element can exist without
      belonging, belong without functioning).

    PART B — STATUS IS DERIVED (sharpens Roles.v §V "Status = Rule + Element, not a 4th primitive").
      status rule e := rule e.  Then: (1) status is determined by (rule, element); (2) it is NOT a new
      primitive — every status-assignment is realized by a rule; (3) it is RELATIONAL — the same
      element gets different statuses under different rules, so status is not a property of the element
      alone (it is Element + Rule).

    ============================== E/R/R разбор ==============================
    PART A (three levels of being):
      Rules (L5): functioning -> belonging (a role only on a member) -> existence; levels strictly
        nested.  Roles (L4): member = the membership criterion; role_filter = the role's filter; the
        three level-predicates.  Elements (L1+P4): an abstract carrier E; a concrete nat model
        (threshold >=1 member, >=2 functioning).  P4: the ladder is forced (functioning needs a member
        by the order); the levels are genuinely distinct (strict witnesses).  Honesty wall: existence
        is the absolute/bottom level (True by design, matching the prose "EXISTENCE (absolute)"); the
        content is the chain + strictness, not "being" as a phenomenon.
    PART B (status derived):
      Rules (L5): status is the result of a rule applied to an element.  Roles (L4): the rule = the
        status-assigner; the element = the substrate; the status = the output.  Elements (L1+P4): the
        carriers E, St; the rules.  P4: status carries no DOF beyond (rule, element); a status-pattern
        IS a rule (no new primitive); status is relational (element alone underdetermines it).
        Honesty wall: modest / near-definitional (status := rule e); the value is making "derived,
        not primitive" precise, not depth.
    0 axioms (both parts stdlib-only).

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.

(* ===================================================================== *)
(*  PART A — THREE LEVELS OF BEING                                         *)
(* ===================================================================== *)

Section ThreeLevels.

Variable E : Type.
Variable member : E -> Prop.        (* belongs: satisfies the system's criterion *)
Variable role_filter : E -> Prop.    (* functions: fulfills a role's filter *)
(* L5 order: a role can only be fulfilled by a member. *)
Hypothesis role_needs_member : forall e, role_filter e -> member e.

Definition being_exists (e : E) : Prop := True.            (* L1: absolute existence *)
Definition being_belongs (e : E) : Prop := member e.       (* L2: relational membership *)
Definition being_functions (e : E) : Prop := role_filter e. (* L3: active functioning *)

(** ★ Functioning presupposes belonging (a role is only fulfilled by a member). *)
Lemma functioning_presupposes_belonging : forall e, being_functions e -> being_belongs e.
Proof. intros e H. apply role_needs_member. exact H. Qed.

(** ★ Belonging presupposes existence. *)
Lemma belonging_presupposes_existence : forall e, being_belongs e -> being_exists e.
Proof. intros e _. exact I. Qed.

(** ★ The ladder: functioning => belonging => existence. *)
Lemma three_levels_chain : forall e,
  being_functions e -> being_belongs e /\ being_exists e.
Proof.
  intros e H. split.
  - apply functioning_presupposes_belonging. exact H.
  - exact I.
Qed.

End ThreeLevels.

(* A concrete model: candidates = nat, members = n >= 1, functioning = n >= 2. *)
Definition mem1 (n : nat) : Prop := (1 <= n)%nat.
Definition rol2 (n : nat) : Prop := (2 <= n)%nat.

(** ★ EXISTS but does not BELONG (0 exists, is not a member). *)
Lemma exists_not_belongs : being_exists nat 0 /\ ~ being_belongs nat mem1 0.
Proof. unfold being_exists, being_belongs, mem1. split; [ exact I | lia ]. Qed.

(** ★ BELONGS but does not FUNCTION (1 is a member, fulfills no role). *)
Lemma belongs_not_functions : being_belongs nat mem1 1 /\ ~ being_functions nat rol2 1.
Proof. unfold being_belongs, being_functions, mem1, rol2. split; lia. Qed.

(** ★ All three inhabited (2 functions, hence belongs, hence exists). *)
Lemma all_three_inhabited :
  being_functions nat rol2 2 /\ being_belongs nat mem1 2 /\ being_exists nat 2.
Proof.
  unfold being_functions, being_belongs, being_exists, mem1, rol2.
  split; [ lia | split; [ lia | exact I ] ].
Qed.

(** ★★★ THE THREE LEVELS OF BEING: a presupposition ladder (functioning => belonging => existence),
    strictly nested (exists-not-belongs, belongs-not-functions), all three inhabited.  Replaces the
    `three_levels_of_being := True` marker with real structure. *)
Theorem err_three_levels_of_being :
  (forall (E : Type) (member role_filter : E -> Prop),
     (forall e, role_filter e -> member e) ->
     forall e, being_functions E role_filter e -> being_belongs E member e /\ being_exists E e)
  /\ (being_exists nat 0 /\ ~ being_belongs nat mem1 0)
  /\ (being_belongs nat mem1 1 /\ ~ being_functions nat rol2 1)
  /\ (being_functions nat rol2 2 /\ being_belongs nat mem1 2 /\ being_exists nat 2).
Proof.
  split.
  - intros E member role_filter rnm e Hf. exact (three_levels_chain E member role_filter rnm e Hf).
  - split; [ exact exists_not_belongs
           | split; [ exact belongs_not_functions | exact all_three_inhabited ] ].
Qed.

(* ===================================================================== *)
(*  PART B — STATUS IS DERIVED (Rule + Element -> Status)                  *)
(* ===================================================================== *)

Section StatusTheory.

Variable E : Type.
Variable St : Type.

(** Status = the result of applying a rule to an element. *)
Definition status (rule : E -> St) (e : E) : St := rule e.

(** ★ Status is DETERMINED by (rule, element): same rule + same element => same status. *)
Lemma status_determined : forall (r1 r2 : E -> St) (e1 e2 : E),
  r1 = r2 -> e1 = e2 -> status r1 e1 = status r2 e2.
Proof. intros r1 r2 e1 e2 Hr He. subst. reflexivity. Qed.

(** ★ Status is NOT a new primitive: every status-assignment is realized by a rule. *)
Lemma status_realizable : forall (assign : E -> St),
  exists rule, forall e, status rule e = assign e.
Proof. intro assign. exists assign. intro e. reflexivity. Qed.

End StatusTheory.

(** ★★ Status is RELATIONAL: the same element gets DIFFERENT statuses under different rules — so
    status is not a property of the element alone; it is Element + Rule. *)
Lemma status_needs_rule :
  exists (E St : Type) (e : E) (r1 r2 : E -> St), status E St r1 e <> status E St r2 e.
Proof.
  exists bool, bool, true, (fun _ => true), (fun _ => false).
  cbn. discriminate.
Qed.

(** ★★★ STATUS IS DERIVED, not a fourth primitive: determined by (rule, element)
    (status_determined), realizable by a rule (status_realizable, no new primitive), and relational
    (status_needs_rule, the element alone does not fix it).  Sharpens "Status = Rule + Element". *)
Theorem err_status_derived :
  (forall (E St : Type) (r1 r2 : E -> St) (e1 e2 : E),
     r1 = r2 -> e1 = e2 -> status E St r1 e1 = status E St r2 e2)
  /\ (forall (E St : Type) (assign : E -> St), exists rule, forall e, status E St rule e = assign e)
  /\ (exists (E St : Type) (e : E) (r1 r2 : E -> St), status E St r1 e <> status E St r2 e).
Proof.
  split; [ exact status_determined | ].
  split; [ exact status_realizable | exact status_needs_rule ].
Qed.

Print Assumptions err_three_levels_of_being.
Print Assumptions err_status_derived.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  PART A (§9.6): the THREE LEVELS OF BEING as a presupposition ladder        *)
(*  (functioning_presupposes_belonging / belonging_presupposes_existence /     *)
(*  three_levels_chain), strictly nested (exists_not_belongs,                   *)
(*  belongs_not_functions, all_three_inhabited).  Replaces                      *)
(*  `three_levels_of_being := True`.  PART B (§9.7): STATUS is DERIVED          *)
(*  (status := rule e): determined by (rule,element) (status_determined), not   *)
(*  a new primitive (status_realizable), relational (status_needs_rule).        *)
(*  Sharpens Roles.v §V.  HONEST: both modest (the value is precision) — the    *)
(*  ladder + strictness, and "derived not primitive" made exact.  Closes the    *)
(*  small/interpretive tail of the §9 agenda.                                  *)
(* ========================================================================= *)
