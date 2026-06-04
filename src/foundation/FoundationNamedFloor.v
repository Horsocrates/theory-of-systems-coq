(** * FoundationNamedFloor.v — closing the reflexive loop: FoundationAudit's vague `rides_on_model`
      verdicts on the SM structures are UPGRADED to the precise `rides_on_named_floor` (PositFloor),
      with the uniqueness bricks attached.

    FoundationAudit.v tagged the gauge group and the generation count `rides_on_model` — i.e.
    `0 < n_posited` (there IS some posit), VAGUE: one "Posited" flag standing for the whole
    interpretive content.  The posit-closing bricks (GaugePositReduction, GenerationsPositReduction,
    PositFloor) then EXHIBITED the named floor and proved the structures are uniquely derived from it.

    This file connects the two: the old single "Posited" flag RESOLVES to the explicit named floor
    (gauge_floor = {L1-no-repeat, L4-minimality, reflexive}; gen_floor = {L4-minimality}), and the
    new tier `audit_upgraded` = (old vague verdict) ∧ (exhibited named floor) ∧ (uniqueness brick).
    The new tier IMPLIES the old (`upgraded_implies_old`) — it is a strict REFINEMENT, not a
    replacement: FoundationAudit was right ("rides on a model"); we now say WHICH model, NAMED,
    COUNTED, and prove the derivation is unique.

    Net: the audit that EXPOSED the posits now references the PROVED named floor — the honesty loop
    is machine-linked end to end: audit verdict → named floor → uniqueness → framework {classic, P4}.

    (FoundationAudit's verdict records are replicated locally — with this citation — to stay
    self-contained; the upgrade applies identically to the originals.)

    Elements: the (replicated) audit verdicts; the exhibited named floors; the uniqueness bricks
    Roles:    the audit's single "Posited" flag resolves to the named floor; audit_upgraded = old ⊆ new
    Rules:    rides_on_model (old, vague) is refined to audit_upgraded (named floor + uniqueness), and
              the new implies the old

    ============ E/R/R разбор ============
      Rules (L5): старый rides_on_model уточняется до audit_upgraded (названный пол + единственность);
                  новый влечёт старый (уточнение, не замена).
      Roles (L4): флаг «Posited» аудита разрешается в названный пол; audit_upgraded = старое ⊆ новое.
      Elements  : вердикты аудита (реплика); экспонированные полы; кирпичи единственности.
    ДИАГНОСТИКА (P4): рефлексивная петля замкнута — аудит → названный пол → единственность → {classic,P4};
    честность уточнена с «едет на чём-то» до «едет РОВНО на этих названных, единственно».

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From ToS Require Import foundation.GaugePositReduction.        (* gauge_unique, primary_binary, ... *)
From ToS Require Import foundation.GenerationsPositReduction.   (* generations_unique, L4_minimal_generations *)
From ToS Require Import foundation.PositFloor.                  (* NamedPosit, sm_floor, gauge_floor, gen_floor, rides_on_named_floor *)

(* ===================================================================== *)
(*  FoundationAudit's verdicts (replicated; cite stdlib/FoundationAudit.v) *)
(* ===================================================================== *)

(* Replicated from stdlib/DerivationAudit.v: the provenance-audit skeleton. *)
Inductive Source := Structural | Indep | Posited | Target.
Record Audit := mkAudit { leaves : list Source; data_points : nat }.
Definition is_posited (s : Source) : bool := match s with Posited => true | _ => false end.
Definition n_posited (a : Audit) : nat := length (filter is_posited (leaves a)).
Definition rides_on_model (a : Audit) : Prop := (0 < n_posited a)%nat.

(* Replicated from stdlib/FoundationAudit.v: the gauge-group and generation verdicts. *)
Definition gauge_group_audit : Audit := mkAudit [Structural; Posited] 1.
Definition generation_count_audit : Audit := mkAudit [Structural; Posited; Indep] 1.

(** FoundationAudit's OLD verdicts: each rides on SOME model (vague — one Posited flag). *)
Lemma gauge_group_rides : rides_on_model gauge_group_audit.
Proof. unfold rides_on_model, gauge_group_audit, n_posited. simpl. lia. Qed.

Lemma generation_rides : rides_on_model generation_count_audit.
Proof. unfold rides_on_model, generation_count_audit, n_posited. simpl. lia. Qed.

(* ===================================================================== *)
(*  The upgraded tier: old verdict + exhibited named floor + uniqueness    *)
(* ===================================================================== *)

(** A structure's audit is UPGRADED when: its old `rides_on_model` holds, AND we EXHIBIT a named
    floor, AND the structure is uniquely derived from it.  Strictly refines `rides_on_model`. *)
Definition audit_upgraded (a : Audit) (floor : list NamedPosit) (uniqueness : Prop) : Prop :=
  rides_on_model a /\ rides_on_named_floor floor /\ uniqueness.

(** ★ The new tier IMPLIES the old: a refinement, not a replacement. *)
Lemma upgraded_implies_old (a : Audit) (floor : list NamedPosit) (P : Prop) :
  audit_upgraded a floor P -> rides_on_model a.
Proof. intros [H _]. exact H. Qed.

(** ★ The gauge group: old `rides_on_model` UPGRADED — rides on the named floor {L1NoRep,L4Min,
    Reflexive}, and [2,3,1] is uniquely derived from it (gauge_unique). *)
Theorem gauge_group_upgraded :
  audit_upgraded gauge_group_audit gauge_floor
    (forall f, primary_binary f -> L4_minimal_level1 f -> reflexive_terminal f -> decomp3 f = [2;3;1]).
Proof.
  split; [ exact gauge_group_rides | ].
  split; [ unfold rides_on_named_floor, gauge_floor; simpl; discriminate | ].
  exact gauge_unique.
Qed.

(** ★ The generation count: old `rides_on_model` UPGRADED — rides on the named floor {L4Min}, and
    "exactly 3" is uniquely derived from it (generations_unique). *)
Theorem generation_upgraded :
  audit_upgraded generation_count_audit gen_floor
    (forall gen, L4_minimal_generations gen -> gen = 3).
Proof.
  split; [ exact generation_rides | ].
  split; [ unfold rides_on_named_floor, gen_floor; simpl; discriminate | ].
  exact generations_unique.
Qed.

(** The audit's single "Posited" flag resolves to the 3 named structural principles. *)
Lemma posited_flag_resolves : length gauge_floor = 3 /\ n_posited gauge_group_audit = 1.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the reflexive loop closed                                    *)
(* ===================================================================== *)

(** The honesty loop, machine-linked:
      (old)       FoundationAudit tagged both structures `rides_on_model` (vague);
      (gauge)     UPGRADED to the named floor + unique [2,3,1] derivation;
      (gen)       UPGRADED to the named floor + unique "exactly 3";
      (total)     the whole structure's named floor is exhibited = {Classic,P4,L1NoRep,L4Min,Reflexive}.
    The audit that exposed the posits now references the proved named floor — end to end. *)
Theorem foundation_audit_named_floor :
  (rides_on_model gauge_group_audit /\ rides_on_model generation_count_audit)
  /\ audit_upgraded gauge_group_audit gauge_floor
       (forall f, primary_binary f -> L4_minimal_level1 f -> reflexive_terminal f -> decomp3 f = [2;3;1])
  /\ audit_upgraded generation_count_audit gen_floor
       (forall gen, L4_minimal_generations gen -> gen = 3)
  /\ sm_floor = [Classic; P4; L1NoRep; L4Min; Reflexive].
Proof.
  split; [ split; [ exact gauge_group_rides | exact generation_rides ] | ].
  split; [ exact gauge_group_upgraded | ].
  split; [ exact generation_upgraded | ].
  exact sm_floor_explicit.
Qed.
