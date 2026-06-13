(** * KnowledgeInteractionResolution.v — what is STRUCTURALLY forced about determinacy vs
      potentiality: the flat-domain resolution skeleton (deepening of KnowledgeInteraction's honest
      "structural only, not a QM derivation")

    Direction C (honest deepening).  KnowledgeInteraction.v modeled the boundary status as option bool
    (None = potential / "not yet either", Some b = a determinate trace value), proved the trace is
    append-only and "potential is not both", and STOPPED honestly: structural only, not a QM
    derivation.  That stop can be SHARPENED by SAYING what the structure IS: determinacy/potentiality
    is exactly the FLAT-DOMAIN resolution skeleton.

      potential = BOTTOM       — None is below every status (it can still resolve);
      determinate = MAXIMAL     — Some b is fixed (nothing strictly above it; further interaction
                                  cannot move it);
      resolution = MONOTONE     — a status process only rises in the information order leq; the value,
                                  once committed, never changes (at most one bit ever commits);
      no "both"                 — the carrier option bool has no "both" constructor; true and false
                                  have NO common upper bound, so no status is "both" — potentiality is
                                  NOT a contradiction, by the carrier, not by physics;
      frame underdetermines rule— two different monotone resolution RULES act on the SAME frame; the
                                  flat domain does not fix the rule (the physics).

    What stays behind the wall (sharper): the RULE — which potential resolves to which value, with
    what statistics (Born |psi|^2, the dynamics) — is physics, cited (MeasurementProcess.v /
    BornRule.v), not appropriated.  Only the FRAME (the flat-domain resolution) is structural.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) potential = bottom (None below all), determinate = maximal (Some b fixed);
      (2) resolution is MONOTONE (the status never falls; the committed value never changes);
      (3) the carrier option bool forbids "both" — potentiality is not a contradiction;
      (4) the frame (flat domain) does NOT fix the resolution rule (physics).
    Roles (L4): None = bottom / potential; Some b = maximal / determinate; leq = the information
      order (flat domain); resolution = the monotone rise; the rule = physics.
    Elements (L1+P4): the status carrier (option bool); the status process (status over steps); the
      resolution rule.
    P4 diagnostic (could it be otherwise?):
      The determinacy/potentiality FRAME is forced (flat domain: bottom/maximal, monotone resolution,
      at most one value, no "both"); the RULE (which potential -> which value, the statistics) is
      FREE (physics).  Sharpens KnowledgeInteraction's "structural only": now it is SAID what is
      structural (the flat-domain resolution), and the wall (rule = physics) is sharp.  "Both" is
      impossible by the carrier, not by QM; determinacy = a fixed point of interaction.
    Honesty wall:
      the resolution RULE (Born / dynamics) is physics — cited (MeasurementProcess.v / BornRule.v),
      not appropriated; only the flat-domain frame is structural.  option bool is the structural
      proxy for "potential / determinate-true / determinate-false".

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool.

(** The information order on the status carrier (flat domain): None below everything; a determinate
    value below only itself. *)
Definition leq (x y : option bool) : Prop :=
  match x with None => True | Some b => y = Some b end.

(* ===================================================================== *)
(*  PART I — leq is a partial order; bottom / maximal                       *)
(* ===================================================================== *)

Lemma leq_refl : forall x, leq x x.
Proof. intro x. destruct x as [b|]; [ reflexivity | exact I ]. Qed.

Lemma leq_trans : forall x y z, leq x y -> leq y z -> leq x z.
Proof.
  intros x y z Hxy Hyz. destruct x as [b|]; simpl in *.
  - subst y. exact Hyz.
  - exact I.
Qed.

Lemma leq_antisym : forall x y, leq x y -> leq y x -> x = y.
Proof.
  intros x y Hxy Hyx. destruct x as [b|]; destruct y as [c|]; simpl in *.
  - congruence.
  - discriminate Hxy.
  - discriminate Hyx.
  - reflexivity.
Qed.

(** ★ Potential is the BOTTOM: None can still resolve to anything. *)
Lemma none_bottom : forall x, leq None x.
Proof. intro x. exact I. Qed.

(** ★ Determinate is MAXIMAL / fixed: nothing is strictly above Some b — further interaction cannot
    move a committed value. *)
Lemma some_maximal : forall b x, leq (Some b) x -> x = Some b.
Proof. intros b x H. exact H. Qed.

(* ===================================================================== *)
(*  PART II — resolution is monotone; at most one value commits            *)
(* ===================================================================== *)

(** A resolution = a status process that only rises in the information order. *)
Definition resolution (s : nat -> option bool) : Prop := forall n, leq (s n) (s (S n)).

(** ★ Once determinate, it stays — the committed value persists (R5 on the boundary, sharpened to
    the whole process). *)
Theorem determinate_stays : forall s, resolution s ->
  forall n b, s n = Some b -> forall m, (n <= m)%nat -> s m = Some b.
Proof.
  intros s Hres n b Hn m Hm. induction Hm as [|m Hm IH].
  - exact Hn.
  - pose proof (Hres m) as Hstep. rewrite IH in Hstep. simpl in Hstep. exact Hstep.
Qed.

(** ★★ At most one value ever commits: a monotone resolution cannot present two different determinate
    values.  (The committed bit is unique.) *)
Theorem at_most_one_value : forall s, resolution s ->
  forall n m b c, s n = Some b -> s m = Some c -> b = c.
Proof.
  intros s Hres n m b c Hn Hm. destruct (Nat.le_ge_cases n m) as [H|H].
  - pose proof (determinate_stays s Hres n b Hn m H) as Hb. congruence.
  - pose proof (determinate_stays s Hres m c Hm n H) as Hc. congruence.
Qed.

(* ===================================================================== *)
(*  PART III — no "both"; potential can resolve; frame underdetermines rule *)
(* ===================================================================== *)

(** ★★ No "both": true and false have NO common upper bound — no status is "both true and false".
    Potentiality is therefore NOT a contradiction; it is None (not-yet-either).  Forced by the
    carrier (option bool has no "both"), not by physics. *)
Theorem no_both : ~ exists x, leq (Some true) x /\ leq (Some false) x.
Proof. intros [x [H1 H2]]. simpl in H1, H2. congruence. Qed.

(** ★ Potential can resolve EITHER way: None is below both determinate values. *)
Theorem potential_can_resolve : leq None (Some true) /\ leq None (Some false).
Proof. split; exact I. Qed.

(** ★★ The FRAME underdetermines the RULE: two distinct monotone resolution rules act on the SAME
    flat-domain frame — the structure does not pick which potential resolves to which value (that is
    physics).  (Sharpens KnowledgeInteraction.determinacy_underdetermines_rules.) *)
Theorem frame_underdetermines_rule :
  exists (r1 r2 : option bool -> option bool),
    (forall x, leq x (r1 x)) /\ (forall x, leq x (r2 x)) /\ r1 None <> r2 None.
Proof.
  exists (fun x => match x with None => Some true  | Some b => Some b end),
         (fun x => match x with None => Some false | Some b => Some b end).
  split; [ | split ].
  - intro x. destruct x as [b|]; simpl; [ reflexivity | exact I ].
  - intro x. destruct x as [b|]; simpl; [ reflexivity | exact I ].
  - simpl. discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The determinacy/potentiality FRAME is the flat-domain resolution skeleton: potential =
    bottom, determinate = maximal/fixed, at most one value commits, no "both"; and the frame
    underdetermines the rule (physics).  Structural skeleton derived; the resolution RULE is free. *)
Theorem determinacy_potentiality_capstone :
  (forall x, leq None x)
  /\ (forall b x, leq (Some b) x -> x = Some b)
  /\ (forall s, resolution s -> forall n m b c, s n = Some b -> s m = Some c -> b = c)
  /\ (~ exists x, leq (Some true) x /\ leq (Some false) x)
  /\ (exists r1 r2 : option bool -> option bool,
        (forall x, leq x (r1 x)) /\ (forall x, leq x (r2 x)) /\ r1 None <> r2 None).
Proof.
  split; [ exact none_bottom | ].
  split; [ exact some_maximal | ].
  split; [ exact at_most_one_value | ].
  split; [ exact no_both | exact frame_underdetermines_rule ].
Qed.

Print Assumptions determinacy_potentiality_capstone.
Print Assumptions at_most_one_value.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Determinacy/potentiality = the FLAT-DOMAIN resolution skeleton: leq is a  *)
(*  partial order (leq_refl/trans/antisym), potential = bottom (none_bottom), *)
(*  determinate = maximal/fixed (some_maximal); a monotone resolution keeps   *)
(*  the value (determinate_stays) and commits at most one (at_most_one_value);*)
(*  "both" is impossible by the carrier (no_both); the frame underdetermines  *)
(*  the rule (frame_underdetermines_rule).  Deepens KnowledgeInteraction's    *)
(*  "structural only, not a QM derivation": it now SAYS what is structural     *)
(*  (the flat-domain resolution) and the wall (rule = physics, Born/dynamics  *)
(*  cited) is sharp.  "Both" is forbidden by the carrier, not by QM.         *)
(* ========================================================================= *)
