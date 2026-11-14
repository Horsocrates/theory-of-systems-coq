(** * StructuralPath.v — The structural path: the first position, the first
      candidate, the gate and the weight

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.5, places 5.1-5.4 and footnotes 2-3, 2026-11-14):

    Elements: the positions of a structured system (Position := nat) and the
              elements placed at them; entities with gate signals and scores
              (ERRProcess.v).
    Roles:    the first occupied position; the number of a position, counted
              from one; a candidate for a role — a position whose element
              passes the check; the weight of an entity; the primary — the
              first by weight.
    Rules:    L5 — an element stands at one position; resolution takes the
              least position among the candidates; the gate decides the
              status; the weight orders the admitted.
    Proved:   (1) a non-empty structured system has exactly one first
                  occupied position; in a normalized system its number is 1,
                  without normalization it may be other; the numbers of
                  positions are exactly the positive numbers; induction from
                  one;
              (2) resolve_role returns the least of the candidates AND the
                  default, so it may miss; when the default is not less than
                  some candidate, the result is the FIRST CANDIDATE — from
                  the list, occupied by an element that passes the check,
                  not greater than any other candidate; the variant without
                  a default (resolve_role_opt) needs no condition;
              (3) in process_entity the status is decided by the gate; a
                  positive weight implies admission; with the domain number
                  at least 1 admission is EQUIVALENT to a positive weight;
              (4) a role with a numeric requirement (a measure and a
                  threshold): the chosen position is occupied by an element
                  that reaches the threshold and is the first among such;
              (5) find_primary returns an admitted entity of the list with
                  the greatest weight, among the equal — the earliest
                  created; it exists as soon as one entity is admitted.
    P4 diagnostic ("could it be otherwise?"): finite lists and positions
              only. Forced: (1)-(5). NOT claimed: that Position is derived —
              Position := nat is a technical record; that process_entity
              takes a role as an argument — it does not; that selection by
              weight (StatusFromERR.v) and selection by position (Roles.v)
              are one mechanism — they stay two files, (4) is a new record
              that joins a measure with resolution by position; the status
              HistoricalMax is assigned by no function.

    STATUS: 43 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import List PeanoNat Lia Bool.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import Roles.
From ToS Require Import L5Resolution.
From ToS Require Import foundation.ERRProcess.
From ToS Require Import foundation.StatusFromERR.

Local Open Scope nat_scope.

(* ========================================================================= *)
(*  1. EXAMPLES: AN EMPTY AND A SPARSE STRUCTURED SYSTEM                     *)
(* ========================================================================= *)

Definition empty_ss : StructuredSystem L2.
Proof.
  refine (mkStructuredSystem L2 example_nat_system (fun _ => None) _).
  intros p1 p2 e H. discriminate H.
Defined.

Lemma empty_ss_no_position : forall p, ~ position_occupied empty_ss p.
Proof. intros p [e H]. discriminate H. Qed.

Definition sparse_ss : StructuredSystem L2.
Proof.
  refine (mkStructuredSystem L2 example_nat_system
            (fun p => if Nat.eqb p 5 then Some 7 else None) _).
  intros p1 p2 e H1 H2.
  destruct (Nat.eqb p1 5) eqn:E1; [ | discriminate H1].
  destruct (Nat.eqb p2 5) eqn:E2; [ | discriminate H2].
  apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2. congruence.
Defined.

Lemma sparse_ss_only_5 : forall p, position_occupied sparse_ss p <-> p = 5.
Proof.
  intro p. unfold position_occupied. simpl. split.
  - intros [e H]. destruct (Nat.eqb p 5) eqn:E; [ | discriminate H].
    apply Nat.eqb_eq in E. exact E.
  - intro H. subst p. exists 7. reflexivity.
Qed.

(** The second side of uniqueness: a position carries at most one element. *)
Lemma one_position_one_element :
  forall (L : Level) (S : StructuredSystem L) p e1 e2,
    ss_assignment L S p = Some e1 -> ss_assignment L S p = Some e2 -> e1 = e2.
Proof. intros L S p e1 e2 H1 H2. rewrite H1 in H2. injection H2. auto. Qed.

(* ========================================================================= *)
(*  2. THE FIRST OCCUPIED POSITION; NUMBERS OF POSITIONS FROM ONE            *)
(* ========================================================================= *)

Definition nonempty_structured {L : Level} (S : StructuredSystem L) : Prop :=
  exists p, position_occupied S p.

Definition first_occupied_position {L : Level} (S : StructuredSystem L) (p : Position) : Prop :=
  position_occupied S p /\ forall q, position_occupied S q -> p <= q.

Lemma position_occupied_dec :
  forall (L : Level) (S : StructuredSystem L) (p : Position),
    {position_occupied S p} + {~ position_occupied S p}.
Proof.
  intros L S p. unfold position_occupied.
  destruct (ss_assignment L S p) as [e | ].
  - left. exists e. reflexivity.
  - right. intros [e H]. discriminate H.
Qed.

Lemma first_occupied_search :
  forall (L : Level) (S : StructuredSystem L) (n : nat),
    (forall q, q < n -> ~ position_occupied S q) \/
    (exists p, first_occupied_position S p).
Proof.
  intros L S n. induction n as [ | n IH].
  - left. intros q Hq. lia.
  - destruct IH as [Hfree | Hfound].
    + destruct (position_occupied_dec L S n) as [Hocc | Hno].
      * right. exists n. split; [exact Hocc | ].
        intros q Hq. destruct (Nat.lt_ge_cases q n) as [Hlt | Hge]; [ | exact Hge].
        exfalso. exact (Hfree q Hlt Hq).
      * left. intros q Hq Hocc.
        destruct (Nat.eq_dec q n) as [Heq | Hne].
        -- subst q. exact (Hno Hocc).
        -- apply (Hfree q); [lia | exact Hocc].
    + right. exact Hfound.
Qed.

(** Every non-empty structured system has a first occupied position. *)
Theorem nonempty_has_first_position :
  forall (L : Level) (S : StructuredSystem L),
    nonempty_structured S -> exists p, first_occupied_position S p.
Proof.
  intros L S [p0 Hp0].
  destruct (first_occupied_search L S (Datatypes.S p0)) as [Hfree | Hfound].
  - exfalso. apply (Hfree p0); [lia | exact Hp0].
  - exact Hfound.
Qed.

Theorem first_occupied_position_unique :
  forall (L : Level) (S : StructuredSystem L) p q,
    first_occupied_position S p -> first_occupied_position S q -> p = q.
Proof.
  intros L S p q [Hp Hpmin] [Hq Hqmin].
  pose proof (Hpmin q Hq). pose proof (Hqmin p Hp). lia.
Qed.

Theorem empty_has_no_first : forall p, ~ first_occupied_position empty_ss p.
Proof. intros p [H _]. exact (empty_ss_no_position p H). Qed.

(** A first occupied position exists exactly when the system is non-empty. *)
Theorem first_position_iff_nonempty :
  forall (L : Level) (S : StructuredSystem L),
    nonempty_structured S <-> exists p, first_occupied_position S p.
Proof.
  intros L S. split.
  - apply nonempty_has_first_position.
  - intros [p [Hp _]]. exists p. exact Hp.
Qed.

(** A normalized presentation: the occupied positions form an initial segment. *)
Definition normalized {L : Level} (S : StructuredSystem L) : Prop :=
  forall p q, q <= p -> position_occupied S p -> position_occupied S q.

(** The number of a position, counted from one. *)
Definition pos_number (p : Position) : nat := Datatypes.S p.

Theorem normalized_first_is_zero :
  forall (L : Level) (S : StructuredSystem L),
    normalized S -> nonempty_structured S -> first_occupied_position S 0.
Proof.
  intros L S Hn [p Hp]. split.
  - apply (Hn p 0); [lia | exact Hp].
  - intros q _. lia.
Qed.

(** In a normalized non-empty system the first position has the number 1. *)
Theorem normalized_first_number_one :
  forall (L : Level) (S : StructuredSystem L),
    normalized S -> nonempty_structured S ->
    exists p, first_occupied_position S p /\ pos_number p = 1.
Proof.
  intros L S Hn Hne. exists 0. split.
  - apply normalized_first_is_zero; assumption.
  - reflexivity.
Qed.

(** Without normalization the number of the first occupied position may be other: here 6. *)
Lemma sparse_first_is_5 : first_occupied_position sparse_ss 5 /\ pos_number 5 = 6.
Proof.
  split; [ | reflexivity]. split.
  - apply sparse_ss_only_5. reflexivity.
  - intros q Hq. apply sparse_ss_only_5 in Hq. lia.
Qed.

Lemma sparse_not_normalized : ~ normalized sparse_ss.
Proof.
  intro Hn.
  assert (H5 : position_occupied sparse_ss 5) by (apply sparse_ss_only_5; reflexivity).
  pose proof (Hn 5 0 (Nat.le_0_l 5) H5) as H0.
  apply sparse_ss_only_5 in H0. discriminate H0.
Qed.

Lemma pos_number_examples : pos_number 0 = 1 /\ pos_number 1 = 2.
Proof. split; reflexivity. Qed.

Lemma pos_number_positive : forall p, 1 <= pos_number p.
Proof. intro p. unfold pos_number. lia. Qed.

Lemma pos_number_onto_positive : forall n, 1 <= n -> exists p, pos_number p = n.
Proof. intros n Hn. exists (n - 1). unfold pos_number. lia. Qed.

Lemma pos_number_injective : forall p q, pos_number p = pos_number q -> p = q.
Proof. intros p q H. unfold pos_number in H. lia. Qed.

Definition position_ind :
  forall P : Position -> Prop,
    P 0 -> (forall p, P p -> P (Datatypes.S p)) -> forall p, P p := nat_ind.

(** Induction over the numbers of positions, with the base 1. *)
Lemma number_ind_from_one :
  forall P : nat -> Prop,
    P 1 -> (forall n, 1 <= n -> P n -> P (Datatypes.S n)) -> forall n, 1 <= n -> P n.
Proof.
  intros P H1 Hstep n Hn.
  destruct (pos_number_onto_positive n Hn) as [p Hp]. subst n.
  induction p as [ | p IH] using position_ind.
  - exact H1.
  - apply (Hstep (pos_number p)); [apply pos_number_positive | ].
    apply IH. apply pos_number_positive.
Qed.

(* ========================================================================= *)
(*  3. RESOLUTION BY POSITION: WHEN THE RESULT IS THE FIRST CANDIDATE        *)
(* ========================================================================= *)

(** The result of L5_resolve may be no candidate: the default is less than every candidate. *)
Lemma L5_resolve_may_miss : L5_resolve [5; 7] 0 = 0 /\ ~ In 0 [5; 7].
Proof.
  split; [reflexivity | ].
  simpl. intros [H | [H | H]]; try discriminate H; exact H.
Qed.

Lemma resolve_role_may_miss :
  resolve_role L2 sparse_ss (fun _ => true) [5] 0 = 0 /\
  role_candidates L2 sparse_ss (fun _ => true) [5] = [5] /\
  ~ position_occupied sparse_ss 0.
Proof.
  split; [reflexivity | split; [reflexivity | ] ].
  intro H. apply sparse_ss_only_5 in H. discriminate H.
Qed.

(** The result is a candidate or the default itself. *)
Lemma L5_resolve_in_or_default :
  forall (cs : list Position) (d : Position),
    In (L5_resolve cs d) cs \/ L5_resolve cs d = d.
Proof.
  intros cs d. unfold L5_resolve. induction cs as [ | a cs IH]; simpl.
  - right. reflexivity.
  - destruct (Nat.min_dec a (fold_right Nat.min d cs)) as [H | H]; rewrite H.
    + left. left. reflexivity.
    + destruct IH as [IH | IH].
      * left. right. exact IH.
      * right. exact IH.
Qed.

(** If the default is not less than some candidate, the result IS a candidate. *)
Lemma L5_resolve_in :
  forall (cs : list Position) (d : Position),
    (exists p, In p cs /\ p <= d) -> In (L5_resolve cs d) cs.
Proof.
  intros cs d [p [Hin Hle]].
  destruct (L5_resolve_in_or_default cs d) as [H | H]; [exact H | ].
  assert (Hne : cs <> nil) by (intro E; subst cs; exact Hin).
  pose proof (L5_resolve_le_all cs d Hne p Hin) as Hmin.
  assert (Heq : L5_resolve cs d = p) by lia.
  rewrite Heq. exact Hin.
Qed.

(** resolve_role chooses the FIRST candidate — under the named condition on the default:
    the chosen position is from the list, is occupied by an element that passes the
    check, and is not greater than any other candidate. *)
Theorem resolve_role_first_candidate :
  forall (L : Level) (S : StructuredSystem L)
         (decide : crit_domain L (sys_criterion L (ss_base L S)) -> bool)
         (positions : list Position) (default : Position),
    (exists p, In p (role_candidates L S decide positions) /\ p <= default) ->
    In (resolve_role L S decide positions default) positions /\
    (exists e, ss_assignment L S (resolve_role L S decide positions default) = Some e
               /\ decide e = true) /\
    (forall q, In q (role_candidates L S decide positions) ->
               resolve_role L S decide positions default <= q).
Proof.
  intros L S decide positions default Hex.
  assert (Hne : role_candidates L S decide positions <> nil).
  { destruct Hex as [p [Hin _]]. intro E. rewrite E in Hin. exact Hin. }
  pose proof (L5_resolve_in (role_candidates L S decide positions) default Hex) as Hin.
  fold (resolve_role L S decide positions default) in Hin.
  unfold role_candidates in Hin at 1. apply filter_In in Hin. destruct Hin as [Hpos Hdec].
  split; [exact Hpos | split].
  - destruct (ss_assignment L S (resolve_role L S decide positions default)) as [e | ].
    + exists e. split; [reflexivity | exact Hdec].
    + discriminate Hdec.
  - intros q Hq. apply resolve_role_le_all_candidates; assumption.
Qed.

(** It suffices to take one of the candidates as the default. *)
Corollary resolve_role_default_candidate :
  forall (L : Level) (S : StructuredSystem L) decide positions default,
    In default (role_candidates L S decide positions) ->
    In (resolve_role L S decide positions default) (role_candidates L S decide positions).
Proof.
  intros L S decide positions default Hin.
  unfold resolve_role. apply L5_resolve_in. exists default. split; [exact Hin | lia].
Qed.

(* ========================================================================= *)
(*  4. THE GATE DECIDES THE STATUS; A ROLE WITH A NUMERIC REQUIREMENT        *)
(* ========================================================================= *)

(** The status of process_entity is computed from the gate; the weight does not enter it. *)
Lemma process_entity_status_by_gate :
  forall id lg sig sc,
    ent_status (process_entity id lg sig sc) =
    (if gate_valid (compute_gate sig) then Candidate else Invalid).
Proof. reflexivity. Qed.

Lemma process_entity_two_statuses :
  forall id lg sig sc,
    ent_status (process_entity id lg sig sc) = Candidate \/
    ent_status (process_entity id lg sig sc) = Invalid.
Proof.
  intros. rewrite process_entity_status_by_gate.
  destruct (gate_valid (compute_gate sig)); [left | right]; reflexivity.
Qed.

Lemma process_entity_invalid_weight_zero :
  forall id lg sig sc,
    ent_status (process_entity id lg sig sc) = Invalid ->
    ent_weight (process_entity id lg sig sc) = 0.
Proof.
  intros id lg sig sc H. rewrite process_entity_status_by_gate in H.
  simpl. apply zero_gate_law.
  destruct (gate_valid (compute_gate sig)); [discriminate H | reflexivity].
Qed.

Lemma process_entity_positive_weight_candidate :
  forall id lg sig sc,
    0 < ent_weight (process_entity id lg sig sc) ->
    ent_status (process_entity id lg sig sc) = Candidate.
Proof.
  intros id lg sig sc H.
  destruct (process_entity_two_statuses id lg sig sc) as [Hc | Hi]; [exact Hc | ].
  apply process_entity_invalid_weight_zero in Hi. lia.
Qed.

(** The converse fails without a condition: the gate is passed, the weight is zero. *)
Lemma candidate_with_zero_weight :
  ent_status (process_entity 0 0 valid_signals (mkRS 0 0 0)) = Candidate /\
  ent_weight (process_entity 0 0 valid_signals (mkRS 0 0 0)) = 0.
Proof. split; reflexivity. Qed.

(** The status is not a function of the weight: equal weights, different statuses. *)
Lemma status_not_determined_by_weight :
  ent_weight (process_entity 0 0 valid_signals (mkRS 0 0 0)) =
  ent_weight (process_entity 1 1 invalid_signals (mkRS 8 7 3)) /\
  ent_status (process_entity 0 0 valid_signals (mkRS 0 0 0)) <>
  ent_status (process_entity 1 1 invalid_signals (mkRS 8 7 3)).
Proof. split; [reflexivity | discriminate]. Qed.

Lemma weight_formula :
  forall s d k g, gate_valid g = true ->
    compute_weight (mkRS s d k) g = s + k * 10 + d.
Proof. intros s d k g H. unfold compute_weight. rewrite H. reflexivity. Qed.

(** With the domain number at least 1 (in ERRProcess.v: D1-D6 = 1-6) an entity is admitted
    exactly when its weight is positive: then "the weight decides". *)
Theorem candidate_iff_positive_weight :
  forall id lg sig sc, 1 <= rs_current_domain sc ->
    (ent_status (process_entity id lg sig sc) = Candidate <->
     0 < ent_weight (process_entity id lg sig sc)).
Proof.
  intros id lg sig sc Hd. split.
  - intro H. rewrite process_entity_status_by_gate in H. simpl. unfold compute_weight.
    destruct (gate_valid (compute_gate sig)); [lia | discriminate H].
  - apply process_entity_positive_weight_candidate.
Qed.

(** A role with a numeric requirement: a measure decides whether an element fits; among
    the fitting ones the first is taken by the order of positions. The number takes part
    twice — as the measure and as the position. *)
Section MeasuredRole.
  Variable L : Level.
  Variable S : StructuredSystem L.
  Variable measure : crit_domain L (sys_criterion L (ss_base L S)) -> nat.
  Variable threshold : nat.

  Definition fits (e : crit_domain L (sys_criterion L (ss_base L S))) : bool :=
    threshold <=? measure e.

  Theorem measured_role_first :
    forall (positions : list Position) (default : Position),
      (exists p, In p (role_candidates L S fits positions) /\ p <= default) ->
      exists e,
        ss_assignment L S (resolve_role L S fits positions default) = Some e /\
        threshold <= measure e /\
        (forall q e', In q positions -> ss_assignment L S q = Some e' ->
                      threshold <= measure e' ->
                      resolve_role L S fits positions default <= q).
  Proof.
    intros positions default Hex.
    destruct (resolve_role_first_candidate L S fits positions default Hex)
      as [_ [[e [He Hfit]] Hmin]].
    exists e. split; [exact He | split].
    - unfold fits in Hfit. apply Nat.leb_le in Hfit. exact Hfit.
    - intros q e' Hq He' Hm. apply Hmin.
      unfold role_candidates. apply filter_In. split; [exact Hq | ].
      rewrite He'. unfold fits. apply Nat.leb_le. exact Hm.
  Qed.
End MeasuredRole.

(* ========================================================================= *)
(*  5. SELECTION BY WEIGHT: WHAT find_primary RETURNS                        *)
(* ========================================================================= *)

Lemma compare_entities_true :
  forall e b, compare_entities e b = true ->
    ent_weight b < ent_weight e \/
    (ent_weight e = ent_weight b /\ ent_legacy_idx e <= ent_legacy_idx b).
Proof.
  intros e b H. unfold compare_entities in H.
  destruct (ent_weight b <? ent_weight e) eqn:E1.
  - left. apply Nat.ltb_lt. exact E1.
  - apply Nat.ltb_ge in E1.
    destruct (ent_weight e <? ent_weight b) eqn:E2; [discriminate H | ].
    apply Nat.ltb_ge in E2. apply Nat.leb_le in H. right. split; lia.
Qed.

Lemma compare_entities_false :
  forall e b, compare_entities e b = false ->
    ent_weight e < ent_weight b \/
    (ent_weight e = ent_weight b /\ ent_legacy_idx b < ent_legacy_idx e).
Proof.
  intros e b H. unfold compare_entities in H.
  destruct (ent_weight b <? ent_weight e) eqn:E1; [discriminate H | ].
  apply Nat.ltb_ge in E1.
  destruct (ent_weight e <? ent_weight b) eqn:E2.
  - left. apply Nat.ltb_lt. exact E2.
  - apply Nat.ltb_ge in E2. apply Nat.leb_gt in H. right. split; lia.
Qed.

(** The general law: find_primary returns an entity of the list admitted by the gate, with
    the greatest weight, and among the equal in weight — the earliest created. *)
Theorem find_primary_spec :
  forall (es : list ERREntity) (p : ERREntity),
    find_primary es = Some p ->
    In p es /\ gate_valid (ent_gate p) = true /\
    (forall e, In e es -> gate_valid (ent_gate e) = true ->
       ent_weight e < ent_weight p \/
       (ent_weight e = ent_weight p /\ ent_legacy_idx p <= ent_legacy_idx e)).
Proof.
  induction es as [ | a rest IH]; intros p H; simpl in H.
  - discriminate H.
  - destruct (find_primary rest) as [best | ] eqn:Hrest.
    + specialize (IH best eq_refl). destruct IH as [Hin [Hgate Hmax]].
      destruct (gate_valid (ent_gate a)) eqn:Ga.
      * destruct (compare_entities a best) eqn:Hc; injection H as H; subst p.
        -- apply compare_entities_true in Hc.
           split; [left; reflexivity | split; [exact Ga | ] ].
           intros e [He | He] Ge.
           ++ subst e. right. split; lia.
           ++ destruct (Hmax e He Ge) as [Hlt | [Heq Hle]]; destruct Hc as [Hc | [Hc1 Hc2]].
              ** left. lia.
              ** left. lia.
              ** left. lia.
              ** right. split; lia.
        -- apply compare_entities_false in Hc.
           split; [right; exact Hin | split; [exact Hgate | ] ].
           intros e [He | He] Ge.
           ++ subst e. destruct Hc as [Hc | [Hc1 Hc2]]; [left; exact Hc | right; split; lia].
           ++ exact (Hmax e He Ge).
      * injection H as H; subst p.
        split; [right; exact Hin | split; [exact Hgate | ] ].
        intros e [He | He] Ge.
        -- subst e. rewrite Ga in Ge. discriminate Ge.
        -- exact (Hmax e He Ge).
    + destruct (gate_valid (ent_gate a)) eqn:Ga; [ | discriminate H].
      injection H as H; subst p.
      split; [left; reflexivity | split; [exact Ga | ] ].
      intros e [He | He] Ge.
      * subst e. right. split; lia.
      * exfalso. clear IH.
        revert e He Ge Hrest. induction rest as [ | b rest' IH']; intros e He Ge Hrest.
        -- exact He.
        -- simpl in Hrest. destruct (find_primary rest') as [best' | ] eqn:Hr'.
           ++ destruct (gate_valid (ent_gate b)); [ | discriminate Hrest].
              destruct (compare_entities b best'); discriminate Hrest.
           ++ destruct (gate_valid (ent_gate b)) eqn:Gb; [discriminate Hrest | ].
              destruct He as [He | He].
              ** subst e. rewrite Gb in Ge. discriminate Ge.
              ** exact (IH' e He Ge eq_refl).
Qed.

Corollary find_primary_max_weight :
  forall es p, find_primary es = Some p ->
    forall e, In e es -> gate_valid (ent_gate e) = true -> ent_weight e <= ent_weight p.
Proof.
  intros es p H e He Ge.
  destruct (find_primary_spec es p H) as [_ [_ Hmax]].
  destruct (Hmax e He Ge) as [Hlt | [Heq _]]; lia.
Qed.

Lemma find_primary_none :
  forall es, find_primary es = None ->
    forall e, In e es -> gate_valid (ent_gate e) = false.
Proof.
  induction es as [ | a rest IH]; intros H e He.
  - destruct He.
  - simpl in H. destruct (find_primary rest) as [best | ] eqn:Hr.
    + destruct (gate_valid (ent_gate a)); [ | discriminate H].
      destruct (compare_entities a best); discriminate H.
    + destruct (gate_valid (ent_gate a)) eqn:Ga; [discriminate H | ].
      destruct He as [He | He]; [subst e; exact Ga | exact (IH eq_refl e He)].
Qed.

(** The primary exists as soon as at least one entity is admitted. *)
Theorem find_primary_exists :
  forall es, (exists e, In e es /\ gate_valid (ent_gate e) = true) ->
    exists p, find_primary es = Some p.
Proof.
  intros es [e [He Ge]].
  destruct (find_primary es) as [p | ] eqn:H.
  - exists p. reflexivity.
  - pose proof (find_primary_none es H e He) as Hf. rewrite Hf in Ge. discriminate Ge.
Qed.

(** StatusFromERR.uniqueness holds without two of its premises. *)
Lemma uniqueness_without_premises :
  forall e p, ent_id e <> ent_id p -> assign_status e (Some p) <> PrimaryMax.
Proof.
  intros e p Hne. unfold assign_status.
  destruct (negb (gate_valid (ent_gate e))); [discriminate | ].
  destruct (ent_id e =? ent_id p) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - destruct (ent_weight e =? ent_weight p); discriminate.
Qed.

(* ========================================================================= *)
(*  6. RESOLUTION WITHOUT A DEFAULT                                          *)
(* ========================================================================= *)

Definition resolve_role_opt (L : Level) (S : StructuredSystem L)
    (decide : crit_domain L (sys_criterion L (ss_base L S)) -> bool)
    (positions : list Position) : option Position :=
  l5_resolve_gen (role_candidates L S decide positions).

(** The chosen position is a candidate, is occupied by an element that passes the check,
    and is not greater than any other candidate. *)
Theorem resolve_role_opt_first :
  forall (L : Level) (S : StructuredSystem L) decide positions r,
    resolve_role_opt L S decide positions = Some r ->
    In r (role_candidates L S decide positions) /\
    (exists e, ss_assignment L S r = Some e /\ decide e = true) /\
    (forall q, In q (role_candidates L S decide positions) -> r <= q).
Proof.
  intros L S decide positions r H. unfold resolve_role_opt in H.
  pose proof (l5_resolve_gen_in _ _ H) as Hin.
  split; [exact Hin | split].
  - unfold role_candidates in Hin. apply filter_In in Hin. destruct Hin as [_ Hdec].
    destruct (ss_assignment L S r) as [e | ].
    + exists e. split; [reflexivity | exact Hdec].
    + discriminate Hdec.
  - intros q Hq. exact (l5_resolve_gen_minimal _ _ H q Hq).
Qed.

Theorem resolve_role_opt_none_iff :
  forall (L : Level) (S : StructuredSystem L) decide positions,
    resolve_role_opt L S decide positions = None <->
    role_candidates L S decide positions = [].
Proof. intros. unfold resolve_role_opt. apply l5_resolve_gen_none_iff. Qed.

(** Agreement with resolve_role: with the found first as the default the results coincide. *)
Theorem resolve_role_opt_agrees :
  forall (L : Level) (S : StructuredSystem L) decide positions r,
    resolve_role_opt L S decide positions = Some r ->
    resolve_role L S decide positions r = r.
Proof.
  intros L S decide positions r H. unfold resolve_role.
  apply l5_resolve_gen_specializes. exact H.
Qed.
