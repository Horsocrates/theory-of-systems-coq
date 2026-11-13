(** * ERRStratification.v — What the well-formedness criterion says exactly,
      and stratification as the property that excludes self-reference

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.4, places 12-14, 16, 17, 19-22, 2026-11-13):

    Elements: the components of an E/R/R table (numbers below
              [errs_n_components]); the references between them.
    Roles:    the category of a component (Element / Role / Rule) and its
              rank (0 / 1 / 2); "component i refers to component j".
    Rules:    (1) the criterion [is_well_formed] says exactly two things: no
                  component refers to itself, and no Rule refers to a Rule.
                  It accepts a mutual reference of two components, accepts
                  every table without references, and rejects a table with
                  no self-reference at all (a Rule referring to another
                  Rule) — so it is neither necessary nor sufficient for
                  "no self-reference through the categories";
              (2) STRATIFICATION — every reference goes strictly down in
                  rank — implies well-formedness and excludes every
                  reference cycle, direct or mediated, of any length;
              (3) self-application and self-membership are separated by this
                  PROPERTY: the table of E/R/R applied to itself is
                  stratified, hence has no cycle; every paradox table has a
                  self-referring component, hence is not stratified;
              (4) the tables written after the analysis of chapter I.4 WITH
                  their references (E/R/R applied to itself — nine
                  components; the naturals; [distinction_of]) are stratified;
              (5) "one entity in two categories" cannot be expressed in
                  [ERRSystem] (the category is a function of the component);
                  in a record where a component may play several categories
                  it can, and there Russell's "Element = Rule" is a mixing.
    P4 diagnostic ("could it be otherwise?"): nothing infinite — finite
              tables. Forced: stratified => no cycle. NOT forced: the tables
              themselves; each is written by hand after the prose analysis
              and is a description of it, not a derivation.

    STATUS: 29 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import Bool PeanoNat Lia List Relations.
Import ListNotations.

From ToS Require Import foundation.Distinction.
From ToS Require Import foundation.ERRWellFormedness.
From ToS Require Import foundation.ParadoxDiagnosis.
From ToS Require Import foundation.PrinciplesToERR.

(* ========================================================================= *)
(*  1. THE EXACT CONTENT OF [is_well_formed]                                 *)
(* ========================================================================= *)

Section Characterization.
  Variable E : ERRSystem.

  Fixpoint diag_check (k : nat) : bool :=
    match k with
    | O => true
    | S k' => if errs_references E k' k' then false else diag_check k'
    end.

  Lemma diag_check_spec : forall m,
    diag_check m = true <-> (forall k, k < m -> errs_references E k k = false).
  Proof.
    induction m as [|m IH]; simpl.
    - split; [intros _ k Hk; lia | reflexivity].
    - destruct (errs_references E m m) eqn:Hm.
      + split; [discriminate |].
        intro H. specialize (H m (Nat.lt_succ_diag_r m)). congruence.
      + rewrite IH. split.
        * intros H k Hk. destruct (Nat.eq_dec k m) as [-> | Hne]; [exact Hm | apply H; lia].
        * intros H k Hk. apply H. lia.
  Qed.

  Section Inner.
    Variable i : nat.
    Fixpoint refs_check (j : nat) : bool :=
      match j with
      | O => true
      | S j' =>
        if errs_references E i j' then
          match errs_category E j' with
          | Cat_Rule => false
          | _ => refs_check j'
          end
        else refs_check j'
      end.

    Lemma refs_check_spec : forall m,
      refs_check m = true <->
      (forall j, j < m -> errs_references E i j = true -> errs_category E j <> Cat_Rule).
    Proof.
      induction m as [|m IH]; simpl.
      - split; [intros _ j Hj; lia | reflexivity].
      - destruct (errs_references E i m) eqn:Hr.
        + destruct (errs_category E m) eqn:Hc.
          * rewrite IH. split.
            -- intros H j Hj Hrj. destruct (Nat.eq_dec j m) as [-> | Hne];
                 [rewrite Hc; discriminate | apply H; [lia | exact Hrj]].
            -- intros H j Hj. apply H. lia.
          * rewrite IH. split.
            -- intros H j Hj Hrj. destruct (Nat.eq_dec j m) as [-> | Hne];
                 [rewrite Hc; discriminate | apply H; [lia | exact Hrj]].
            -- intros H j Hj. apply H. lia.
          * split; [discriminate |].
            intro H. exfalso. exact (H m (Nat.lt_succ_diag_r m) Hr Hc).
        + rewrite IH. split.
          * intros H j Hj Hrj. destruct (Nat.eq_dec j m) as [-> | Hne];
              [congruence | apply H; [lia | exact Hrj]].
          * intros H j Hj. apply H. lia.
    Qed.
  End Inner.

  Section Outer.
    Variable N : nat.
    Fixpoint rules_check (i : nat) : bool :=
      match i with
      | O => true
      | S i' =>
        match errs_category E i' with
        | Cat_Rule => if refs_check i' N then rules_check i' else false
        | _ => rules_check i'
        end
      end.

    Lemma rules_check_spec : forall m,
      rules_check m = true <->
      (forall i, i < m -> errs_category E i = Cat_Rule -> refs_check i N = true).
    Proof.
      induction m as [|m IH]; simpl.
      - split; [intros _ i Hi; lia | reflexivity].
      - destruct (errs_category E m) eqn:Hc.
        + rewrite IH. split.
          * intros H i Hi Hci. destruct (Nat.eq_dec i m) as [-> | Hne];
              [congruence | apply H; [lia | exact Hci]].
          * intros H i Hi. apply H. lia.
        + rewrite IH. split.
          * intros H i Hi Hci. destruct (Nat.eq_dec i m) as [-> | Hne];
              [congruence | apply H; [lia | exact Hci]].
          * intros H i Hi. apply H. lia.
        + destruct (refs_check m N) eqn:Hr.
          * rewrite IH. split.
            -- intros H i Hi Hci. destruct (Nat.eq_dec i m) as [-> | Hne];
                 [exact Hr | apply H; [lia | exact Hci]].
            -- intros H i Hi. apply H. lia.
          * split; [discriminate |].
            intro H. specialize (H m (Nat.lt_succ_diag_r m) Hc). congruence.
    Qed.
  End Outer.

  Lemma no_self_reference_unfold :
    no_self_reference E = diag_check (errs_n_components E).
  Proof. reflexivity. Qed.

  Lemma rules_above_elements_unfold :
    rules_above_elements E = rules_check (errs_n_components E) (errs_n_components E).
  Proof. reflexivity. Qed.

  (** The criterion says exactly: no component refers to itself, and no
      Rule refers to a Rule. *)
  Theorem is_well_formed_spec :
    is_well_formed E = true <->
    (forall k, k < errs_n_components E -> errs_references E k k = false) /\
    (forall i j, i < errs_n_components E -> j < errs_n_components E ->
       errs_category E i = Cat_Rule -> errs_references E i j = true ->
       errs_category E j <> Cat_Rule).
  Proof.
    unfold is_well_formed. rewrite andb_true_iff.
    rewrite no_self_reference_unfold, rules_above_elements_unfold.
    rewrite diag_check_spec, rules_check_spec.
    split.
    - intros [H1 H2]. split; [exact H1 |].
      intros i j Hi Hj Hc Hr.
      exact (proj1 (refs_check_spec i _) (H2 i Hi Hc) j Hj Hr).
    - intros [H1 H2]. split; [exact H1 |].
      intros i Hi Hc. apply refs_check_spec. intros j Hj Hr. exact (H2 i j Hi Hj Hc Hr).
  Qed.
End Characterization.

(** A table without references passes the criterion whatever its size and
    categories. *)
Theorem no_references_well_formed :
  forall (n : nat) (cat : nat -> ERRCategory),
    is_well_formed (mkERRSys n cat (fun _ _ => false)) = true.
Proof.
  intros n cat. apply is_well_formed_spec. simpl. split.
  - intros k _. reflexivity.
  - intros i j _ _ _ Hr. discriminate Hr.
Qed.

(** The criterion ACCEPTS a mutual reference of two components (a cycle of
    length 2)... *)
Definition two_cycle_system : ERRSystem :=
  mkERRSys 2 (fun _ => Cat_Element) (fun i j => negb (i =? j)).

Theorem two_cycle_well_formed : is_well_formed two_cycle_system = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and REJECTS a table with no self-reference at all: a Rule referring
    to another Rule. *)
Definition rule_refers_other_rule : ERRSystem :=
  mkERRSys 2 (fun _ => Cat_Rule) (fun i j => (i =? 1) && (j =? 0)).

Theorem rule_refers_other_rule_ill_formed :
  no_self_reference rule_refers_other_rule = true /\
  is_well_formed rule_refers_other_rule = false.
Proof. split; vm_compute; reflexivity. Qed.

(* ========================================================================= *)
(*  2. STRATIFICATION                                                        *)
(* ========================================================================= *)

Definition cat_rank (c : ERRCategory) : nat :=
  match c with Cat_Element => 0 | Cat_Role => 1 | Cat_Rule => 2 end.

(** Every reference goes strictly DOWN in rank: Rule -> Role -> Element. *)
Definition stratified (E : ERRSystem) : Prop :=
  forall i j, i < errs_n_components E -> j < errs_n_components E ->
    errs_references E i j = true ->
    cat_rank (errs_category E j) < cat_rank (errs_category E i).

(** Stratification implies the criterion. *)
Theorem stratified_well_formed :
  forall E : ERRSystem, stratified E -> is_well_formed E = true.
Proof.
  intros E H. apply is_well_formed_spec. split.
  - intros k Hk. destruct (errs_references E k k) eqn:Hr; [| reflexivity].
    specialize (H k k Hk Hk Hr). lia.
  - intros i j Hi Hj Hc Hr Hcj. specialize (H i j Hi Hj Hr).
    rewrite Hc, Hcj in H. simpl in H. lia.
Qed.

(** "i refers to j" as a relation on the components of the table. *)
Definition ref_rel (E : ERRSystem) (a b : nat) : Prop :=
  a < errs_n_components E /\ b < errs_n_components E /\ errs_references E a b = true.

Lemma stratified_chain_descends :
  forall E : ERRSystem, stratified E ->
  forall i j, clos_trans nat (ref_rel E) i j ->
    cat_rank (errs_category E j) < cat_rank (errs_category E i).
Proof.
  intros E H i j Hc. induction Hc as [a b [Ha [Hb Hr]] | a b c _ IH1 _ IH2].
  - exact (H a b Ha Hb Hr).
  - lia.
Qed.

(** A stratified table has no self-reference — neither direct nor through
    any chain of references. *)
Theorem stratified_no_reference_cycle :
  forall E : ERRSystem, stratified E -> forall k, ~ clos_trans nat (ref_rel E) k k.
Proof.
  intros E H k Hc. pose proof (stratified_chain_descends E H k k Hc). lia.
Qed.

Theorem self_reference_not_stratified :
  forall (E : ERRSystem) (k : nat),
    k < errs_n_components E -> errs_references E k k = true -> ~ stratified E.
Proof. intros E k Hk Hr H. specialize (H k k Hk Hk Hr). lia. Qed.

(** The mutual reference that the criterion accepts is excluded. *)
Theorem two_cycle_not_stratified : ~ stratified two_cycle_system.
Proof.
  intro H. pose proof (H 0 1) as H01. simpl in H01.
  assert (0 < 0) by (apply H01; [lia | lia | reflexivity]). lia.
Qed.

(** Tables without references are stratified trivially — so passing with no
    references says nothing about the system described. *)
Theorem no_references_stratified :
  forall (n : nat) (cat : nat -> ERRCategory), stratified (mkERRSys n cat (fun _ _ => false)).
Proof. intros n cat i j _ _ Hr. discriminate Hr. Qed.

(* ========================================================================= *)
(*  3. SELF-APPLICATION VERSUS SELF-MEMBERSHIP — separated by a property     *)
(* ========================================================================= *)

Theorem err_meta_stratified : stratified err_meta_system.
Proof.
  intros i j Hi Hj Hr.
  destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; simpl in *;
    try discriminate Hr; try lia.
Qed.

Theorem distinction_meta_stratified : stratified distinction_meta_system.
Proof.
  intros i j Hi Hj Hr.
  destruct i as [|[|[|[|[|[|i]]]]]]; destruct j as [|[|[|[|[|[|j]]]]]]; simpl in *;
    try discriminate Hr; try lia.
Qed.

(** Every paradox table has a component that refers to itself. *)
Theorem paradox_tables_self_referential : forall p : ParadoxType,
  ref_rel (paradox_system p) 0 0.
Proof.
  intro p. unfold ref_rel. destruct p; simpl; (split; [lia | split; [lia | reflexivity]]).
Qed.

Theorem paradox_tables_not_stratified : forall p : ParadoxType,
  ~ stratified (paradox_system p).
Proof.
  intros p H.
  destruct (paradox_tables_self_referential p) as [H0 [_ Hr]].
  exact (self_reference_not_stratified (paradox_system p) 0 H0 Hr H).
Qed.

(** A stratified table is none of the paradox tables — and, more than that,
    has no reference cycle at all (Section 2). *)
Theorem stratified_excludes_paradox_tables :
  forall E : ERRSystem, stratified E -> forall p : ParadoxType, E <> paradox_system p.
Proof. intros E H p Heq. subst E. exact (paradox_tables_not_stratified p H). Qed.

(** Self-application of E/R/R versus self-membership: one table is
    stratified and so has no cycle; the other has a self-referring
    component and so is not stratified. *)
Theorem self_application_vs_self_membership :
  stratified err_meta_system /\
  (forall k, ~ clos_trans nat (ref_rel err_meta_system) k k) /\
  ~ stratified russell_system /\
  ref_rel russell_system 0 0.
Proof.
  split; [exact err_meta_stratified |].
  split; [exact (stratified_no_reference_cycle _ err_meta_stratified) |].
  split; [exact (paradox_tables_not_stratified Paradox_Russell) |].
  exact (paradox_tables_self_referential Paradox_Russell).
Qed.

(* ========================================================================= *)
(*  4. TABLES WRITTEN AFTER THE ANALYSIS OF CHAPTER I.4, WITH REFERENCES     *)
(* ========================================================================= *)

(** E/R/R applied to itself, as the chapter analyses it: the three
    categories as three Elements (0, 1, 2), three Roles (3, 4, 5) — role
    3+k is played by element k —, three concrete Rules (6, 7, 8) that set
    the roles. *)
Definition err_self_application_system : ERRSystem := mkERRSys 9
  (fun i => match i with
            | 0 | 1 | 2 => Cat_Element
            | 3 | 4 | 5 => Cat_Role
            | _ => Cat_Rule
            end)
  (fun i j =>
     ((3 <=? i) && (i <=? 5) && (j =? i - 3))
     || ((6 <=? i) && (i <=? 8) && (3 <=? j) && (j <=? 5))).

Theorem err_self_application_stratified : stratified err_self_application_system.
Proof.
  intros i j Hi Hj Hr.
  destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];
  destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; simpl in *;
    try discriminate Hr; try lia.
Qed.

(** The naturals with their references: the rule "successor" refers to the
    element and to the role, the role refers to the element. *)
Definition nat_system_refs : ERRSystem := mkERRSys 3
  (fun i => match i with 0 => Cat_Element | 1 => Cat_Rule | _ => Cat_Role end)
  (fun i j => ((i =? 1) && ((j =? 0) || (j =? 2))) || ((i =? 2) && (j =? 0))).

Theorem nat_system_refs_stratified : stratified nat_system_refs.
Proof.
  intros i j Hi Hj Hr.
  destruct i as [|[|[|i]]]; destruct j as [|[|[|j]]]; simpl in *;
    try discriminate Hr; try lia.
Qed.

(** [distinction_of] after the chapter's table: rules 0, 1, 2 (the
    constructor, the constructive exclusiveness, the appeal to `classic`),
    roles 3, 4 (input, output), elements 5, 6 (the proposition, the built
    instance); rules -> roles -> elements. *)
Definition distinction_of_system : ERRSystem := mkERRSys 7
  (fun i => match i with
            | 0 | 1 | 2 => Cat_Rule
            | 3 | 4 => Cat_Role
            | _ => Cat_Element
            end)
  (fun i j =>
     ((i <=? 2) && ((j =? 3) || (j =? 4)))
     || ((i =? 3) && (j =? 5)) || ((i =? 4) && (j =? 6))).

Theorem distinction_of_system_stratified : stratified distinction_of_system.
Proof.
  intros i j Hi Hj Hr.
  destruct i as [|[|[|[|[|[|[|i]]]]]]];
  destruct j as [|[|[|[|[|[|[|j]]]]]]]; simpl in *;
    try discriminate Hr; try lia.
Qed.

(** All three pass the criterion and have no reference cycle. *)
Theorem analysed_tables_well_formed :
  is_well_formed err_self_application_system = true /\
  is_well_formed nat_system_refs = true /\
  is_well_formed distinction_of_system = true.
Proof.
  split; [| split]; apply stratified_well_formed.
  - exact err_self_application_stratified.
  - exact nat_system_refs_stratified.
  - exact distinction_of_system_stratified.
Qed.

(* ========================================================================= *)
(*  5. "ONE ENTITY IN TWO CATEGORIES"                                        *)
(* ========================================================================= *)

(** In [ERRSystem] a component has one category: the category is a function
    of the component. *)
Lemma one_category_per_component :
  forall (E : ERRSystem) (k : nat) (c1 c2 : ERRCategory),
    errs_category E k = c1 -> errs_category E k = c2 -> c1 = c2.
Proof. intros E k c1 c2 H1 H2. congruence. Qed.

(** A record in which a component MAY play several categories. *)
Record ERRSystemM := mkERRSysM {
  m_n : nat;
  m_plays : nat -> ERRCategory -> bool;   (* component k plays category c *)
  m_refs : nat -> nat -> bool
}.

Definition unmixed (E : ERRSystemM) : Prop :=
  forall k, k < m_n E -> forall c1 c2,
    m_plays E k c1 = true -> m_plays E k c2 = true -> c1 = c2.

Definition as_multi (E : ERRSystem) : ERRSystemM :=
  mkERRSysM (errs_n_components E)
            (fun k c => err_cat_eqb (errs_category E k) c)
            (errs_references E).

Lemma err_cat_eqb_true : forall c1 c2, err_cat_eqb c1 c2 = true -> c1 = c2.
Proof. intros c1 c2 H. destruct c1, c2; simpl in H; try discriminate H; reflexivity. Qed.

(** No [ERRSystem] mixes categories — the paradox tables included: in that
    record the mixing cannot be written down. *)
Theorem every_ERRSystem_unmixed : forall E : ERRSystem, unmixed (as_multi E).
Proof.
  intros E k _ c1 c2 H1 H2. simpl in H1, H2.
  apply err_cat_eqb_true in H1. apply err_cat_eqb_true in H2. congruence.
Qed.

(** "Element = Rule" literally: one component plays two categories. *)
Definition russell_mixed : ERRSystemM :=
  mkERRSysM 1 (fun _ c => match c with Cat_Role => false | _ => true end) (fun _ _ => true).

Theorem russell_mixed_is_mixed : ~ unmixed russell_mixed.
Proof.
  intro H. specialize (H 0). simpl in H.
  assert (Heq : Cat_Element = Cat_Rule) by (apply H; [lia | reflexivity | reflexivity]).
  discriminate Heq.
Qed.
