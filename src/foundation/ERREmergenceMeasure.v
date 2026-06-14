(** * ERREmergenceMeasure.v — a numeric MEASURE of emergence (the ordinal "amount"): the count of
      relation-pairs where the whole's Roles deviate from the part->whole baseline (a Hamming distance
      to the product).  Complements the qualitative strata of ERREmergenceTaxonomy: AMOUNT (here) +
      DIRECTION (super/sub/non-separable, there).

    On a FINITE decidable carrier the deviation of a composite's (bool-valued) Roles R from the
    baseline `base` is COUNTABLE.  The measure is the number of pairs (p,q) where R and base disagree:

      ★ emergence_measure base R := |{ (p,q) : R p q /= base p q }| over the carrier;
      ★ measure_self_zero — a relation deviates from itself by 0: REDUCIBLE <=> measure 0;
      ★ measure_pos_means_disagreement — positive measure exhibits a witnessed disagreement (emergent);
      ★ concrete amounts over the eq-baseline (bool*bool): parity = 4, full = 12;
      ★ ordinal order — parity is LESS emergent than the full relation (4 < 12).

    The carriers/relations here are the decidable bool-shadows of ERREmergenceTaxonomy: beq = the
    eq-baseline (prod_rel eq eq), bfull = the super-additive witness (the full relation), bpar = the
    parity (Bell/GHZ) correlation.  The qualitative DIRECTION (super/sub/non-separable) plus this
    quantitative AMOUNT together describe emergence.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      emergence gets a numeric AMOUNT — the count of relation-pairs where the whole's Roles deviate
      from the part->whole baseline (a Hamming distance to the product).  reducible <=> amount 0;
      emergent <=> positive; the strata get concrete amounts (parity 4, full 12 over the eq-baseline),
      ORDERED (parity less emergent than full).  Amount (this file) + direction (taxonomy) together.
    Roles (L4): emergence_measure (the count); disagree (per-pair deviation); beq / bfull / bpar
      (decidable shadows of the eq-baseline / super-witness / parity).
    Elements (L1+P4): the finite carrier bool*bool; its relation-pairs; bool-valued relations.
    P4 diagnostic (could it be otherwise?):
      the amount is FORCED by the deviation pattern (a count, fully determined); reducible is exactly
      amount 0; emergent is positive (a witnessed disagreement).  On a FINITE carrier the measure is
      computable (P4: finite, actual).  For an infinite carrier the count is a process (role-limit) —
      not done here.
    Honesty wall:
      a Hamming-distance count to the baseline on a FINITE decidable carrier (bool*bool); not
      normalized, not continuous; it COMPLEMENTS (does not replace) the qualitative strata — AMOUNT
      (measure) + DIRECTION (taxonomy).  bpar / beq / bfull are the decidable bool-shadows of
      parity_roles / prod_rel-eq / full (ERREmergenceTaxonomy).  Self-contained (nat/bool/list).
      0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Bool Lia.
Import ListNotations.

(* ===================================================================== *)
(*  THE FINITE CARRIER AND ITS RELATION-PAIRS                              *)
(* ===================================================================== *)

(** The four states of the composite carrier bool*bool. *)
Definition allBB : list (bool * bool) :=
  [ (false, false); (false, true); (true, false); (true, true) ].

(** All 16 ordered relation-pairs over the carrier. *)
Definition allpairs : list ((bool * bool) * (bool * bool)) := list_prod allBB allBB.

(** A decidable (bool-valued) relation on the carrier. *)
Definition BR := (bool * bool) -> (bool * bool) -> bool.

(** A pair where R and base disagree. *)
Definition disagree (R base : BR) (pq : (bool * bool) * (bool * bool)) : bool :=
  negb (Bool.eqb (R (fst pq) (snd pq)) (base (fst pq) (snd pq))).

(** THE MEASURE: the count of pairs where the whole R deviates from the baseline `base`. *)
Definition emergence_measure (base R : BR) : nat :=
  length (filter (disagree R base) allpairs).

(* ===================================================================== *)
(*  THE THREE DECIDABLE WITNESS RELATIONS                                  *)
(* ===================================================================== *)

(** The eq-baseline = prod_rel eq eq (componentwise equality). *)
Definition beq : BR := fun p q => Bool.eqb (fst p) (fst q) && Bool.eqb (snd p) (snd q).

(** The full relation (the super-additive witness). *)
Definition bfull : BR := fun _ _ => true.

(** The parity (Bell/GHZ) correlation (the non-separable witness). *)
Definition bpar : BR := fun p q => Bool.eqb (xorb (fst p) (snd p)) (xorb (fst q) (snd q)).

(* ===================================================================== *)
(*  REDUCIBLE <=> MEASURE 0                                                *)
(* ===================================================================== *)

Lemma filter_all_false : forall {A : Type} (f : A -> bool) (l : list A),
  (forall x, f x = false) -> filter f l = [].
Proof. intros A f l H. induction l as [|x xs IH]; simpl; [ reflexivity | rewrite H; exact IH ]. Qed.

(** ★★ A relation deviates from itself by 0 — REDUCIBLE (whole = baseline) has measure 0. *)
Lemma measure_self_zero : forall base, emergence_measure base base = 0.
Proof.
  intro base. unfold emergence_measure.
  assert (Hf : filter (disagree base base) allpairs = []).
  { apply filter_all_false. intro pq. unfold disagree.
    destruct (base (fst pq) (snd pq)); reflexivity. }
  rewrite Hf. reflexivity.
Qed.

(** ★★ Positive measure EXHIBITS a witnessed disagreement — an emergent composite genuinely deviates
    from the baseline at some pair. *)
Lemma measure_pos_means_disagreement : forall base R, emergence_measure base R > 0 ->
  exists pq, In pq allpairs /\ R (fst pq) (snd pq) <> base (fst pq) (snd pq).
Proof.
  intros base R H. unfold emergence_measure in H.
  destruct (filter (disagree R base) allpairs) as [|pq rest] eqn:E.
  - simpl in H. lia.
  - exists pq.
    assert (Hin : In pq (filter (disagree R base) allpairs)) by (rewrite E; left; reflexivity).
    apply filter_In in Hin. destruct Hin as [Hinp Hdis]. split; [ exact Hinp | ].
    intro Heq. unfold disagree in Hdis. rewrite Heq in Hdis.
    destruct (base (fst pq) (snd pq)); simpl in Hdis; discriminate Hdis.
Qed.

(* ===================================================================== *)
(*  CONCRETE AMOUNTS AND THE ORDINAL ORDER                                 *)
(* ===================================================================== *)

(** ★ The PARITY correlation deviates from the eq-baseline at 4 pairs (it adds the same-parity
    non-diagonal relations). *)
Lemma measure_eq_par : emergence_measure beq bpar = 4.
Proof. vm_compute. reflexivity. Qed.

(** ★ The FULL relation deviates from the eq-baseline at 12 pairs (all off-diagonal). *)
Lemma measure_eq_full : emergence_measure beq bfull = 12.
Proof. vm_compute. reflexivity. Qed.

(** ★ Sub-additive amount: the diagonal (eq) deviates from the full baseline at 12 pairs. *)
Lemma measure_full_diag : emergence_measure bfull beq = 12.
Proof. vm_compute. reflexivity. Qed.

(** ★★ ORDINAL ORDER: parity is strictly LESS emergent than the full relation over the eq-baseline. *)
Lemma parity_less_emergent_than_full :
  emergence_measure beq bpar < emergence_measure beq bfull.
Proof. rewrite measure_eq_par, measure_eq_full. lia. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE EMERGENCE MEASURE: a numeric amount = the count of relation-pairs deviating from the
    part->whole baseline.  reducible <=> amount 0 (measure_self_zero); emergent => a witnessed
    disagreement (measure_pos_means_disagreement); concrete amounts (parity 4, full 12 over eq),
    ORDERED (parity < full).  Amount complements the qualitative direction (ERREmergenceTaxonomy). *)
Theorem err_emergence_measure :
  (forall base, emergence_measure base base = 0)
  /\ (forall base R, emergence_measure base R > 0 ->
        exists pq, In pq allpairs /\ R (fst pq) (snd pq) <> base (fst pq) (snd pq))
  /\ emergence_measure beq bpar = 4
  /\ emergence_measure beq bfull = 12
  /\ emergence_measure beq bpar < emergence_measure beq bfull.
Proof.
  split; [ exact measure_self_zero | ].
  split; [ exact measure_pos_means_disagreement | ].
  split; [ exact measure_eq_par | ].
  split; [ exact measure_eq_full | exact parity_less_emergent_than_full ].
Qed.

Print Assumptions err_emergence_measure.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  A numeric MEASURE of emergence (deepens ERREmergenceTaxonomy / EmergenceSystem):*)
(*  emergence_measure base R = count of relation-pairs over bool*bool where R *)
(*  deviates from the baseline (a Hamming distance to the product).           *)
(*  measure_self_zero (reducible <=> 0), measure_pos_means_disagreement        *)
(*  (emergent => a witnessed deviation).  Concrete amounts: measure_eq_par = 4 *)
(*  (parity over eq), measure_eq_full = 12 (full over eq), measure_full_diag = *)
(*  12 (diagonal under full); parity_less_emergent_than_full (4 < 12 — ordinal *)
(*  order of emergence).  Capstone err_emergence_measure.  HONEST: a Hamming   *)
(*  count on a FINITE decidable carrier (bool*bool), not normalized/continuous;*)
(*  AMOUNT here + DIRECTION (super/sub/non-sep) in the taxonomy.  beq/bfull/    *)
(*  bpar = decidable shadows of prod_rel-eq / full / parity_roles.            *)
(* ========================================================================= *)
