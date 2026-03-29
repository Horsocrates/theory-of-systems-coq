(** * TransfiniteInduction.v — Transfinite Induction (PROVEN, no axiom)
    Elements: Ord, ord_lt (from Ordinal.v)
    Roles:    Transfinite induction principle, recursion
    Rules:    Well-foundedness PROVEN from structural induction on Ord
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    KEY RESULT: wf_ord_lt is a THEOREM, not an axiom.
    Because Ord is inductive and ord_lt constructors decrease structure,
    well-foundedness follows from structural induction + acc_succ lemma.

    Print Assumptions: classic, L4_witness only (2 axioms, same as before).
    NO new axioms introduced.
*)

From ToS Require Import Ordinal.
From Stdlib Require Import Wellfounded.

(* ================================================================= *)
(* WELL-FOUNDEDNESS: PROVEN                                           *)
(* ================================================================= *)

(** Helper: if x is accessible, then OSucc x is accessible.
    Proof by induction on the Acc derivation. *)
Lemma acc_succ : forall x, Acc ord_lt x -> Acc ord_lt (OSucc x).
Proof.
  intros x Hacc. induction Hacc as [x Hx IH].
  constructor. intros b Hb. inversion Hb; subst.
  - (* b = OZero, from lt_zero_succ *)
    constructor. intros c Hc. inversion Hc.
  - (* b = OSucc a0, from lt_succ_mono *)
    apply IH. assumption.
Qed.

(** ★★★ THEOREM (not axiom): ord_lt is well-founded.
    Proof by structural induction on Ord:
    - OZero: nothing is less (inversion)
    - OSucc a: acc_succ applied to IH
    - OLim f: Acc_inv on IHf(n) for appropriate n *)
Theorem wf_ord_lt : well_founded ord_lt.
Proof.
  intro a. induction a as [| a' IHa | f IHf].
  - (* OZero: nothing < OZero *)
    constructor. intros b Hb. inversion Hb.
  - (* OSucc a': use acc_succ *)
    apply acc_succ. exact IHa.
  - (* OLim f: use IHf for each component *)
    constructor. intros b Hb.
    inversion Hb as [| | a0 f0 n0 Hlt Heq1 Heq2 | a0 f0 Hex Heq1 Heq2]; subst.
    + (* lt_to_lim: ord_lt b (f n0) *)
      eapply Acc_inv. apply IHf. exact Hlt.
    + (* lt_succ_to_lim: b = OSucc a0, exists n, ord_lt a0 (f n) *)
      destruct Hex as [m Hm].
      apply acc_succ. eapply Acc_inv. apply IHf. exact Hm.
Qed.

(* ================================================================= *)
(* TRANSFINITE INDUCTION                                              *)
(* ================================================================= *)

(** Transfinite induction -- follows immediately from well-foundedness *)
Theorem transfinite_ind : forall (P : Ord -> Prop),
  (forall a, (forall b, ord_lt b a -> P b) -> P a) ->
  forall a, P a.
Proof.
  intros P H a. apply (well_founded_ind wf_ord_lt). exact H.
Qed.

(* ================================================================= *)
(* TRANSFINITE RECURSION                                              *)
(* ================================================================= *)

(** Transfinite recursion -- existence of recursive functions along ord_lt *)
Theorem transfinite_rec : forall (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_lt b a -> T) -> T),
  forall a : Ord, T.
Proof.
  intros T step a.
  exact (well_founded_induction_type wf_ord_lt (fun _ => T) step a).
Qed.

(* ================================================================= *)
(* SPECIAL CASES                                                      *)
(* ================================================================= *)

(** Nat induction as a special case (trivially provable, shows connection) *)
Lemma nat_induction_from_transfinite : forall (P : nat -> Prop),
  P O -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros P H0 HS n. induction n.
  - exact H0.
  - apply HS. exact IHn.
Qed.

(** Omega tower induction *)
Lemma omega_tower_induction : forall (P : nat -> Prop),
  P O ->
  (forall n, P n -> P (S n)) ->
  forall n, P n.
Proof.
  intros P H0 HS. exact (nat_ind P H0 HS).
Qed.

(* ================================================================= *)
(* TRANSFINITE INDUCTION AT SPECIFIC ORDINALS                        *)
(* ================================================================= *)

(** Transfinite induction at OZero *)
Lemma transfinite_ind_zero : forall (P : Ord -> Prop),
  (forall a, (forall b, ord_lt b a -> P b) -> P a) ->
  P OZero.
Proof.
  intros P H. apply transfinite_ind. exact H.
Qed.

(** Transfinite induction at OSucc *)
Lemma transfinite_ind_succ : forall (P : Ord -> Prop),
  (forall a, (forall b, ord_lt b a -> P b) -> P a) ->
  forall a, P (OSucc a).
Proof.
  intros P H a. apply transfinite_ind. exact H.
Qed.

(** Transfinite induction at omega *)
Lemma transfinite_ind_omega : forall (P : Ord -> Prop),
  (forall a, (forall b, ord_lt b a -> P b) -> P a) ->
  P omega.
Proof.
  intros P H. apply transfinite_ind. exact H.
Qed.

(** Transfinite induction at epsilon_0 *)
Lemma transfinite_ind_epsilon_0 : forall (P : Ord -> Prop),
  (forall a, (forall b, ord_lt b a -> P b) -> P a) ->
  P epsilon_0.
Proof.
  intros P H. apply transfinite_ind. exact H.
Qed.

(* ================================================================= *)
(* WELL-FOUNDEDNESS PROPERTIES                                       *)
(* ================================================================= *)

(** Well-foundedness restricts to nat embedding *)
Lemma wf_restricts_to_nat : forall n, Acc ord_lt (nat_to_ord n).
Proof.
  intros n. apply wf_ord_lt.
Qed.

(** Axiom inventory: NO new axioms. Only classic + L4_witness. *)
Lemma axiom_count_documentation :
  (* classic = L3, L4_witness = L4. wf_ord_lt is now a THEOREM. *)
  True.
Proof. exact I. Qed.
