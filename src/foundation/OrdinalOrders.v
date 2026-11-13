(** * OrdinalOrders.v — the orders on ordinal notations, and induction along them

    Elements: ordinal notations Ord (OZero, OSucc a, OLim f) from Ordinal.v.
    Roles:    one notation plays for another
              - "a STAGE of its construction" (the predecessor of a successor,
                any stage f n of a limit OLim f): the order of construction,
                ord_below;
              - "NOT GREATER" (OLim f read as the least upper bound of its
                stages): the order of comparison, ole / olt (Brouwer's order).
    Rules:    both orders are well-founded.  Induction along ord_below has, at
              a limit step, the hypothesis for ALL stages; recursion along it
              comes with its fixed-point equation.
    P4 diagnostic ("could it be otherwise?"): the order of construction is
              forced by the inductive definition of Ord itself.  The relation
              ord_lt of Ordinal.v is not: nothing forces it to admit only
              finite notations on the left (section A below).

    Why this file (Nov 2026).  Transfinite induction was stated along ord_lt
    (TransfiniteInduction.v).  Those theorems are true, but ord_lt compares
    with a notation only the FINITE notations: omega is not below omega+1 and
    not below epsilon_0, and below epsilon_0 lies exactly what lies below
    omega.  At a limit step induction along ord_lt knows nothing about the
    stages of the limit.  Here are the orders that do the work.

    A. What ord_lt really is.
    B. The order of construction: well-foundedness, induction, induction below
       epsilon_0, induction along the tower, recursion with its equation.
    C. Brouwer's order: reflexive, transitive, well-founded; omega < omega+1,
       n < omega, omega < epsilon_0; a stage of construction is not greater.

    STATUS: 40 Qed, 0 Admitted, 0 axioms (every statement: Closed under the
            global context)
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import Lia PeanoNat Wellfounded Relation_Operators.
From ToS Require Import foundation.Ordinal foundation.TransfiniteInduction.

(* ================================================================= *)
(* A. What lies below a notation along ord_lt                         *)
(* ================================================================= *)

(** On the left of ord_lt there are only finite notations. *)
Lemma ord_lt_left_numeral : forall b a, ord_lt a b -> exists n, a = nat_to_ord n.
Proof.
  induction b as [| b' IH | f IH]; intros a H.
  - inversion H.
  - inversion H; subst.
    + exists 0. reflexivity.
    + match goal with H0 : ord_lt _ b' |- _ => destruct (IH _ H0) as [n Hn] end.
      exists (S n). simpl. rewrite Hn. reflexivity.
  - inversion H as [| | a0 f0 n0 Hlt Heq1 Heq2 | a0 f0 Hex Heq1 Heq2]; subst.
    + exact (IH n0 _ Hlt).
    + destruct Hex as [m Hm]. destruct (IH m _ Hm) as [n Hn].
      exists (S n). simpl. rewrite Hn. reflexivity.
Qed.

(** A limit notation is not below any notation. *)
Theorem lim_not_lt : forall f x, ~ ord_lt (OLim f) x.
Proof.
  intros f x H. destruct (ord_lt_left_numeral _ _ H) as [n Hn].
  destruct n; discriminate Hn.
Qed.

Corollary omega_not_lt_succ_omega : ~ ord_lt omega (OSucc omega).
Proof. unfold omega. apply lim_not_lt. Qed.

Corollary omega_not_lt_epsilon_0 : ~ ord_lt omega epsilon_0.
Proof. unfold omega. apply lim_not_lt. Qed.

(** Every stage of the tower is itself a limit notation. *)
Lemma tower_stage_is_limit : forall n, exists g, omega_tower n = OLim g.
Proof.
  induction n as [| n [g Hg]].
  - exists nat_to_ord. reflexivity.
  - simpl. rewrite Hg. simpl. eexists. reflexivity.
Qed.

(** So no stage of the tower is below epsilon_0 along ord_lt. *)
Corollary tower_stage_not_lt_epsilon_0 : forall n, ~ ord_lt (omega_tower n) epsilon_0.
Proof.
  intros n. destruct (tower_stage_is_limit n) as [g Hg]. rewrite Hg. apply lim_not_lt.
Qed.

Lemma below_omega_iff : forall x, ord_lt x omega <-> exists n, x = nat_to_ord n.
Proof.
  intros x. split.
  - apply ord_lt_left_numeral.
  - intros [n Hn]. subst. apply nat_lt_omega.
Qed.

(** Below epsilon_0 along ord_lt lies exactly what lies below omega. *)
Theorem below_epsilon_0_iff_below_omega : forall x, ord_lt x epsilon_0 <-> ord_lt x omega.
Proof.
  intros x. split.
  - intros H. apply below_omega_iff. exact (ord_lt_left_numeral _ _ H).
  - intros H. unfold epsilon_0. apply lt_to_lim with (n := 0). simpl. exact H.
Qed.

(** ord_lt does not read OLim as an upper bound either: 1 < sup{1,1,1,...}. *)
Lemma one_lt_lim_const_one : ord_lt (OSucc OZero) (OLim (fun _ => OSucc OZero)).
Proof. apply lt_succ_to_lim. exists 0. apply lt_zero_succ. Qed.

(* ================================================================= *)
(* B. The order of construction                                       *)
(* ================================================================= *)

(** One step of construction: a is the predecessor of OSucc a; f n is a stage of OLim f. *)
Inductive ord_sub : Ord -> Ord -> Prop :=
  | sub_succ : forall a, ord_sub a (OSucc a)
  | sub_lim  : forall f n, ord_sub (f n) (OLim f).

Lemma wf_ord_sub : well_founded ord_sub.
Proof.
  intro a. induction a as [| a IH | f IH]; constructor; intros b Hb; inversion Hb; subst.
  - exact IH.
  - apply IH.
Qed.

(** The order of construction: finitely many steps. *)
Definition ord_below : Ord -> Ord -> Prop := clos_trans Ord ord_sub.

Theorem wf_ord_below : well_founded ord_below.
Proof. unfold ord_below. apply wf_clos_trans. exact wf_ord_sub. Qed.

Lemma ord_below_trans : forall a b c, ord_below a b -> ord_below b c -> ord_below a c.
Proof. intros a b c H1 H2. exact (t_trans _ _ _ _ _ H1 H2). Qed.

Lemma below_succ : forall a, ord_below a (OSucc a).
Proof. intro a. apply t_step. constructor. Qed.

Lemma stage_below_lim : forall f n, ord_below (f n) (OLim f).
Proof. intros f n. apply t_step. constructor. Qed.

(** Transfinite induction along the order of construction: at a limit step the
    hypothesis is available for all stages and everything below them. *)
Theorem structural_transfinite_ind : forall P : Ord -> Prop,
  (forall a, (forall b, ord_below b a -> P b) -> P a) -> forall a, P a.
Proof. intros P H. apply (well_founded_ind wf_ord_below). exact H. Qed.

Lemma nat_below_omega : forall n, ord_below (nat_to_ord n) omega.
Proof. intro n. unfold omega. apply stage_below_lim. Qed.

Lemma tower_below_epsilon_0 : forall n, ord_below (omega_tower n) epsilon_0.
Proof. intro n. unfold epsilon_0. apply stage_below_lim. Qed.

Lemma omega_below_epsilon_0 : ord_below omega epsilon_0.
Proof. exact (tower_below_epsilon_0 0). Qed.

Lemma omega_below_succ_omega : ord_below omega (OSucc omega).
Proof. apply below_succ. Qed.

(** Induction "up to epsilon_0": a property inherited upwards among the
    notations below epsilon_0 holds for all notations below epsilon_0. *)
Theorem induction_below_epsilon_0 : forall P : Ord -> Prop,
  (forall a, ord_below a epsilon_0 -> (forall b, ord_below b a -> P b) -> P a) ->
  forall a, ord_below a epsilon_0 -> P a.
Proof.
  intros P H.
  apply (well_founded_ind wf_ord_below (fun a => ord_below a epsilon_0 -> P a)).
  intros a IH Ha. apply (H a Ha). intros b Hb. apply (IH b Hb).
  exact (ord_below_trans _ _ _ Hb Ha).
Qed.

(** Induction along the tower: over the stages omega_tower n. *)
Theorem tower_induction : forall P : Ord -> Prop,
  P omega -> (forall n, P (omega_tower n) -> P (omega_tower (S n))) ->
  forall n, P (omega_tower n).
Proof. intros P H0 HS n. induction n as [| n IH]; [exact H0 | exact (HS n IH)]. Qed.

(** Recursion along the order of construction ... *)
Definition ord_rec (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_below b a -> T) -> T) : Ord -> T :=
  Fix wf_ord_below (fun _ => T) step.

(** ... with its fixed-point equation: the value at a is the step applied to
    the values below a. *)
Theorem ord_rec_eq : forall (T : Type)
  (step : forall a : Ord, (forall b : Ord, ord_below b a -> T) -> T),
  (forall a (f g : forall b, ord_below b a -> T),
      (forall b p, f b p = g b p) -> step a f = step a g) ->
  forall a, ord_rec T step a = step a (fun b _ => ord_rec T step b).
Proof.
  intros T step Hext a. unfold ord_rec.
  exact (Fix_eq wf_ord_below (fun _ => T) step Hext a).
Qed.

(* ================================================================= *)
(* C. Brouwer's order: OLim f is the least upper bound of its stages  *)
(* ================================================================= *)

Inductive ole : Ord -> Ord -> Prop :=
  | ole_zero  : forall b, ole OZero b
  | ole_succ  : forall a b, ole a b -> ole (OSucc a) (OSucc b)
  | ole_stage : forall a f n, ole a (f n) -> ole a (OLim f)
  | ole_lim   : forall f b, (forall n, ole (f n) b) -> ole (OLim f) b.

Definition olt (a b : Ord) : Prop := ole (OSucc a) b.

Lemma ole_refl : forall a, ole a a.
Proof.
  induction a as [| a IH | f IH].
  - constructor.
  - constructor. exact IH.
  - apply ole_lim. intro n. apply ole_stage with n. apply IH.
Qed.

Lemma ole_lim_inv : forall x c, ole x c -> forall f, x = OLim f -> forall n, ole (f n) c.
Proof.
  intros x c H. induction H as [b | a b _ _ | a g m _ IH | g b Hg _]; intros f Heq n.
  - discriminate Heq.
  - discriminate Heq.
  - apply ole_stage with m. exact (IH f Heq n).
  - injection Heq as Heq. subst. apply Hg.
Qed.

Lemma ole_succ_trans_aux : forall a b,
  (forall c, ole b c -> ole a c) ->
  forall x c, ole x c -> x = OSucc b -> ole (OSucc a) c.
Proof.
  intros a b IH x c H. induction H as [c | b0 c' Hb0 _ | a0 g m _ IHin | g c _ _]; intro Heq.
  - discriminate Heq.
  - injection Heq as Heq. subst. apply ole_succ. apply IH. exact Hb0.
  - apply ole_stage with m. apply IHin. exact Heq.
  - discriminate Heq.
Qed.

Theorem ole_trans : forall a b, ole a b -> forall c, ole b c -> ole a c.
Proof.
  intros a b H. induction H as [b | a b _ IH | a f n _ IH | f b _ IH]; intros c Hc.
  - constructor.
  - exact (ole_succ_trans_aux a b IH _ c Hc eq_refl).
  - apply IH. exact (ole_lim_inv _ _ Hc f eq_refl n).
  - apply ole_lim. intro n. apply (IH n). exact Hc.
Qed.

Lemma acc_olt_down : forall b, Acc olt b -> forall a, ole a b -> Acc olt a.
Proof.
  intros b Hb a Hab. constructor. intros c Hc.
  apply (Acc_inv Hb). unfold olt in *. exact (ole_trans _ _ Hc _ Hab).
Qed.

Theorem wf_olt : well_founded olt.
Proof.
  intro b. induction b as [| b IH | f IH]; constructor; intros c Hc; unfold olt in Hc.
  - inversion Hc.
  - inversion Hc; subst. apply (acc_olt_down b IH). assumption.
  - inversion Hc as [| | a0 f0 n0 Hle Heq1 Heq2 |]; subst.
    apply (Acc_inv (IH n0)). exact Hle.
Qed.

Theorem brouwer_transfinite_ind : forall P : Ord -> Prop,
  (forall a, (forall b, olt b a -> P b) -> P a) -> forall a, P a.
Proof. intros P H. apply (well_founded_ind wf_olt). exact H. Qed.

Lemma olt_succ : forall a, olt a (OSucc a).
Proof. intro a. unfold olt. apply ole_refl. Qed.

Lemma ole_stage_lim : forall f n, ole (f n) (OLim f).
Proof. intros f n. apply ole_stage with n. apply ole_refl. Qed.

Lemma ole_self_succ : forall b, ole b (OSucc b).
Proof.
  induction b as [| b IH | f IH].
  - constructor.
  - constructor. exact IH.
  - apply ole_lim. intro n. apply (ole_trans _ _ (IH n)).
    constructor. apply ole_stage_lim.
Qed.

Lemma olt_trans : forall a b c, olt a b -> olt b c -> olt a c.
Proof.
  unfold olt. intros a b c Hab Hbc.
  apply (ole_trans _ _ Hab).
  apply (ole_trans b (OSucc b)); [apply ole_self_succ | exact Hbc].
Qed.

(** The two orders agree: a stage of construction is not greater. *)
Lemma ord_below_ole : forall a b, ord_below a b -> ole a b.
Proof.
  intros a b H. induction H as [x y Hs | x y z _ IH1 _ IH2].
  - destruct Hs as [a | f n]; [apply ole_self_succ | apply ole_stage_lim].
  - exact (ole_trans _ _ IH1 _ IH2).
Qed.

Lemma olt_nat_omega : forall n, olt (nat_to_ord n) omega.
Proof.
  intro n. unfold olt, omega. apply ole_stage with (S n). simpl. apply ole_refl.
Qed.

Lemma olt_omega_succ_omega : olt omega (OSucc omega).
Proof. apply olt_succ. Qed.

Lemma mul_one_numeral : forall n, ord_mul (OSucc OZero) (nat_to_ord n) = nat_to_ord n.
Proof. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma add_zero_numeral : forall n, ord_add OZero (nat_to_ord n) = nat_to_ord n.
Proof. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** omega < epsilon_0 in Brouwer's order. *)
Theorem olt_omega_epsilon_0 : olt omega epsilon_0.
Proof.
  unfold olt, epsilon_0.
  apply ole_stage with 1. simpl.            (* omega ^ omega *)
  apply ole_stage with 2. simpl.            (* omega ^ 2 = (omega^1) * omega *)
  apply ole_stage with 2. simpl.            (* (omega^1) * 2 *)
  apply ole_stage with 1. simpl.            (* (omega^1)*1 + 1 *)
  apply ole_succ.
  unfold omega at 1. apply ole_lim. intro n.
  apply ole_stage with n.
  rewrite mul_one_numeral, add_zero_numeral. apply ole_refl.
Qed.

(** ord_lt is not Brouwer's order: the example one_lt_lim_const_one fails in it. *)
Lemma olt_differs_from_ord_lt : ~ olt (OSucc OZero) (OLim (fun _ => OSucc OZero)).
Proof.
  unfold olt. intro H.
  inversion H as [| | a f n Hle Heq1 Heq2 |]; subst. cbv beta in Hle.
  inversion Hle as [| a b Hle' Heq1 Heq2 | |]; subst.
  inversion Hle'.
Qed.

(* Axiom audit: expected "Closed under the global context" for each. *)
Print Assumptions below_epsilon_0_iff_below_omega.
Print Assumptions wf_ord_below.
Print Assumptions structural_transfinite_ind.
Print Assumptions induction_below_epsilon_0.
Print Assumptions tower_induction.
Print Assumptions ord_rec_eq.
Print Assumptions ole_trans.
Print Assumptions wf_olt.
Print Assumptions olt_omega_epsilon_0.
Print Assumptions ord_below_ole.
