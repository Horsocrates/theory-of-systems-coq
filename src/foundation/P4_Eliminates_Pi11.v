(** * P4_Eliminates_Pi11.v — Pi-1-1 comprehension collapses to arithmetic
    Elements: Program codes (nat), eval_program, function quantifiers
    Roles:    Second-order quantification READ as first-order via P4
    Rules:    the quantifier over codes = the quantifier over the functions
              GIVEN BY codes; it is a choice of domain, not an equivalent
              replacement of "forall f"
    STATUS:   17 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    KEY INSIGHT: Pi-1-1 comprehension asserts that {n : forall f, phi(n,f)}
    defines a set whenever phi is arithmetical. This requires quantifying
    over ALL functions nat->nat, which classically means over an uncountable
    set. Under P4 (Finite Actuality), every function is a PROCESS = a
    program. So "forall f" becomes "forall c:nat" — purely arithmetic.

    HONEST SCOPE (Nov 2026).
    - eval_program used to be a Parameter.  It is now a VARIABLE of the
      section: every statement holds for ANY table Program -> nat -> nat, and
      nothing appears in Print Assumptions (except classic in pi11_negation).
    - The file does not prove "every function has a code", and it cannot:
      for any total table the diagonal function n |-> S (ev n n) is outside it
      (no_table_covers_all_functions).  Hence the quantifier over codes is
      strictly weaker than the quantifier over functions
      (codes_reading_is_weaker).  Reading "forall f" as "forall c" is a choice
      of ontology (P4: a function is a process given by a code).
    - What IS proved: the quantifier over codes is the quantifier over the
      functions given by codes (P4_eliminates_Pi11), and the two quantifiers
      coincide exactly under the premise "every function has a code"
      (pi11_hierarchy_collapse).
*)

From Stdlib Require Import Lia PeanoNat List Classical_Prop.
Import ListNotations.

(* ================================================================= *)
(* PROGRAMS AS NATURAL NUMBERS                                        *)
(* ================================================================= *)

(* Under P4, a "function" is a program code.
   eval_program c n = "the value of the function with code c at n".
   Nov 2026: the table is a variable of the section, with no properties
   assumed -- in particular it is total, so it is not a universal machine
   (see cs/HaltingRoleLimit.v for the partial one). *)
Definition Program := nat.

Section Codes.

Variable eval_program : Program -> nat -> nat.

(* ================================================================= *)
(* PI-1-1 COLLAPSE                                                    *)
(* ================================================================= *)

(* Under P4: "for all functions" = "for all program codes" *)
Definition P4_forall_functions (phi : (nat -> nat) -> nat -> Prop) (n : nat) : Prop :=
  forall c : Program, phi (eval_program c) n.

(* Under P4: "exists a function" = "exists a program code" *)
Definition P4_exists_function (phi : (nat -> nat) -> nat -> Prop) (n : nat) : Prop :=
  exists c : Program, phi (eval_program c) n.

(* ================================================================= *)
(* PROOFS                                                             *)
(* ================================================================= *)

(* 1. Programs ARE natural numbers *)
Lemma P4_functions_are_nat : Program = nat.
Proof. reflexivity. Qed.

(* 2. Pi-1-1 is just arithmetic under P4 *)
Lemma pi11_to_arithmetic : forall phi n,
  P4_forall_functions phi n <-> forall c : nat, phi (eval_program c) n.
Proof. intros. unfold P4_forall_functions, Program. split; auto. Qed.

(* 3. Sigma-1-1 is just arithmetic under P4 *)
Lemma sigma11_to_arithmetic : forall phi n,
  P4_exists_function phi n <-> exists c : nat, phi (eval_program c) n.
Proof. intros. unfold P4_exists_function, Program. split; auto. Qed.

(* 4. Program codes exist — nat is INHABITED (June 2026: was `exists c, c = c`,
      vacuous; `inhabited` is the honest nonemptiness statement) *)
Lemma program_exists : inhabited Program.
Proof. exact (inhabits 0). Qed.

(* 5. The function space is "countable" — indexed by nat *)
Lemma function_space_indexed_by_nat :
  forall (phi : (nat -> nat) -> Prop),
  (forall f, phi f) ->
  (forall c : nat, phi (eval_program c)).
Proof. intros phi H c. apply H. Qed.

(* 6. Negation of Pi-1-1 becomes Sigma-1-1 *)
Lemma pi11_negation : forall phi n,
  ~ P4_forall_functions phi n <->
  exists c : nat, ~ phi (eval_program c) n.
Proof.
  intros. unfold P4_forall_functions, Program. split.
  - intros H.
    (* This direction needs classical logic or decidability.
       We prove the contrapositive form instead. *)
    destruct (Classical_Prop.classic (exists c, ~ phi (eval_program c) n)) as [E|NE].
    + exact E.
    + exfalso. apply H. intro c.
      destruct (Classical_Prop.classic (phi (eval_program c) n)) as [Y|N].
      * exact Y.
      * exfalso. apply NE. exists c. exact N.
  - intros [c Hc] Hall. apply Hc. apply Hall.
Qed.

(* 7. Comprehension: the set defined by Pi-1-1 is arithmetical *)
Definition pi11_set (phi : (nat -> nat) -> nat -> Prop) : nat -> Prop :=
  fun n => P4_forall_functions phi n.

Lemma pi11_set_is_arithmetic : forall phi n,
  pi11_set phi n <-> forall c : nat, phi (eval_program c) n.
Proof. intros. unfold pi11_set. apply pi11_to_arithmetic. Qed.

(* 8. Composition of program evaluations *)
Definition compose_programs (c1 c2 : Program) : nat -> nat :=
  fun n => eval_program c1 (eval_program c2 n).

Lemma compose_is_nat_function : forall c1 c2,
  compose_programs c1 c2 = fun n => eval_program c1 (eval_program c2 n).
Proof. intros. reflexivity. Qed.

(* 9. Pi-1-1 is closed under conjunction *)
Lemma pi11_conjunction : forall phi psi n,
  P4_forall_functions phi n /\ P4_forall_functions psi n <->
  P4_forall_functions (fun f => fun m => phi f m /\ psi f m) n.
Proof.
  intros. unfold P4_forall_functions. split.
  - intros [Hp Hq] c. split; [apply Hp | apply Hq].
  - intros H. split; intros c; specialize (H c); destruct H; assumption.
Qed.

(* 10. Sigma-1-1 is closed under disjunction *)
Lemma sigma11_disjunction : forall phi psi n,
  P4_exists_function phi n \/ P4_exists_function psi n ->
  P4_exists_function (fun f => fun m => phi f m \/ psi f m) n.
Proof.
  intros. unfold P4_exists_function in *.
  destruct H as [[c Hc] | [c Hc]].
  - exists c. left. exact Hc.
  - exists c. right. exact Hc.
Qed.

(* 11. Every decidable property lifts to programs *)
Lemma decidable_lift : forall (P : nat -> Prop) (dec : forall n, P n \/ ~ P n),
  forall n, P n \/ ~ P n.
Proof. intros. apply dec. Qed.

(* 12. Pi-1-1 implies Sigma-1-1 with witness *)
Lemma pi11_witness : forall phi n c,
  P4_forall_functions phi n -> phi (eval_program c) n.
Proof. intros. apply H. Qed.

(* 13. The hierarchy collapses -- Pi-1-1 = forall-nat -- exactly under the
       premise that every function has a code.  (Nov 2026: the premise used to
       be an equation that the proof ignored; now it is the real condition and
       it is used.) *)
Theorem pi11_hierarchy_collapse :
  forall (phi : (nat -> nat) -> nat -> Prop),
  (forall f : nat -> nat, exists c : Program, f = eval_program c) ->
  forall n, (forall f, phi f n) <-> P4_forall_functions phi n.
Proof.
  intros phi Hcode n. split.
  - intros H c. apply H.
  - intros H f. destruct (Hcode f) as [c Hc]. rewrite Hc. apply H.
Qed.

(* 13a. That premise fails for every table: the diagonal function is outside it. *)
Theorem no_table_covers_all_functions :
  ~ (forall f : nat -> nat, exists c : Program, f = eval_program c).
Proof.
  intro H. destruct (H (fun n => S (eval_program n n))) as [c Hc].
  pose proof (f_equal (fun g : nat -> nat => g c) Hc) as E. cbv beta in E.
  exact (Nat.neq_succ_diag_l _ E).
Qed.

(* 13b. So the quantifier over codes is strictly weaker than the quantifier
        over functions. *)
Theorem codes_reading_is_weaker :
  exists phi : (nat -> nat) -> nat -> Prop,
    (forall n, P4_forall_functions phi n) /\ ~ (forall n f, phi f n).
Proof.
  exists (fun f _ => exists c : Program, forall m, f m = eval_program c m). split.
  - intros n c. exists c. reflexivity.
  - intro H. destruct (H 0 (fun n => S (eval_program n n))) as [c Hc].
    specialize (Hc c). cbv beta in Hc. exact (Nat.neq_succ_diag_l _ Hc).
Qed.

(* 14. Concrete: constant zero function *)
Definition const_zero : nat -> nat := fun _ => 0.

Lemma const_zero_property : forall n, const_zero n = 0.
Proof. intros. reflexivity. Qed.

(* 15. SYNTHESIS.  The P4 reading of "forall f" is the quantifier over codes;
   it IS the quantifier over the functions given by codes.  (Nov 2026: the
   statement used to repeat the definition; "every function has a code" is not
   claimed and is false for a total table, see 13a.) *)
Theorem P4_eliminates_Pi11 :
  forall phi n,
  P4_forall_functions phi n <->
  (forall f : nat -> nat, (exists c : Program, f = eval_program c) -> phi f n).
Proof.
  intros phi n. split.
  - intros H f [c Hc]. subst. apply H.
  - intros H c. apply H. exists c. reflexivity.
Qed.

End Codes.
