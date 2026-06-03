(** * CantorTheoremGeneral.v — Cantor's theorem without choice, for any type
    Elements: a type X, predicates X->bool, candidate map f : X -> (X->bool)
    Roles:    surjectivity = role of f; the diagonal predicate = refuter
    Rules:    diagonal g x := negb (f x x) differs from every row => no surjection
    STATUS:   6 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The GENERAL Cantor theorem: for ANY type X there is no surjection
    X -> (X -> bool). Fully constructive: no classic, no choice. Surjectivity
    itself supplies the witness a with f a = g; the diagonal
    g a = negb (f a a) then contradicts f a a = g a. No inhabitant of X is
    needed: the refuting predicate IS the witness.

    HONEST SCOPE: this concerns the bool-power TYPE (predicates over X), NOT a
    completed power-set Element-object. The power set AS A SET is structurally
    blocked by P1 (a criterion-domain must sit strictly below its system).
*)

From Stdlib Require Import Bool.

Section CantorGeneral.
  Context {X : Type}.

  (* f surjects onto the predicate space X->bool *)
  Definition surjective (f : X -> (X -> bool)) : Prop :=
    forall g : X -> bool, exists a : X, f a = g.

  (* The diagonal predicate, built to differ from every row of f *)
  Definition cantor_diagonal (f : X -> (X -> bool)) : X -> bool :=
    fun x => negb (f x x).

  Lemma no_bool_fixpoint : forall b : bool, b = negb b -> False.
  Proof. intros [|] H; discriminate. Qed.

  Lemma diagonal_differs_at_point :
    forall (f : X -> (X -> bool)) (a : X),
      f a = cantor_diagonal f -> f a a = negb (f a a).
  Proof.
    intros f a Heq.
    assert (Hpt : f a a = cantor_diagonal f a).
    { rewrite Heq. reflexivity. }
    unfold cantor_diagonal in Hpt. exact Hpt.
  Qed.

  (* No row of f equals the diagonal *)
  Theorem diagonal_not_in_image :
    forall (f : X -> (X -> bool)) (a : X), f a <> cantor_diagonal f.
  Proof.
    intros f a Heq.
    apply (no_bool_fixpoint (f a a)).
    apply diagonal_differs_at_point. exact Heq.
  Qed.

  (* The general Cantor theorem: no surjection X -> (X -> bool) *)
  Theorem cantor_no_surjection :
    forall f : X -> (X -> bool), ~ surjective f.
  Proof.
    intros f Hsurj.
    destruct (Hsurj (cantor_diagonal f)) as [a Ha].
    exact (diagonal_not_in_image f a Ha).
  Qed.

  (* Constructive strengthening: an explicit predicate missed by every row *)
  Theorem exists_predicate_unhit :
    forall f : X -> (X -> bool), exists g : X -> bool, forall a : X, f a <> g.
  Proof.
    intros f. exists (cantor_diagonal f). intros a. apply diagonal_not_in_image.
  Qed.

End CantorGeneral.

(** Book-facing capstone: no carrier surjects onto its own bool-power TYPE.
    This is the role-comparison statement ("no maximal cardinality"), NOT a
    completed power-set Element-object. *)
Theorem no_maximal_bool_power :
  forall (X : Type) (f : X -> (X -> bool)), ~ @surjective X f.
Proof. exact @cantor_no_surjection. Qed.
