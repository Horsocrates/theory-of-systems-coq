(** * TarskiUndefinability.v — the LIMIT face: truth is not internally definable (Tarski) = Lawvere
      The deepest REACH of the one diagonal: the foundations of logic.  Tarski's undefinability of
      truth (1936) — no formal system with negation and self-reference can define its own truth
      predicate — is the SAME Lawvere diagonal, now at the level of sentences.  The Liar sentence G
      ("I am not true") is the diagonal witness; it forces tv G <-> ~ tv G.

      Chain (0 axioms):  LAWVERE → RECURSION → DIAGONAL LEMMA → TARSKI.
      The diagonal lemma (every sentence-transformer has a truth-fixed-point) follows from the
      (Leibniz) recursion theorem (cs/RecursionTheorem.v), which is Lawvere (cs/LawvereFixedPoint.v).

    ★★ HONEST SCOPE.  This is TARSKI's undefinability of TRUTH — the diagonal-lemma SIBLING of
    Gödel's first incompleteness, NOT a metamathematical incompleteness theorem about arithmetic
    (no arithmetisation of provability).  It says truth is a ROLE-LIMIT: "the truth of the whole" is
    not an internal Element-predicate of the system about itself.  This respects the project's
    deliberate avoidance of Gödel — it is about undefinability (a clean diagonal), not incompleteness.
    The Liar G is exactly Roles.v §XII's circular status (s = negb s) and the Liar of
    Architecture_of_Reasoning/ParadoxDissolution.v — now shown to BE the Lawvere diagonal.

    Honest level: Tarski 1936 is classical; the contribution is the unification
    (Tarski = Lawvere = recursion = the Liar), 0 axioms, machine-checked.

    Elements: sentences Sent; the truth value tv; negation neg; self-application app
    Roles:    an internal truth predicate Tr (the system's mirror-role of itself); the diagonal G
              (the Liar) = a witness-role of the limit; tv = a status-role of a sentence
    Rules:    the diagonal lemma (= Kleene recursion on sentences = Lawvere) gives self-reference;
              neg + Tr-adequacy force tv G <-> ~ tv G

    ============ E/R/R разбор ============
      Rules (L5): диагональная лемма (= рекурсия Клини на предложениях = Ловер) даёт само-ссылку;
                  neg + адекватность Tr → tv G <-> ~ tv G.
      Roles (L4): «внутренний предикат истины» Tr (роль-зеркало системы о себе); Лжец G —
                  роль-свидетель предела; tv = роль-статус предложения.
      Elements  : предложения Sent; истинностное значение tv; отрицание neg; само-применение app.
    ДИАГНОСТИКА (P4): самая глубокая грань-ПРЕДЕЛ — истина целого НЕ определима ВНУТРИ системы
      (Тарский), это role-limit; Лжец G = диагональный свидетель = Ловер при f=neg.  Та же диагональ,
      что Кантор/halting/Райс, у основания логики.  Честно: undefinability истины (чистая диагональ),
      НЕ неполнота арифметики — уважает анти-Гёделеву позицию проекта.  Вклад — унификация
      (Тарский = Ловер = рекурсия = Лжец из Roles §XII), 0 аксиом.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import cs.LawvereFixedPoint.
From ToS Require Import cs.RecursionTheorem.

(** A proposition equivalent to its own negation is absurd (constructive — the Liar core). *)
Lemma iff_not_self_absurd : forall P : Prop, (P <-> ~ P) -> False.
Proof.
  intros P [H1 H2]. assert (np : ~ P) by (intro p; exact (H1 p p)).
  exact (np (H2 np)).
Qed.

Section Tarski.

  Variable Sent : Type.
  Variable tv  : Sent -> Prop.        (* the (external) truth of a sentence *)
  Variable neg : Sent -> Sent.        (* negation *)
  Hypothesis neg_ok : forall S, tv (neg S) <-> ~ tv S.

  (** The DIAGONAL LEMMA follows from the (Leibniz) recursion theorem: every sentence-transformer
      has a truth-fixed-point. *)
  Lemma diag_from_recursion :
    (forall f : Sent -> Sent, exists e, f e = e) ->
    forall f : Sent -> Sent, exists G, tv G <-> tv (f G).
  Proof.
    intros Hrec f. destruct (Hrec f) as [G HG]. exists G. rewrite HG. tauto.
  Qed.

  (** ★ TARSKI: with negation and the diagonal lemma, no internal truth predicate exists.
      The Liar G := "neg (Tr G)" forces tv G <-> ~ tv G. *)
  Theorem tarski_no_truth_predicate :
    (forall f : Sent -> Sent, exists G, tv G <-> tv (f G)) ->
    ~ exists Tr : Sent -> Sent, forall S, tv (Tr S) <-> tv S.
  Proof.
    intros diag [Tr Hadq].
    destruct (diag (fun S => neg (Tr S))) as [G HG]. cbv beta in HG.
    (* HG : tv G <-> tv (neg (Tr G)) *)
    apply (iff_not_self_absurd (tv G)). split.
    - intro Hg. intro Hg'.
      pose proof (proj1 HG Hg) as HnegTr.                 (* tv (neg (Tr G)) *)
      pose proof (proj1 (neg_ok (Tr G)) HnegTr) as HnTr.  (* ~ tv (Tr G) *)
      pose proof (proj2 (Hadq G) Hg') as HTr.             (* tv (Tr G) *)
      exact (HnTr HTr).
    - intro Hng.
      apply (proj2 HG). apply (proj2 (neg_ok (Tr G))).
      intro HTr. apply Hng. apply (proj1 (Hadq G)). exact HTr.
  Qed.

End Tarski.

(** ★ THE CHAIN: LAWVERE → RECURSION → DIAGONAL LEMMA → TARSKI.  For any universal sentence system
    with negation, truth is undefinable internally — the foundations-of-logic face of the one
    diagonal, derived from the same root. *)
Theorem tarski_from_lawvere :
  forall (Sent : Type) (tv : Sent -> Prop) (neg : Sent -> Sent)
         (app : Sent -> (Sent -> Sent)),
    point_surjective app ->
    (forall S, tv (neg S) <-> ~ tv S) ->
    ~ exists Tr : Sent -> Sent, forall S, tv (Tr S) <-> tv S.
Proof.
  intros Sent tv neg app Hsurj Hneg.
  apply (tarski_no_truth_predicate Sent tv neg Hneg).
  apply (diag_from_recursion Sent tv).
  apply (kleene_recursion_from_lawvere Sent app Hsurj).
Qed.

(** So Cantor (set), halting & Rice (computation), and Tarski (truth) are ONE Lawvere diagonal;
    the Liar G here is Roles.v §XII's s = negb s.  The negative limits of self-reference across
    sets, programs and logic share the single root cs/LawvereFixedPoint.lawvere_fixed_point. *)

Print Assumptions tarski_no_truth_predicate.
Print Assumptions tarski_from_lawvere.
