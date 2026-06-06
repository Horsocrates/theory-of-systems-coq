(** * RegularElementFloor.v — regular languages as the Element FLOOR of computability
      Phase 3 of the Computer-Science branch.

      Regular languages are the lowest, most "Element" storey of the Chomsky hierarchy:
      membership is DECIDABLE (a terminating bool), and the class is CLOSED under the boolean
      operations (complement / intersection / union) — all by finite-state computation, 0 axioms.
      This is the positive Element-floor that BoundaryDecidability.v's ElementDrawn picks out:
      a regular language is an Element-drawn boundary (a finite automaton draws it).

      The role-limit step — NON-regular languages via the pumping lemma (a finite-memory /
      pigeonhole obstruction) — is the next file (Phase 3b).

    Cited, not duplicated: stdlib/Automata.v has the base DFA/NFA + run lemmas + complement.
    The increment here is the CLOSURE ALGEBRA (product construction for ∩ and ∪) and the
    Element-floor framing tying regular languages to the Phase-1 boundary.  (These could later
    merge into stdlib/Automata.v.)  Honest level: classical (methods); the contribution is the
    framing + the closure algebra + the link to Element/role-limit.

    Elements: alphabet symbols (Sigma), words (lists), automaton states (Q)
    Roles:    "accepted / rejected" = the STATUS a word acquires (accepting); a state = a
              role-position in finite memory (Status != Role)
    Rules:    delta (transition); reading the word left-to-right (L5 order, fold_left);
              finiteness of Q = finite actual memory (P4)

    ============ E/R/R разбор ============
      Rules (L5): delta — переход; слово читается СЛЕВА-НАПРАВО (L5-порядок, fold_left);
                  конечность Q = конечная АКТУАЛЬНАЯ память (P4).
      Roles (L4): «принято/отвергнуто» — СТАТУС слова (accepting); состояние = роль-позиция.
      Elements  : символы алфавита, слова (списки), состояния.
    ДИАГНОСТИКА (P4): регулярные языки = Element-ПОЛ вычислимости — принадлежность РАЗРЕШИМА
      (membership_decidable), класс ЗАМКНУТ под ¬/∩/∪ (булевы операции на конечных состояниях),
      всё терминирует, 0 аксиом.  Это нижний, самый Element-этаж иерархии Хомского; role-limit-шаг
      (нерегулярность через pumping = обструкция конечной памяти) — следующий файл.  Связь с
      BoundaryDecidability.v: регулярная принадлежность — Element-проведённая граница.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Bool.
Import ListNotations.

Section Regular.

  Context {Sigma : Type}.    (* the alphabet *)

  (** A DFA's dynamics: fold the transition over the word (L5: left-to-right). *)
  Definition run {Q : Type} (delta : Q -> Sigma -> Q) (q : Q) (w : list Sigma) : Q :=
    fold_left delta w q.

  Lemma run_app {Q} (delta : Q -> Sigma -> Q) : forall w1 w2 q,
    run delta q (w1 ++ w2) = run delta (run delta q w1) w2.
  Proof. intros w1 w2 q. unfold run. apply fold_left_app. Qed.

  Definition accepts {Q} (delta : Q -> Sigma -> Q) (acc : Q -> bool)
    (q0 : Q) (w : list Sigma) : bool := acc (run delta q0 w).

  (** ELEMENT FLOOR: membership in a regular language is DECIDABLE (a terminating bool). *)
  Lemma membership_decidable {Q} (delta : Q -> Sigma -> Q) (acc : Q -> bool) (q0 : Q) :
    forall w, {accepts delta acc q0 w = true} + {accepts delta acc q0 w = false}.
  Proof. intro w. destruct (accepts delta acc q0 w); [left | right]; reflexivity. Qed.

  (** CLOSURE under complement (flip the accepting states). *)
  Lemma complement_spec {Q} (delta : Q -> Sigma -> Q) (acc : Q -> bool) (q0 : Q) :
    forall w, accepts delta (fun q => negb (acc q)) q0 w = negb (accepts delta acc q0 w).
  Proof. intro w. unfold accepts. reflexivity. Qed.

  (* ----- CLOSURE under intersection / union via the product construction ----- *)
  Section Product.

    Context {Q1 Q2 : Type}.
    Variables (d1 : Q1 -> Sigma -> Q1) (d2 : Q2 -> Sigma -> Q2).

    Definition dprod (q : Q1 * Q2) (a : Sigma) : Q1 * Q2 :=
      let (x, y) := q in (d1 x a, d2 y a).

    Lemma run_prod : forall w q1 q2,
      run dprod (q1, q2) w = (run d1 q1 w, run d2 q2 w).
    Proof.
      induction w as [|a w IH]; intros q1 q2.
      - reflexivity.
      - simpl. apply IH.
    Qed.

    Variables (a1 : Q1 -> bool) (a2 : Q2 -> bool) (s1 : Q1) (s2 : Q2).

    Lemma intersection_spec : forall w,
      accepts dprod (fun q => let (x, y) := q in a1 x && a2 y) (s1, s2) w = true
      <-> accepts d1 a1 s1 w = true /\ accepts d2 a2 s2 w = true.
    Proof.
      intro w. unfold accepts. rewrite run_prod. simpl. apply andb_true_iff.
    Qed.

    Lemma union_spec : forall w,
      accepts dprod (fun q => let (x, y) := q in a1 x || a2 y) (s1, s2) w = true
      <-> accepts d1 a1 s1 w = true \/ accepts d2 a2 s2 w = true.
    Proof.
      intro w. unfold accepts. rewrite run_prod. simpl. apply orb_true_iff.
    Qed.

  End Product.

End Regular.

(* ----- Concrete: the parity DFA (even number of 1s) — finite memory, computed ----- *)

Definition parity_delta (q a : bool) : bool := xorb q a.
Definition parity_acc   (q : bool) : bool := negb q.   (* even parity = accept *)

Example parity_accepts_empty : accepts parity_delta parity_acc false [] = true.
Proof. reflexivity. Qed.

Example parity_rejects_one : accepts parity_delta parity_acc false [true] = false.
Proof. reflexivity. Qed.

Example parity_accepts_two : accepts parity_delta parity_acc false [true; true] = true.
Proof. reflexivity. Qed.

(** Element floor, summarised: regular membership is decidable and the class is closed under
    ¬ / ∩ / ∪ — all finite-state, 0 axioms.  In BoundaryDecidability.v terms, every regular
    language is an Element-drawn boundary.  The role-limit step (non-regularity via pumping) is
    Phase 3b. *)

Print Assumptions intersection_spec.
Print Assumptions membership_decidable.
