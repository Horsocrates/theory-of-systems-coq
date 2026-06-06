(** * DecidableSelection.v — deterministic selection WITHOUT choice (the Element side of choice)
      Phase 2 of the Computer-Science branch.  The positive complement of BoundaryDecidability.v:
      where a "choice" is resolved by a DECIDABLE rule + an order, selection is deterministic,
      computable, and axiom-free — no Axiom of Choice (AC), no Dependent Choice (DC).

      This distils the project's "constructive signature" (vein B): argmax-by-index (EVT_idx.v),
      the DC→Fixpoint move (analysis/BolzanoWeierstrass.v), and L5's first-qualifying-position
      (L5Resolution.v) all reduce to TWO axiom-free patterns:

      (A) FINITE — first_witness: a decidable predicate over an ordered finite carrier yields the
          FIRST qualifying element, deterministically.  Punchline `decidable_list_choice`: a
          decidable existential over a list gives a COMPUTABLE witness — a Skolem/choice function
          with NO axiom (the L4_witness/L5 content, not AC).

      (B) INFINITE — trajectory: a DETERMINISTIC step rule yields a unique infinite sequence with
          NO Dependent Choice.  `trajectory_unique` (the rule pins down THE sequence) and
          `trajectory_is_R_chain` (a deterministic refinement of a relation R gives an R-chain
          without DC) — the BolzanoWeierstrass `bw_step`/`bw_iter` pattern, abstracted.

    Honest boundary (cited, not duplicated): the SAME selection over an UNORDERED family with no
    decidable test is exactly AC (finite-front survives; the completed infinite choice graph is the
    P4-forbidden role-limit) — see settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v.
    Honest level: algorithms are standard (Bishop); the contribution is the systematic, axiom-free
    packaging + the explicit localization of where AC/DC is and isn't needed.

    Elements: finite carriers (lists), states, candidates
    Roles:    the selected witness / chosen successor = a ROLE assigned BY THE RULE (L5 picks the
              FIRST), not by free choice; the selector is a role-assigner (Status != Role)
    Rules:    the decidable test P / the deterministic step — they RESOLVE the choice (L5 order
              constitutes "first")

    ============ E/R/R разбор ============
      Rules (L5): разрешимый тест P / детерминированный шаг step РАЗРЕШАЮТ выбор; L5-порядок
                  конституирует «первый» (first_witness берёт первый прошедший тест).
      Roles (L4): «выбранный свидетель» / «выбранный преемник» — РОЛЬ, назначаемая правилом, а не
                  свободным выбором.  Селектор = назначатель роли.
      Elements  : конечные носители (списки), состояния, кандидаты.
    ДИАГНОСТИКА (P4): где выбор разрешён ПРАВИЛОМ + ПОРЯДКОМ — Element-сторона: детерминированно,
      вычислимо, 0 аксиом (first_witness, decidable_list_choice, trajectory).  Где НЕ разрешён
      (произвольное бесконечное семейство, без теста/порядка) — AC/DC = role-limit (завершённая
      choice-функция, P4-запрещённая).  Это позитивное дополнение BoundaryDecidability.v: Element-
      сторона «проведения выбора».  Дистиллят EVT_idx / BolzanoWeierstrass / L5_resolve.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

(* ===================================================================== *)
(*  PART A — FINITE: first_witness (deterministic, no AC)                  *)
(* ===================================================================== *)

Section FirstWitness.

  Variable A : Type.
  Variable P : A -> bool.            (* a DECIDABLE predicate *)

  (** The FIRST element of a list passing the test — deterministic, computable. *)
  Fixpoint first_witness (l : list A) : option A :=
    match l with
    | []      => None
    | x :: xs => if P x then Some x else first_witness xs
    end.

  (** Sound: the selected element is really in the list and passes the test. *)
  Lemma first_witness_sound : forall l x,
    first_witness l = Some x -> In x l /\ P x = true.
  Proof.
    induction l as [|a xs IH]; simpl; intros x H.
    - discriminate.
    - destruct (P a) eqn:Ea.
      + injection H as H. subst x. split; [left; reflexivity | exact Ea].
      + apply IH in H. destruct H as [Hin HP]. split; [right; exact Hin | exact HP].
  Qed.

  (** Complete: if a witness exists, the selector finds one. *)
  Lemma first_witness_complete : forall l,
    (exists x, In x l /\ P x = true) -> first_witness l <> None.
  Proof.
    induction l as [|a xs IH]; intros [x [Hin Hx]]; simpl.
    - destruct Hin.
    - destruct (P a) eqn:Ea.
      + discriminate.
      + destruct Hin as [Heq | Hin'].
        * subst x. rewrite Ea in Hx. discriminate.
        * apply IH. exists x. split; assumption.
  Qed.

  (** Deterministic = FIRST: the selected element is the leftmost qualifying one. *)
  Lemma first_witness_first : forall l1 x l2,
    (forall y, In y l1 -> P y = false) ->
    P x = true ->
    first_witness (l1 ++ x :: l2) = Some x.
  Proof.
    induction l1 as [|a l1' IH]; intros x l2 Hl1 Hx; simpl.
    - rewrite Hx. reflexivity.
    - assert (P a = false) as Ea by (apply Hl1; left; reflexivity).
      rewrite Ea. apply IH; [intros y Hy; apply Hl1; right; exact Hy | exact Hx].
  Qed.

  (** ★ THE PUNCHLINE: a decidable existential over a finite carrier yields a COMPUTABLE
      witness — a choice/Skolem function with NO axiom (this is L4_witness/L5, NOT AC). *)
  Lemma decidable_list_choice : forall l,
    {x | In x l /\ P x = true} + {forall x, In x l -> P x = false}.
  Proof.
    intro l. destruct (first_witness l) eqn:E.
    - left. exists a. apply first_witness_sound. exact E.
    - right. intros x Hin. destruct (P x) eqn:Ex.
      + exfalso. apply (first_witness_complete l).
        * exists x. split; [exact Hin | exact Ex].
        * exact E.
      + reflexivity.
  Qed.

End FirstWitness.

(** Concrete: the first element exceeding 5 in [3;7;2;9] is 7 — deterministic, computed. *)
Example first_gt5 :
  first_witness nat (fun n => Nat.ltb 5 n) [3;7;2;9] = Some 7.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — INFINITE: deterministic descent (no Dependent Choice)        *)
(* ===================================================================== *)

Section DeterministicDescent.

  Variable State : Type.
  Variable step : State -> State.    (* a DETERMINISTIC rule (the choice already resolved) *)

  Fixpoint trajectory (n : nat) (s : State) : State :=
    match n with O => s | S k => step (trajectory k s) end.

  (** The deterministic rule pins down THE unique sequence — no choice among successors,
      hence no Dependent Choice. *)
  Lemma trajectory_unique : forall (f : nat -> State) (s : State),
    f O = s ->
    (forall n, f (S n) = step (f n)) ->
    forall n, f n = trajectory n s.
  Proof.
    intros f s H0 Hstep. induction n as [|k IH].
    - simpl. exact H0.
    - simpl. rewrite Hstep, IH. reflexivity.
  Qed.

  (** DC-free chain: a deterministic refinement of a relation R yields an R-chain with no
      Dependent Choice (the BolzanoWeierstrass bw_step/bw_iter pattern, abstracted). *)
  Variable R : State -> State -> Prop.
  Hypothesis step_refines : forall s, R s (step s).

  Lemma trajectory_is_R_chain : forall n s,
    R (trajectory n s) (trajectory (S n) s).
  Proof. intros n s. simpl. apply step_refines. Qed.

End DeterministicDescent.

(* ===================================================================== *)
(*  SYNTHESIS                                                              *)
(* ===================================================================== *)

(** Element-side of choice (this file): decidable rule + order ⟹ deterministic, computable,
    0-axiom selection — finite (first_witness) and infinite (trajectory).
    role-limit-side (NOT here): an unordered family with no decidable test ⟹ AC/DC, whose
    completed choice graph P4 forbids (settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v).
    Together with BoundaryDecidability.v: choosing, like deciding, is Element-drawable exactly
    when a terminating rule draws it. *)

Print Assumptions decidable_list_choice.
Print Assumptions trajectory_is_R_chain.
