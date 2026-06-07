(** * CountableSelectionFree.v — COUNTABLE choice without AC: the structured-infinite middle between finite
       selection (free) and the Axiom of Choice (refused).  DecidableSelection.v handles the FINITE case
       (first_witness over a list); this adds the COUNTABLE case: for a DECIDABLE predicate over ℕ, the LEAST
       witness is a canonical, deterministic, axiom-free selector (nat_least), and hence COUNTABLE CHOICE FOR
       DECIDABLE FAMILIES is FREE (0 axioms) — no Axiom of Choice, no countable choice axiom (ACω).

    -- The two results --
      (1) nat_least: a decidable P : ℕ → bool with some witness has a LEAST witness — {n | P n /\ ∀ m<n, ¬P m}.
          This is ℕ's canonical choice function: the order + the decidable test RESOLVE the choice (L5 = the
          least = the first qualifying), with no oracle.  (Constructive ε for ℕ; 0 axioms.)
      (2) dec_family_choice: a family Q : ℕ → ℕ → bool of decidably-nonempty sets has a CHOICE FUNCTION
          i ↦ (least n with Q i n) — correct (Q i (choice i) = true) and CANONICAL (it is the MINIMAL valid
          choice: any other valid g has choice i ≤ g i).  Countable choice, deterministic, 0 axioms.

    -- The honest boundary (cited, not duplicated) --
      The SAME selection over a family with NO decidable membership test (arbitrary nonempty sets) is exactly
      the Axiom of Choice — the completed infinite choice graph P4 forbids: settheory/ChoicePriceMap.v,
      foundation/P4ProhibitsAC.v.  So: countable + DECIDABLE ⟹ free; non-decidable / uncountable ⟹ AC.
      Level: the least-witness is constructive ε (standard); the contribution is the countable-choice-for-
      decidable-families packaging, its canonicity (minimal valid choice), and the finite→countable bridge of
      vein B (argmax-by-index / DecidableSelection.first_witness extended off finite carriers).

    Elements: ℕ (the countable carrier); the decidable predicate P / family Q.
    Roles:    the LEAST witness = a Role assigned BY THE RULE (test + order), not by free choice; the choice
              function = a role-assigner; "least" makes it canonical (one rule-selection, not many).
    Rules:    the decidable test + the ℕ-order RESOLVE the choice (L5: least = first qualifying); decidable +
              countable ⟹ selection is free (0 axioms); non-decidable ⟹ AC (the boundary).

    ============ E/R/R разбор ============
      Rules (L5): разрешимый тест P / семейство Q + порядок ℕ РАЗРЕШАЮТ выбор; наименьший свидетель = первый прошедший.
      Roles (L4): наименьший свидетель / функция выбора — РОЛЬ, назначаемая правилом; «наименьший» = канонично (не свобода).
      Elements  : ℕ — счётный носитель; разрешимый предикат/семейство.
    ДИАГНОСТИКА (P4): счётный РАЗРЕШИМЫЙ выбор — Element-сторона: детерминирован, канонический наименьший, 0 аксиом
      (nat_least, dec_family_choice). Расширяет DecidableSelection с конечного (first_witness) на счётное. Неразрешимое
      семейство ⟹ AC = role-limit (завершённый choice-граф, P4-запрещён; ChoicePriceMap/P4ProhibitsAC). Уровень: `синтез`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (self-contained: ConstructiveEpsilon / PeanoNat / Bool / Arith)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ConstructiveEpsilon PeanoNat Bool Arith Lia.

(* ===================================================================== *)
(*  ★ ℕ's canonical selector: the LEAST witness of a decidable predicate   *)
(* ===================================================================== *)

(** ★ For a decidable P : ℕ → bool with some witness, the LEAST witness exists — a canonical, deterministic,
    axiom-free choice on ℕ.  The order + the decidable test resolve the choice (no oracle). *)
Lemma nat_least : forall (P : nat -> bool),
  (exists n, P n = true) ->
  {n : nat | P n = true /\ forall m, m < n -> P m = false}.
Proof.
  intros P Hex.
  destruct (epsilon_smallest (fun n => P n = true)
              (fun n => bool_dec (P n) true) Hex) as [n [Hn Hsmall]].
  exists n. split; [ exact Hn | ].
  intros m Hm. destruct (P m) eqn:E; [ | reflexivity ].
  exfalso. specialize (Hsmall m E). lia.
Qed.

(* ===================================================================== *)
(*  ★★ Countable choice for DECIDABLE families is FREE (0 axioms)          *)
(* ===================================================================== *)

(** The canonical choice function for a decidably-nonempty family: i ↦ least n with Q i n = true. *)
Definition dec_family_choice (Q : nat -> nat -> bool)
  (Hne : forall i, exists n, Q i n = true) (i : nat) : nat :=
  proj1_sig (nat_least (Q i) (Hne i)).

(** ★★ The choice function is CORRECT: it lands in each set. Countable choice, no axiom. *)
Lemma dec_family_choice_correct : forall Q Hne i,
  Q i (dec_family_choice Q Hne i) = true.
Proof.
  intros Q Hne i. unfold dec_family_choice.
  exact (proj1 (proj2_sig (nat_least (Q i) (Hne i)))).
Qed.

(** Each value is the LEAST witness of its set. *)
Lemma dec_family_choice_least : forall Q Hne i m,
  m < dec_family_choice Q Hne i -> Q i m = false.
Proof.
  intros Q Hne i m Hm. unfold dec_family_choice in *.
  exact (proj2 (proj2_sig (nat_least (Q i) (Hne i))) m Hm).
Qed.

(** ★★ CANONICITY (the "without free choice" punch): the rule's choice is the MINIMAL valid one — any other
    valid choice function g has dec_family_choice i ≤ g i.  So the selection is DETERMINED by the rule (the
    least), not freely chosen — there is exactly one rule-selection. *)
Lemma dec_family_choice_canonical : forall Q Hne (g : nat -> nat) i,
  Q i (g i) = true -> dec_family_choice Q Hne i <= g i.
Proof.
  intros Q Hne g i Hg.
  destruct (le_lt_dec (dec_family_choice Q Hne i) (g i)) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. pose proof (dec_family_choice_least Q Hne i (g i) Hlt) as Hf.
  rewrite Hg in Hf. discriminate.
Qed.

(* ===================================================================== *)
(*  Concrete: the family {n : n ≥ i} — choice i is the least n ≥ i        *)
(* ===================================================================== *)

(** The family Q i = {n : i ≤ n} is decidably nonempty (i itself works). *)
Lemma geq_family_nonempty : forall i, exists n, Nat.leb i n = true.
Proof. intro i. exists i. apply Nat.leb_refl. Qed.

(** Its canonical choice lands in each set (the least n ≥ i — here i). *)
Example geq_family_choice_correct : forall i,
  Nat.leb i (dec_family_choice (fun i n => Nat.leb i n) geq_family_nonempty i) = true.
Proof. intro i. apply dec_family_choice_correct. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Countable selection without choice:
      (selector)   nat_least — a decidable predicate over ℕ has a canonical LEAST witness (0 axioms);
      (countable)  dec_family_choice_correct — countable choice for DECIDABLE families is free (no AC, no ACω);
      (canonical)  dec_family_choice_canonical — the rule's choice is the MINIMAL valid one: deterministic,
                   not free — there is one rule-selection, fixed by the order + test.
    So selection over a COUNTABLE carrier with a DECIDABLE test is Element-side: deterministic, canonical,
    axiom-free — extending DecidableSelection.first_witness from finite lists to ℕ.  The boundary is exactly
    the non-decidable / uncountable family, where selection becomes the Axiom of Choice — the completed choice
    graph P4 refuses (settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v).  Level: synthesis — constructive
    ε is standard; the contribution is the decidable-countable-choice packaging, its canonicity, and the
    finite→countable bridge of vein B. *)
Theorem countable_selection_free :
  inhabited (forall (P : nat -> bool), (exists n, P n = true) ->
     {n : nat | P n = true /\ forall m, m < n -> P m = false})
  /\ (forall (Q : nat -> nat -> bool) (Hne : forall i, exists n, Q i n = true) i,
        Q i (dec_family_choice Q Hne i) = true)
  /\ (forall (Q : nat -> nat -> bool) (Hne : forall i, exists n, Q i n = true) (g : nat -> nat) i,
        Q i (g i) = true -> dec_family_choice Q Hne i <= g i).
Proof.
  split; [ exact (inhabits nat_least) | ].
  split; [ exact dec_family_choice_correct | exact dec_family_choice_canonical ].
Qed.
