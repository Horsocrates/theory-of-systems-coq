(** * SelectionWithoutChoiceSynthesis.v — the SYNTHESIS of vein B: the choice ladder.  Selection over a
       carrier is AXIOM-FREE exactly when a DECIDABLE test + an ORDER (a Rule, L5) resolve it; the Axiom of
       Choice / Dependent Choice / weak König's lemma is the price ONLY at the undecidable / unordered
       boundary.  This bundles the thread's four free levels and states the unifying thesis.

    -- The choice ladder (each free level a machine-checked file of this thread) --
      Finite        — decidable_list_choice (DecidableSelection): a decidable existential over a list yields a
                      computable witness — first_witness, 0 axioms.
      CountableChoice— nat_least / dec_family_choice (CountableSelectionFree): the canonical LEAST witness over
                      ℕ; countable choice for decidable families is free, 0 axioms.
      CountableDC   — dc_chain (CountableDependentChoiceFree): the least-successor trajectory of a decidable
                      total relation is an R-chain — dependent choice with no DC, 0 axioms.
      KonigPath     — path (DecidableKonig): given decidable infiniteness + the pigeonhole step, the infinite
                      path is built deterministically — König / WKL on the decidable side, 0 axioms.
      UnstructuredBoundary — the SAME selection over an unordered family with no decidable test = the Axiom of
                      Choice / DC / WKL, the P4-forbidden completed choice graph (ChoicePriceMap / P4ProhibitsAC;
                      analysis/BolzanoWeierstrass.v pays classic for its undecidable bisection criterion).

    -- The unifying thesis (the genuine synthesis) --
      All four free levels reduce to ONE pattern: a decidable test over a well-ordered carrier picks the LEAST
      qualifying element (nat_least / first_witness), and the higher levels ITERATE it (dependent choice =
      iterate least-successor; König = iterate first-infinite-child).  The axiom-price is exactly the structure
      deficit: undecidable test or unordered carrier.  So selection, like deciding, is Element-drawable exactly
      when a terminating rule draws it.

    -- The cross-thread link (sharp) --
      This boundary is the SAME line as the decidability stratification of RoleLimitTaxonomy (H48): there,
      "is-it-an-Element?" is decidable on the algebraic stratum, undecidable at the diagonal; HERE, "can-I-
      select?" is free with a decidable rule, priced without one.  Selection-freedom (vein B) ⟺ decidability —
      pillar B and the finitization boundary (H1) are one boundary seen from two sides.

    WHAT THE REPO HAS (surveyed): DecidableSelection, CountableSelectionFree (H49), CountableDependentChoiceFree
    (H50), DecidableKonig (H51), ChoicePriceMap, P4ProhibitsAC, StructuralWellOrders, BolzanoWeierstrass.
    GAP: the unifying ladder + the selection-freedom ⟺ decidability thesis.  This adds it.

    ============ E/R/R разбор ============
      Elements : уровни выбора (конечный/счётный/зависимый/König/граница); флаг axiom-free.
      Roles    : свободный уровень = выбор, разрешённый ПРАВИЛОМ (тест+порядок); граница = AC/DC/WKL (role-limit).
      Rules    : разрешимый тест + порядок ⟹ 0 акс (наименьший = первый); неразрешимое/неупорядоченное ⟹ цена.
      ДИАГНОСТИКА (P4): свобода выбора ⟺ РАЗРЕШИМОСТЬ — та же линия, что H48/H1. Четыре уровня = итерации наименьшего
      селектора (nat_least/first_witness); AC — цена структурного дефицита. Уровень: `синтез` (связка нити + тезис, без новой математики).

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (bundles DecidableSelection + H49 + H50 + H51)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Bool.
From ToS Require Import cs.DecidableSelection.
From ToS Require Import cs.CountableSelectionFree.
From ToS Require Import cs.CountableDependentChoiceFree.
From ToS Require Import cs.DecidableKonig.
Import ListNotations.

(* ===================================================================== *)
(*  The choice ladder and its axiom cost                                   *)
(* ===================================================================== *)

Inductive SelectionLevel :=
  | Finite | CountableChoice | CountableDC | KonigPath | UnstructuredBoundary.

(** Free (0 axioms) on every structured level; priced (AC/DC/WKL) only at the unstructured boundary. *)
Definition axiom_free (s : SelectionLevel) : bool :=
  match s with UnstructuredBoundary => false | _ => true end.

Definition all_levels : list SelectionLevel :=
  [Finite; CountableChoice; CountableDC; KonigPath; UnstructuredBoundary].

Definition count_free : nat := length (filter axiom_free all_levels).
Definition count_priced : nat := length (filter (fun s => negb (axiom_free s)) all_levels).

(** ★ FOUR structured levels are axiom-free; ONE (unstructured) is the AC/DC/WKL boundary. *)
Lemma count_free_4 : count_free = 4%nat.
Proof. reflexivity. Qed.

Lemma count_priced_1 : count_priced = 1%nat.
Proof. reflexivity. Qed.

Lemma ladder_total : (count_free + count_priced)%nat = length all_levels.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The four free levels — each a real theorem of the thread               *)
(* ===================================================================== *)

(** ★ FINITE: a decidable existential over a list yields a computable witness (no axiom). *)
Lemma level_finite :
  inhabited (forall (A : Type) (P : A -> bool) (l : list A),
    {x | In x l /\ P x = true} + {forall x, In x l -> P x = false}).
Proof. exact (inhabits decidable_list_choice). Qed.

(** ★ COUNTABLE CHOICE: ℕ's canonical least-witness selector (no axiom). *)
Lemma level_countable_choice :
  inhabited (forall (P : nat -> bool), (exists n, P n = true) ->
    {n : nat | P n = true /\ forall m, m < n -> P m = false}).
Proof. exact (inhabits nat_least). Qed.

(** ★ COUNTABLE DEPENDENT CHOICE: the least-successor chain of a decidable total relation is an R-chain. *)
Lemma level_countable_dc :
  forall (R : nat -> nat -> bool) (Htot : forall x, exists y, R x y = true) x0 n,
    R (dc_chain R Htot x0 n) (dc_chain R Htot x0 (S n)) = true.
Proof. exact dc_chain_step. Qed.

(** ★ KÖNIG: an infinite root yields an infinite path of real child edges (decidable side, no WKL). *)
Lemma level_konig :
  forall (children : nat -> list nat) (inf_b : nat -> bool),
    (forall x, inf_b x = true -> exists c, In c (children x) /\ inf_b c = true) ->
    forall root, inf_b root = true ->
    forall n, In (path children inf_b root (S n)) (children (path children inf_b root n)).
Proof. exact path_edge. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The choice ladder, synthesized:
      (finite)      decidable existential over a list ⟹ computable witness;
      (countable)   ℕ's canonical least-witness selector ⟹ countable choice for decidable families is free;
      (dependent)   least-successor chain of a decidable total relation ⟹ dependent choice with no DC;
      (König)       decidable infiniteness + pigeonhole ⟹ an infinite path, no WKL;
      (ladder)      4 structured levels are axiom-free; 1 (unstructured) is the AC/DC/WKL boundary.
    Unifying thesis: selection is axiom-free EXACTLY when a decidable test + an order (a Rule) resolve it —
    the four levels all iterate the canonical least selector (nat_least / first_witness), and AC is the price
    of the structure deficit (undecidable test / unordered carrier).  This is the SAME boundary as the
    decidability stratification of RoleLimitTaxonomy (H48): selection-freedom ⟺ decidability — vein B and the
    finitization boundary are one line, two sides.  Honest boundary: ChoicePriceMap / P4ProhibitsAC (AC) and
    BolzanoWeierstrass (classic for the undecidable bisection).  Level: synthesis — no new mathematics; the
    thread's results bundled under the selection-freedom ⟺ decidability thesis. *)
Theorem selection_without_choice_synthesis :
  inhabited (forall (A : Type) (P : A -> bool) (l : list A),
    {x | In x l /\ P x = true} + {forall x, In x l -> P x = false})
  /\ inhabited (forall (P : nat -> bool), (exists n, P n = true) ->
       {n : nat | P n = true /\ forall m, m < n -> P m = false})
  /\ (forall (Q : nat -> nat -> bool) (Hne : forall i, exists n, Q i n = true) i,
        Q i (dec_family_choice Q Hne i) = true)
  /\ (forall (R : nat -> nat -> bool) (Htot : forall x, exists y, R x y = true) x0 n,
        R (dc_chain R Htot x0 n) (dc_chain R Htot x0 (S n)) = true)
  /\ (forall (children : nat -> list nat) (inf_b : nat -> bool),
        (forall x, inf_b x = true -> exists c, In c (children x) /\ inf_b c = true) ->
        forall root, inf_b root = true ->
        forall n, In (path children inf_b root (S n)) (children (path children inf_b root n)))
  /\ count_free = 4%nat /\ count_priced = 1%nat.
Proof.
  split; [ exact level_finite | ].
  split; [ exact level_countable_choice | ].
  split; [ exact dec_family_choice_correct | ].
  split; [ exact dc_chain_step | ].
  split; [ exact path_edge | ].
  split; [ exact count_free_4 | exact count_priced_1 ].
Qed.
