(** * DecidableKonig.v — König's lemma without choice, on the DECIDABLE side: the path-construction of the
       canonical weak-choice theorem is choice-free once infiniteness is decidable.  König's lemma (a
       finitely-branching infinite tree has an infinite path) is the textbook "weak choice" result (weak
       König's lemma WKL in reverse mathematics).  This localizes its choice-content: GIVEN a DECIDABLE
       infiniteness test and the finitely-branching pigeonhole step, the infinite path is built
       DETERMINISTICALLY (always the least infinite child, via first_witness) — 0 axioms, no AC/DC.

    -- What is assumed vs proven (the honest localization) --
      A tree on ℕ-encoded nodes: children : ℕ → list ℕ (FINITELY branching), and inf_b : ℕ → bool, a DECIDABLE
      "this node has an infinite branch through it".  The one assumed fact is the König / pigeonhole step:
        konig_step : inf_b x = true → ∃ c ∈ children x, inf_b c = true
      (an infinite node has an infinite child — for finite branching this is the classical pigeonhole, the
      place WKL/choice would enter).  GIVEN it, everything else is deterministic and axiom-free:
        next x := the FIRST child c with inf_b c = true (first_witness over the finite child list);
        path   := the trajectory of next from an infinite root;
        path_inf : every path node is infinite;  path_edge : each path node is a child of the previous.
      So the infinite path needs NO further choice — the choice-content of König is exactly the pigeonhole
      step + the (un)decidability of inf, not the path extraction.

    -- The boundary --
      Drop decidability of inf (the genuine case: "infinite subtree" is a Π predicate, undecidable like
      BolzanoWeierstrass's "infinitely-many-in") and the half/child cannot be chosen deterministically — WKL /
      dependent choice is the price (settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v; cf.
      analysis/BolzanoWeierstrass.v paying classic).  Decidable inf + pigeonhole ⟹ path is free.

    Elements: the finitely-branching tree (children); the decidable infiniteness flag inf_b; ℕ-encoded nodes.
    Roles:    the infinite path = a role-limit (the unfinished branch); next x = the least infinite child, a
              Role assigned BY THE RULE (first qualifying), not freely; each finite stage is actual (P4).
    Rules:    konig_step + decidable inf_b ⟹ first_witness deterministically picks the child ⟹ a path with
              no choice; the order on children constitutes "first/least infinite child".

    ============ E/R/R разбор ============
      Rules (L5): konig-шаг + разрешимый inf_b ⟹ first_witness берёт ПЕРВОГО бесконечного ребёнка (порядок = «первый»).
      Roles (L4): путь = role-limit (незавершённая ветвь); next = наименьший бесконечный ребёнок (роль по правилу).
      Elements  : конечно-ветвящееся дерево children; флаг inf_b; узлы-ℕ; каждая конечная стадия пути актуальна.
    ДИАГНОСТИКА (P4): König Element-сторона при РАЗРЕШИМОМ inf (детерминированный путь, 0 акс); классическое содержание
      (pigeonhole) локализовано в гипотезе konig_step. Без разрешимости — WKL/выбор (role-limit; BW платит classic за то же).
      Продолжение нити «выбор без AC»: first_witness (конечный выбор) ⟹ König-путь. Уровень: `новая теорема` (decidable König) + `синтез`.

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (builds on cs.DecidableSelection)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List PeanoNat.
From ToS Require Import cs.DecidableSelection.
Import ListNotations.

Section Konig.

  Variable children : nat -> list nat.        (* finitely branching: a list of children per node *)
  Variable inf_b : nat -> bool.               (* DECIDABLE "node lies on an infinite branch" *)

  (** The König / pigeonhole step (the classical content, assumed): an infinite node has an infinite child. *)
  Hypothesis konig_step : forall x, inf_b x = true -> exists c, In c (children x) /\ inf_b c = true.

  (** The deterministic successor: the FIRST infinite child (least by child-list order). *)
  Definition next (x : nat) : nat :=
    match first_witness nat inf_b (children x) with Some c => c | None => x end.

  (** ★ Under the König step, next picks a genuine infinite child. *)
  Lemma next_spec : forall x, inf_b x = true -> In (next x) (children x) /\ inf_b (next x) = true.
  Proof.
    intros x Hx. unfold next.
    destruct (first_witness nat inf_b (children x)) eqn:E.
    - exact (first_witness_sound nat inf_b (children x) n E).
    - exfalso. apply (first_witness_complete nat inf_b (children x) (konig_step x Hx)). exact E.
  Qed.

  (** The path: the trajectory of next from a root. *)
  Fixpoint path (root : nat) (n : nat) : nat :=
    match n with O => root | S k => next (path root k) end.

  (** ★ Every node on the path is infinite (induction via the König step). *)
  Lemma path_inf : forall root, inf_b root = true -> forall n, inf_b (path root n) = true.
  Proof.
    intros root Hr. induction n as [| k IH]; simpl.
    - exact Hr.
    - exact (proj2 (next_spec (path root k) IH)).
  Qed.

  (** ★★ KÖNIG'S LEMMA (decidable, deterministic, 0 axioms): from an infinite root, an infinite path whose
      every step is a real child edge — no AC, no DC, no WKL. *)
  Theorem path_edge : forall root, inf_b root = true ->
    forall n, In (path root (S n)) (children (path root n)).
  Proof.
    intros root Hr n. simpl. exact (proj1 (next_spec (path root n) (path_inf root Hr n))).
  Qed.

  (** ★ The path is UNIQUE / deterministic: the rule pins THE branch (next is a function; no choice). *)
  Lemma path_unique : forall root (f : nat -> nat),
    f O = root -> (forall n, f (S n) = next (f n)) -> forall n, f n = path root n.
  Proof.
    intros root f H0 Hstep. induction n as [| k IH]; simpl.
    - exact H0.
    - rewrite Hstep, IH. reflexivity.
  Qed.

End Konig.

(* ===================================================================== *)
(*  Concrete: the full binary tree (every node infinite) — a computed path *)
(* ===================================================================== *)

Definition bin_children (x : nat) : list nat := [2 * x + 1; 2 * x + 2].

(** Every node is infinite, and the König step is the first child. *)
Lemma bin_konig_step : forall x, (fun _ : nat => true) x = true ->
  exists c, In c (bin_children x) /\ (fun _ : nat => true) c = true.
Proof. intros x _. exists (2 * x + 1). split; [ left; reflexivity | reflexivity ]. Qed.

(** ★ The deterministic path from the root follows the first (left) child — computed. *)
Example bin_path_values :
  path bin_children (fun _ => true) 0 1 = 1 /\
  path bin_children (fun _ => true) 0 2 = 3 /\
  path bin_children (fun _ => true) 0 3 = 7.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ★ ...and every step is a genuine child edge (König's lemma instantiated, 0 axioms). *)
Example bin_path_edge : forall n,
  In (path bin_children (fun _ => true) 0 (S n)) (bin_children (path bin_children (fun _ => true) 0 n)).
Proof. apply (path_edge bin_children (fun _ => true) bin_konig_step 0). reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** König's lemma without choice (decidable side):
      (next)       the least infinite child is selected deterministically (first_witness, 0 axioms);
      (path_inf)   every node on the trajectory stays infinite (via the assumed pigeonhole step);
      (path_edge)  König's lemma — an infinite root yields an infinite path of real child edges, no AC/DC/WKL;
      (path_unique)the rule pins THE branch — deterministic, no choice among children.
    So the path-construction of the canonical weak-choice theorem is Element-side once infiniteness is
    DECIDABLE: the choice-content of König is exactly the pigeonhole step + the (un)decidability of inf, not
    the extraction.  Undecidable inf ⟹ WKL/DC is the price (analysis/BolzanoWeierstrass.v pays classic for the
    same reason).  Continues vein B: first_witness (finite selection) ⟹ the König path.  Level: a decidable
    König (new in the repo) + the AC-price localization. *)
Theorem decidable_konig :
  (forall children inf_b,
     (forall x, inf_b x = true -> exists c, In c (children x) /\ inf_b c = true) ->
     forall root, inf_b root = true ->
     forall n, In (path children inf_b root (S n)) (children (path children inf_b root n)))
  /\ (forall children inf_b root (f : nat -> nat),
        f O = root -> (forall n, f (S n) = next children inf_b (f n)) ->
        forall n, f n = path children inf_b root n).
Proof.
  split.
  - intros children inf_b Hstep root Hr n. exact (path_edge children inf_b Hstep root Hr n).
  - intros children inf_b root f H0 Hstep n. exact (path_unique children inf_b root f H0 Hstep n).
Qed.
