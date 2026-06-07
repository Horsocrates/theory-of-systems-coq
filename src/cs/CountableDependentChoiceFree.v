(** * CountableDependentChoiceFree.v — DEPENDENT choice without DC: the dependent-choice analog of
       CountableSelectionFree.  H49 (CountableSelectionFree) showed countable CHOICE for decidable families is
       free; this shows countable DEPENDENT CHOICE for decidable TOTAL relations on ℕ is free — an infinite
       R-chain built with NO Dependent Choice axiom, because at each step the LEAST valid successor (nat_least)
       makes the step DETERMINISTIC.

    -- The result --
      Given a relation R : ℕ → ℕ → bool that is TOTAL (∀x, ∃y, R x y = true), define the deterministic
      successor  next x := least y with R x y  (via nat_least, 0 axioms).  Its trajectory from any x0 is an
      infinite R-chain:  R (chain n) (chain (S n)) = true  for all n — dependent choice realized with no DC.
      The chain is CANONICAL (each step is the minimal valid successor) and UNIQUE (the rule pins THE chain —
      no choice among successors).

    -- The boundary (cited, not duplicated) --
      Drop decidability or totality-witnessing and the chain needs genuine Dependent Choice — the role-limit
      (settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v).  Concretely, the standard Bolzano–Weierstrass
      (analysis/BolzanoWeierstrass.v) costs classic + L4_witness for exactly this reason: its bisection
      criterion "infinitely-many-in [lo,hi]" is UNDECIDABLE, so the successor half cannot be chosen
      deterministically.  Decidable + total ⟹ DC is free; undecidable ⟹ DC/LEM is the price.

    Elements: ℕ (the countable carrier); the decidable total relation R.
    Roles:    the successor next x = a Role assigned BY THE RULE (least valid), not a free choice; the chain =
              the deterministic trajectory; "least" makes each step canonical.
    Rules:    nat_least picks the least successor ⟹ a deterministic step ⟹ an R-chain with NO DC; decidability
              + totality ⟹ dependent choice is free.

    ============ E/R/R разбор ============
      Rules (L5): nat_least + порядок ℕ выбирают НАИМЕНЬШИЙ преемник ⟹ детерминированный шаг ⟹ R-цепь без DC.
      Roles (L4): преемник / цепь — РОЛЬ, назначаемая правилом «наименьший допустимый»; цепь детерминирована (одна).
      Elements  : ℕ; разрешимое тотальное отношение R.
    ДИАГНОСТИКА (P4): зависимый выбор — Element-сторона, когда R разрешимо+тотально на ℕ (наименьший-преемник, 0 акс);
      неразрешимое/несвидетельствованное ⟹ DC = role-limit (BolzanoWeierstrass платит classic именно за неразрешимость
      критерия половины). Параллель H49 (счётный выбор) → счётный ЗАВИСИМЫЙ выбор. Уровень: `синтез`.

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (builds on cs.CountableSelectionFree)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import PeanoNat Arith Lia.
From ToS Require Import cs.CountableSelectionFree.

(* ===================================================================== *)
(*  The deterministic successor: the LEAST valid one (via nat_least)       *)
(* ===================================================================== *)

(** A total decidable relation: every point has a (decidably-witnessed) successor. *)
Definition next (R : nat -> nat -> bool) (Htot : forall x, exists y, R x y = true) (x : nat) : nat :=
  proj1_sig (nat_least (R x) (Htot x)).

(** ★ The successor is valid: R x (next x) holds. *)
Lemma next_sound : forall R Htot x, R x (next R Htot x) = true.
Proof. intros R Htot x. unfold next. exact (proj1 (proj2_sig (nat_least (R x) (Htot x)))). Qed.

(** ★ ...and CANONICAL: it is the LEAST valid successor — any valid y has next x ≤ y. *)
Lemma next_least : forall R Htot x y, R x y = true -> next R Htot x <= y.
Proof.
  intros R Htot x y Hy. unfold next.
  destruct (le_lt_dec (proj1_sig (nat_least (R x) (Htot x))) y) as [Hle | Hlt]; [ exact Hle | ].
  exfalso. pose proof (proj2 (proj2_sig (nat_least (R x) (Htot x))) y Hlt) as Hf.
  rewrite Hy in Hf. discriminate.
Qed.

(* ===================================================================== *)
(*  The dependent-choice chain (trajectory of next) — no DC               *)
(* ===================================================================== *)

Fixpoint dc_chain (R : nat -> nat -> bool) (Htot : forall x, exists y, R x y = true)
  (x0 : nat) (n : nat) : nat :=
  match n with O => x0 | S k => next R Htot (dc_chain R Htot x0 k) end.

(** ★★ The chain IS an R-chain: dependent choice realized with NO Dependent Choice axiom. *)
Theorem dc_chain_step : forall R Htot x0 n,
  R (dc_chain R Htot x0 n) (dc_chain R Htot x0 (S n)) = true.
Proof. intros R Htot x0 n. simpl. apply next_sound. Qed.

(** ★ The chain is UNIQUE: the rule pins THE sequence — no choice among successors, hence no DC. *)
Lemma dc_chain_unique : forall R Htot x0 (f : nat -> nat),
  f O = x0 -> (forall n, f (S n) = next R Htot (f n)) ->
  forall n, f n = dc_chain R Htot x0 n.
Proof.
  intros R Htot x0 f H0 Hstep. induction n as [| k IH]; simpl.
  - exact H0.
  - rewrite Hstep, IH. reflexivity.
Qed.

(* ===================================================================== *)
(*  Concrete: a strictly-increasing chain from a total relation            *)
(* ===================================================================== *)

(** The relation x < y is total (S x is a successor). *)
Lemma lt_total : forall x, exists y, Nat.ltb x y = true.
Proof. intro x. exists (S x). apply Nat.ltb_lt. lia. Qed.

(** Its deterministic chain from 0 is strictly increasing at every step (0 axioms). *)
Example lt_chain_increasing : forall n,
  Nat.ltb (dc_chain Nat.ltb lt_total 0 n) (dc_chain Nat.ltb lt_total 0 (S n)) = true.
Proof. intro n. apply dc_chain_step. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Countable dependent choice without DC:
      (chain)      the least-successor trajectory of a decidable total relation is an R-chain (0 axioms);
      (canonical)  each step is the MINIMAL valid successor (next x ≤ any valid y) — deterministic, not free;
      (unique)     the rule pins THE chain — no choice among successors, hence no Dependent Choice.
    So dependent choice over a COUNTABLE carrier with a DECIDABLE total relation is Element-side: a
    deterministic, canonical, axiom-free chain — the dependent-choice analog of CountableSelectionFree.  The
    boundary is the undecidable / non-witnessed relation, where genuine DC (or classic, as in
    analysis/BolzanoWeierstrass.v's bisection) is the price.  Level: synthesis — least-successor descent is
    standard given nat_least; the contribution is the decidable-DC packaging, its determinism, and the
    parallel to H49. *)
Theorem countable_dependent_choice_free :
  (forall R (Htot : forall x, exists y, R x y = true) x0 n,
     R (dc_chain R Htot x0 n) (dc_chain R Htot x0 (S n)) = true)
  /\ (forall R Htot x y, R x y = true -> next R Htot x <= y)
  /\ (forall R Htot x0 (f : nat -> nat),
        f O = x0 -> (forall n, f (S n) = next R Htot (f n)) ->
        forall n, f n = dc_chain R Htot x0 n).
Proof.
  split; [ exact dc_chain_step | ].
  split; [ exact next_least | exact dc_chain_unique ].
Qed.
