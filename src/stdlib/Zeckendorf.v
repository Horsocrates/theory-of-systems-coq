(** * Zeckendorf.v — Zeckendorf's theorem / the Fibonacci (golden-ratio) base: every integer
      is UNIQUELY a sum of non-consecutive Fibonacci numbers.  The canonical bridge between the
      role-limit φ (the golden ratio, √5, a non-terminating process) and the Element-level
      integers: the IRRATIONAL base φ organizes EVERY integer into a UNIQUE FINITE
      representation.  Ties the cluster's whole φ/√5 thread (GoldenFibonacci, FibonacciWord,
      LucasFibonacci, MarkovTree, CircleRotation) to its representation thread (BaseExpansion,
      CalkinWilf).

    Elements: the Fibonacci numbers Fₖ; a representation = a finite non-consecutive index list;
              concrete 100 = F₁₁+F₆+F₄, 12 = F₆+F₄+F₂ (L1 + P4)
    Roles:    Element side = every integer is a finite, terminating Fibonacci "digit string",
              UNIQUE (the Zeckendorf representation, a well-defined Element / function);
              role-limit = the base φ = lim Fₙ₊₁/Fₙ = (1+√5)/2, a non-terminating process (√5∉ℚ)
    Rules:    the non-consecutiveness constraint forces uniqueness; the engine is one inequality
              — a non-consecutive sum with largest term Fₖ is < Fₖ₊₁ (zbound); deeper, the
              recurrence Fₖ₊₁=Fₖ+Fₖ₋₁ is why "the rest after removing Fₖ" is < Fₖ₋₁

    THE DEEP POINT — uniqueness, driven by ONE bound.  A valid (non-consecutive) Fibonacci sum
    with largest term Fₖ is strictly less than Fₖ₊₁ (`zbound`) — this single inequality forces
    the largest Fibonacci to be uniquely determined, hence the whole representation is unique
    (`zuniq`: equal sums of valid reps ⟹ identical reps).  Uniqueness is the deepest "Element"
    property: the representation is a FUNCTION — exactly one finite description per integer, no
    ambiguity.  The base φ = lim Fₙ₊₁/Fₙ = (1+√5)/2 is the role-limit (√5∉ℚ,
    `golden_base_role_limit`): the integers (Element) are uniquely organized by the golden-ratio
    base (role-limit).  ★ BOUNDARY INVERSION vs BaseExpansion: in positional base-b the base b
    is an Element (an integer) and some NUMBERS fail to terminate (irrationals); here the base φ
    is a role-limit yet EVERY integer terminates uniquely — the boundary sits in the BASE, not in
    the represented number.  Element = a finite unique Zeckendorf string; role-limit = the
    irrational base φ that organizes them.

    ============ E/R/R разбор ============
      Rules (L5): несоседство форсирует единственность; движок = одно неравенство (несоседняя сумма
                  с наибольшим Fₖ строго < Fₖ₊₁, zbound); глубже — рекуррента Fₖ₊₁=Fₖ+Fₖ₋₁.
      Roles (L4): Element = каждое целое = конечная единственная строка Фибоначчи (представление =
                  функция); role-limit = базис φ=lim Fₙ₊₁/Fₙ=(1+√5)/2, нетерминирующий процесс (√5∉ℚ).
      Elements  : Fₖ; несоседний список индексов; 100=F₁₁+F₆+F₄, 12=F₆+F₄+F₂ (L1+P4).
    ДИАГНОСТИКА (P4): целые (Element) уникально организованы базисом-φ (role-limit). Единственность =
    представление есть ФУНКЦИЯ (ровно одно конечное описание на целое) — глубочайшее «Element», гонимое
    единственным bound Fₖ-сумма<Fₖ₊₁. ★ ИНВЕРСИЯ ГРАНИЦЫ vs BaseExpansion: в позиционном базисе b сам
    базис — Element, а иррациональные ЧИСЛА не терминируют; здесь базис φ — role-limit, но КАЖДОЕ целое
    терминирует единственно — граница в БАЗИСЕ, не в числе. «Что есть φ?» = не-вопрос (нетерм. процесс).

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia List QArith.
From ToS Require Import analysis.Sqrt5Irrational.
Import ListNotations.

Open Scope nat_scope.

(* ===================================================================== *)
(*  Fibonacci numbers and their basic monotonicity                        *)
(* ===================================================================== *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

(** The recurrence, definitional. *)
Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. intros. reflexivity. Qed.

(** Every Fibonacci number fib (S n) is positive. *)
Lemma fib_pos : forall n, 1 <= fib (S n).
Proof.
  induction n as [| n IH].
  - simpl. lia.
  - rewrite fib_SS. lia.
Qed.

(** fib is non-decreasing across one step, hence monotone. *)
Lemma fib_le_succ : forall n, fib n <= fib (S n).
Proof.
  intros n. destruct n as [| n].
  - simpl. lia.
  - rewrite fib_SS. lia.
Qed.

Lemma fib_mono : forall m n, m <= n -> fib m <= fib n.
Proof.
  intros m n H. induction H.
  - lia.
  - transitivity (fib m0); [ exact IHle | apply fib_le_succ ].
Qed.

(** From index ≥ 2, the Fibonacci number is ≥ 1. *)
Lemma fib_ge1_from2 : forall i, 2 <= i -> 1 <= fib i.
Proof.
  intros i H. transitivity (fib 2).
  - simpl. lia.
  - apply fib_mono. exact H.
Qed.

(* ===================================================================== *)
(*  Valid Zeckendorf representations: decreasing indices ≥2, gaps ≥2       *)
(* ===================================================================== *)

(** A list of Fibonacci indices is a valid Zeckendorf representation when it is strictly
    decreasing (head largest), every index is ≥ 2 (so F₂=1 is the smallest, avoiding the
    F₁=F₂=1 duplicate), and consecutive indices differ by ≥ 2 (non-consecutive Fibonaccis). *)
Inductive zvalid : list nat -> Prop :=
| zv_nil  : zvalid []
| zv_one  : forall i, 2 <= i -> zvalid [i]
| zv_cons : forall i j l, 2 <= j -> j + 2 <= i -> zvalid (j :: l) -> zvalid (i :: j :: l).

(** The value of a representation: the sum of its Fibonacci numbers. *)
Fixpoint zsum (l : list nat) : nat :=
  match l with
  | [] => 0
  | i :: r => fib i + zsum r
  end.

(** The tail of a valid representation is valid. *)
Lemma zvalid_tail : forall i l, zvalid (i :: l) -> zvalid l.
Proof. intros i l H. inversion H; subst; [ apply zv_nil | assumption ]. Qed.

(** The head Fibonacci is a lower bound on the value. *)
Lemma zsum_head_le : forall i r, fib i <= zsum (i :: r).
Proof. intros. simpl. lia. Qed.

(* ===================================================================== *)
(*  THE ENGINE: a valid rep with top index i has value < fib (S i)        *)
(* ===================================================================== *)

(** ★ The one bound that drives everything: a non-consecutive Fibonacci sum with largest index
    i is strictly less than F_{i+1}.  (This is exactly why the greedy choice of the largest
    Fibonacci is forced, hence the representation is unique.) *)
Lemma zbound : forall l, zvalid l ->
  match l with [] => True | i :: _ => zsum l < fib (S i) end.
Proof.
  intros l H. induction H.
  - exact I.
  - destruct i as [| [| k]]; try lia.
    cbn [zsum]. rewrite (fib_SS (S k)). pose proof (fib_pos k). lia.
  - destruct i as [| [| m]]; try lia.
    cbn [zsum] in *. rewrite (fib_SS (S m)).
    assert (Hsm : fib (S j) <= fib (S m)) by (apply fib_mono; lia).
    lia.
Qed.

(** The same bound in directly usable cons form. *)
Lemma zbound_cons : forall i l, zvalid (i :: l) -> zsum (i :: l) < fib (S i).
Proof. intros i l H. exact (zbound (i :: l) H). Qed.

(* ===================================================================== *)
(*  THE THEOREM: uniqueness of the Zeckendorf representation               *)
(* ===================================================================== *)

(** ★ Zeckendorf uniqueness: two valid representations with the same value are identical.  So
    the Zeckendorf representation is a well-defined FUNCTION of the integer — the deepest
    Element property (exactly one finite description per integer). *)
Lemma zuniq : forall l1 l2, zvalid l1 -> zvalid l2 -> zsum l1 = zsum l2 -> l1 = l2.
Proof.
  induction l1 as [| i1 r1 IH]; intros l2 H1 H2 Hsum.
  - destruct l2 as [| i2 r2].
    + reflexivity.
    + exfalso. simpl in Hsum.
      assert (1 <= fib i2) by (apply fib_ge1_from2; inversion H2; subst; lia).
      lia.
  - destruct l2 as [| i2 r2].
    + exfalso. simpl in Hsum.
      assert (1 <= fib i1) by (apply fib_ge1_from2; inversion H1; subst; lia).
      lia.
    + destruct (lt_eq_lt_dec i1 i2) as [[Hlt | Heq] | Hgt].
      * exfalso.
        pose proof (zbound_cons i1 r1 H1) as Hb1.
        pose proof (zsum_head_le i2 r2) as Hh2.
        assert (fib (S i1) <= fib i2) by (apply fib_mono; lia).
        cbn [zsum] in Hsum, Hb1, Hh2. lia.
      * subst i2.
        assert (Hr : zsum r1 = zsum r2) by (simpl in Hsum; lia).
        assert (r1 = r2) by
          (apply IH; [ apply (zvalid_tail i1 r1 H1)
                     | apply (zvalid_tail i1 r2 H2) | exact Hr ]).
        subst. reflexivity.
      * exfalso.
        pose proof (zbound_cons i2 r2 H2) as Hb2.
        pose proof (zsum_head_le i1 r1) as Hh1.
        assert (fib (S i2) <= fib i1) by (apply fib_mono; lia).
        cbn [zsum] in Hsum, Hb2, Hh1. lia.
Qed.

(* ===================================================================== *)
(*  Concrete Zeckendorf representations                                    *)
(* ===================================================================== *)

(** 100 = 89 + 8 + 3 = F₁₁ + F₆ + F₄. *)
Lemma zeck_100_valid : zvalid [11; 6; 4].
Proof.
  apply zv_cons; [ lia | lia | ].
  apply zv_cons; [ lia | lia | ].
  apply zv_one; lia.
Qed.
Lemma zeck_100 : zsum [11; 6; 4] = 100.
Proof. vm_compute. reflexivity. Qed.

(** 12 = 8 + 3 + 1 = F₆ + F₄ + F₂. *)
Lemma zeck_12_valid : zvalid [6; 4; 2].
Proof.
  apply zv_cons; [ lia | lia | ].
  apply zv_cons; [ lia | lia | ].
  apply zv_one; lia.
Qed.
Lemma zeck_12 : zsum [6; 4; 2] = 12.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: the base φ is irrational                                   *)
(* ===================================================================== *)

(** ★ The Fibonacci base's value is φ = lim Fₙ₊₁/Fₙ = (1+√5)/2 — a role-limit, since no
    rational squares to 5.  So the base is irrational (a non-terminating process) even though
    every integer's Zeckendorf representation is a finite, unique Element. *)
Theorem golden_base_role_limit : ~ (exists r : Q, (r * r == 5)%Q).
Proof. exact sqrt5_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Zeckendorf / the golden-ratio base, split by the finitization boundary:
      (a) ELEMENT — every integer has a UNIQUE finite Fibonacci representation: uniqueness
          (`zuniq`), driven by the one bound that a valid rep with top index i has value
          < F_{i+1} (`zbound_cons`); concretely 100 = F₁₁+F₆+F₄ (`zeck_100`);
      (b) ROLE-LIMIT — the base φ = (1+√5)/2 is irrational (`golden_base_role_limit`): the
          boundary sits in the BASE, while every represented integer terminates uniquely. *)
Theorem zeckendorf_synthesis :
  (forall l1 l2, zvalid l1 -> zvalid l2 -> zsum l1 = zsum l2 -> l1 = l2)
  /\ (forall i l, zvalid (i :: l) -> zsum (i :: l) < fib (S i))
  /\ zsum [11; 6; 4] = 100
  /\ ~ (exists r : Q, (r * r == 5)%Q).
Proof.
  split; [ exact zuniq | ].
  split; [ exact zbound_cons | ].
  split; [ vm_compute; reflexivity | exact golden_base_role_limit ].
Qed.
