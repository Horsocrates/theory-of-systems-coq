(** * SortDecidable.v — Q4 of the open agenda: can the Element/role-limit SORT be made a TOTAL DECISION
      PROCEDURE on a restricted, decidable class?  YES.  The general sort is UNDECIDABLE (GravityH1Decision.v:
      boundedness of an arbitrary process is the halting problem).  But restricted to the class { sqrt n :
      n in nat }, the sort is TOTAL and correct: sqrt n is Element (rational) iff n is a perfect square —
      and "n is a perfect square" is decidable, computed via the integer square root Nat.sqrt.

    -- The decision procedure --
      sort_sqrt n = is_square n = Nat.eqb (Nat.sqrt n * Nat.sqrt n) n.  It always terminates and is correct:
        sort_sqrt n = true  <->  n is a perfect square  <->  sqrt n is rational (Element);
        sort_sqrt n = false <->  n is not a perfect square  <->  sqrt n is irrational (role-limit).
      decide_sqrt is the genuine decision procedure (a sumbool: it returns a PROOF of which side).  The
      Element/role-limit dichotomy is therefore CONSTRUCTIVELY decidable on this class (no excluded middle).

    -- The contrast --
      In GravityH1Decision.v the general sort (Bounded vs Unbounded of an arbitrary process) is NOT a total
      decider — it is the halting problem.  Here, on the class where the criterion is COMPUTABLE (perfect-
      square detection), the same Element/role-limit sort IS total and correct.  So the sort can be made a
      total decision procedure exactly on the decidable classes.  This ties to GeneralSqrt.v (sqrt n
      rational <-> n a perfect square): there it is a theorem, here it is a DECISION PROCEDURE.

    -- HONEST scope --
      One decidable class (the square roots sqrt n).  The general sort remains undecidable
      (GravityH1Decision.v).  The point is not that everything is decidable, but that the boundary of
      decidability is exactly "is the Element/role-limit criterion computable on this class?".

    Elements: is_square n = Nat.eqb (Nat.sqrt n * Nat.sqrt n) n; decide_sqrt (sumbool); sqrt 4 / sqrt 2
    Roles:    perfect square = Element (rational root); non-square = role-limit (irrational); decide_sqrt = procedure
    Rules:    the general sort is undecidable; on { sqrt n } it is a total, correct decision procedure

    ============ E/R/R разбор ============
      Rules (L5): общий H1-сорт неразрешим (halting, GravityH1Decision); на разрешимом классе { sqrt n }
                  он -- тотальная решающая процедура: sqrt n Element <=> n полный квадрат (вычислимо, Nat.sqrt).
      Roles (L4): перфектный квадрат = Element (рациональный корень); не-квадрат = role-limit; decide_sqrt =
                  решающая процедура (sumbool); контраст с общим случаем = граница разрешимости.
      Elements  : is_square n := Nat.eqb (Nat.sqrt n * Nat.sqrt n) n; decide_sqrt; sort_4 / sort_2.
    ДИАГНОСТИКА (P4): ДА -- сорт делается тотальной решающей процедурой на разрешимом классе.  Общий сорт
    неразрешим (halting); на перфектных квадратах -- тотален и корректен (Nat.sqrt вычислим).  Граница
    разрешимости: класс, где критерий Element/role-limit ВЫЧИСЛИМ.  Смычка с GeneralSqrt (там теорема, здесь
    решающая процедура).  ЧЕСТНО: один класс (sqrt n); общий сорт остаётся неразрешим.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  The computable sort on { sqrt n }                                      *)
(* ===================================================================== *)

(** Decide whether n is a perfect square, via the integer square root. *)
Definition is_square (n : nat) : bool := Nat.eqb (Nat.sqrt n * Nat.sqrt n) n.

(** The sort: true = Element (sqrt n rational), false = role-limit (sqrt n irrational). *)
Definition sort_sqrt (n : nat) : bool := is_square n.

(** ★ Correctness: is_square n = true iff n is a perfect square. *)
Lemma is_square_iff : forall n, is_square n = true <-> exists r, r * r = n.
Proof.
  intro n. unfold is_square. rewrite Nat.eqb_eq. split.
  - intro H. exists (Nat.sqrt n). exact H.
  - intros [r Hr]. rewrite <- Hr.
    rewrite !(Nat.sqrt_square r). reflexivity.
Qed.

(* ===================================================================== *)
(*  Soundness on both sides of the boundary                                *)
(* ===================================================================== *)

(** Element side: the sort returns true iff sqrt n is rational (n a perfect square). *)
Lemma sort_element : forall n, sort_sqrt n = true <-> exists r, r * r = n.
Proof. exact is_square_iff. Qed.

(** Role-limit side: the sort returns false iff sqrt n is irrational (n not a perfect square). *)
Lemma sort_role_limit : forall n, sort_sqrt n = false <-> ~ (exists r, r * r = n).
Proof.
  intro n. unfold sort_sqrt. split.
  - intros Hf [r Hr].
    assert (Ht : is_square n = true) by (apply (proj2 (is_square_iff n)); exists r; exact Hr).
    rewrite Hf in Ht. discriminate.
  - intro Hne. destruct (is_square n) eqn:E.
    + exfalso. apply Hne. apply (proj1 (is_square_iff n)). exact E.
    + reflexivity.
Qed.

(* ===================================================================== *)
(*  The genuine decision procedure (sumbool) and constructive decidability *)
(* ===================================================================== *)

(** ★ A TOTAL decision procedure: it always terminates with a PROOF of which side of the boundary sqrt n
    lies on (Element = perfect square, or role-limit = not). *)
Lemma decide_sqrt : forall n, {exists r, r * r = n} + {~ (exists r, r * r = n)}.
Proof.
  intro n. destruct (is_square n) eqn:E.
  - left. apply (proj1 (is_square_iff n)). exact E.
  - right. intro Hex.
    assert (Ht : is_square n = true) by (apply (proj2 (is_square_iff n)); exact Hex).
    rewrite E in Ht. discriminate.
Qed.

(** Hence the Element/role-limit dichotomy is CONSTRUCTIVELY decidable on this class (no excluded middle). *)
Lemma sqrt_decidable : forall n, (exists r, r * r = n) \/ ~ (exists r, r * r = n).
Proof. intro n. destruct (decide_sqrt n) as [H | H]; [ left | right ]; exact H. Qed.

(* ===================================================================== *)
(*  Concrete                                                               *)
(* ===================================================================== *)

Lemma sort_4_element : sort_sqrt 4 = true.    (* sqrt 4 = 2: Element *)
Proof. reflexivity. Qed.

Lemma sort_2_role_limit : sort_sqrt 2 = false. (* sqrt 2 irrational: role-limit *)
Proof. reflexivity. Qed.

Lemma sort_9_element : sort_sqrt 9 = true.    (* sqrt 9 = 3: Element *)
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the sort is total & decidable on { sqrt n }                  *)
(* ===================================================================== *)

(** Q4 — the sort, total on a decidable class:
      (Element)    sort_sqrt n = true  <-> n is a perfect square (sqrt n rational = Element);
      (role-limit) sort_sqrt n = false <-> n is not a perfect square (sqrt n irrational = role-limit);
      (decidable)  the dichotomy is constructively decidable (decide_sqrt always terminates with a proof);
      (concrete)   sqrt 4 Element, sqrt 2 role-limit.
    The general sort is UNDECIDABLE (GravityH1Decision.v: the halting problem); restricted to { sqrt n },
    where the criterion is computable (Nat.sqrt), it is a TOTAL, correct decision procedure.  The boundary
    of decidability is exactly "is the Element/role-limit criterion computable on this class?". *)
Theorem sort_total_on_decidable_class :
  (forall n, sort_sqrt n = true <-> exists r, r * r = n)
  /\ (forall n, sort_sqrt n = false <-> ~ (exists r, r * r = n))
  /\ (forall n, (exists r, r * r = n) \/ ~ (exists r, r * r = n))
  /\ sort_sqrt 4 = true
  /\ sort_sqrt 2 = false.
Proof.
  split; [ exact sort_element | ].
  split; [ exact sort_role_limit | ].
  split; [ exact sqrt_decidable | ].
  split; [ reflexivity | reflexivity ].
Qed.
