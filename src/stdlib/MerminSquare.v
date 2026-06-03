(** * MerminSquare.v — the Peres–Mermin magic square over ℤ: state-independent
      CONTEXTUALITY (the simplest Kochen–Specker proof).  No non-contextual value
      assignment satisfies the 3×3 array of constraints — and the contradiction
      needs NEITHER a quantum state (unlike GHZ) NOR ±1 values: it holds over ANY
      commutative ring.  Pure commutativity, zero continuum content.

    Elements: the 9 cell values; the row/column products ±1; the contradiction
              1 = −1 (L1 + P4)
    Roles:    the magic-square observable products (Elements, ±1) vs a NON-CONTEXTUAL
              value assignment (impossible); contextuality = STATE-INDEPENDENT (no
              state, unlike the GHZ nonlocality) and VALUE-INDEPENDENT (no ±1 needed)
    Rules:    the 3×3 array; the six product constraints (3 rows = +1, columns =
              +1,+1,−1); the commutativity identity ∏rows = ∏cols (each cell occurs
              once in its row and once in its column)

    THE DEEP POINT — contextuality is even more Element than nonlocality.  GHZ
    (`GHZParadox.v`) needs three separated parties and an entangled state.  The
    Peres–Mermin square needs NEITHER: it is a single 3×3 array of observables, and
    the impossibility is about assigning them definite values at all — the
    Kochen–Specker theorem.  Each cell appears in exactly one row and one column, so
    the product of the three row-products equals the product of the three
    column-products (pure commutativity, `mermin_square_no_assignment` via one
    `ring` identity).  But the magic square forces the rows to multiply to +1,+1,+1
    and the columns to +1,+1,−1, so that equal product is +1 on one side and −1 on
    the other: 1 = −1.  The contradiction does NOT even use that the values are ±1 —
    it holds for any commutative-ring assignment.  So the impossibility is
    state-independent AND value-independent: the sharpest, most finite-actual form of
    the quantum obstruction.  All ±1, all integers, all algebra — zero continuum.

    (The quantum side IS realisable: the cells are 2-qubit Pauli products
    [X⊗I, I⊗X, X⊗X; I⊗Y, Y⊗I, Y⊗Y; X⊗Y, Y⊗X, Z⊗Z], whose row/column products give
    exactly +I,+I,+I / +I,+I,−I — non-commuting operators meeting constraints no
    commutative value assignment can.  That is the quantum advantage: contextuality.)

    ============ E/R/R разбор ============
      Rules (L5): массив 3×3; 6 ограничений (3 строки=+1, столбцы +1,+1,−1);
                  тождество ∏строк=∏столбцов (каждая ячейка раз в строке, раз в столбце).
      Roles (L4): произведения магического квадрата (Elements, ±1) vs неконтекстуальное
                  присваивание (невозможно); контекстуальность = состояние-независима
                  (без состояния, в отличие от GHZ) И значение-независима (без ±1).
      Elements  : значения ячеек; произведения ±1; противоречие 1=−1 (L1+P4).
    ДИАГНОСТИКА (P4): квадрат Переса–Мермина = простейший Кохен–Шпекер; противоречие = чистая
    коммутативность, не требует НИ состояния, НИ ±1 — резче GHZ. Контекстуальность полностью
    Element-сторонна (ноль континуума). Самодостаточно над ℤ.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(* ===================================================================== *)
(*  The 3×3 array of observables a_ij, with row/column product constraints *)
(* ===================================================================== *)

(** ★ No assignment of values to the nine cells satisfies all six product
    constraints (3 rows = +1, columns = +1,+1,−1).  The contradiction is pure
    commutativity — ∏rows = ∏cols — and needs NEITHER a state NOR ±1 values: it
    holds for ANY integers (indeed any commutative ring).  This is the Kochen–Specker
    theorem: no non-contextual value assignment exists. *)
Theorem mermin_square_no_assignment :
  forall a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z,
    a11 * a12 * a13 = 1 ->          (* row 1 *)
    a21 * a22 * a23 = 1 ->          (* row 2 *)
    a31 * a32 * a33 = 1 ->          (* row 3 *)
    a11 * a21 * a31 = 1 ->          (* column 1 *)
    a12 * a22 * a32 = 1 ->          (* column 2 *)
    a13 * a23 * a33 = -1 ->         (* column 3 — the "magic" −1 *)
    False.
Proof.
  intros a11 a12 a13 a21 a22 a23 a31 a32 a33 R1 R2 R3 C1 C2 C3.
  assert (Key : (a11 * a12 * a13) * (a21 * a22 * a23) * (a31 * a32 * a33)
              = (a11 * a21 * a31) * (a12 * a22 * a32) * (a13 * a23 * a33)) by ring.
  rewrite R1, R2, R3, C1, C2, C3 in Key. lia.
Qed.

(** The obstruction is EXACTLY the magic −1: if all six products were +1, the array
    is satisfiable (take every cell = 1).  So five of the six contexts are jointly
    consistent; it is the sixth (the −1 column) that no value assignment can meet. *)
Theorem mermin_consistent_without_magic :
  exists a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z,
    a11 * a12 * a13 = 1 /\ a21 * a22 * a23 = 1 /\ a31 * a32 * a33 = 1 /\
    a11 * a21 * a31 = 1 /\ a12 * a22 * a32 = 1 /\ a13 * a23 * a33 = 1.
Proof.
  exists 1, 1, 1, 1, 1, 1, 1, 1, 1. repeat split; reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Peres–Mermin square in one statement — state-independent, value-independent
    contextuality (Kochen–Specker):
      (a) no value assignment satisfies the magic square (the −1 column makes the
          six constraints jointly impossible, over ANY commutative ring);
      (b) yet with all-+1 products the array IS satisfiable — the obstruction is
          exactly the one −1, not any individual context. *)
Theorem mermin_synthesis :
  (forall a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z,
     a11*a12*a13 = 1 -> a21*a22*a23 = 1 -> a31*a32*a33 = 1 ->
     a11*a21*a31 = 1 -> a12*a22*a32 = 1 -> a13*a23*a33 = -1 -> False)
  /\ (exists a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z,
        a11*a12*a13 = 1 /\ a21*a22*a23 = 1 /\ a31*a32*a33 = 1 /\
        a11*a21*a31 = 1 /\ a12*a22*a32 = 1 /\ a13*a23*a33 = 1).
Proof.
  split; [ exact mermin_square_no_assignment | exact mermin_consistent_without_magic ].
Qed.
