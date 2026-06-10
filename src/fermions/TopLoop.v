(** * TopLoop.v — top-loop correction at the N=4 cutoff: real monotonicity, stubs removed
    Elements: loop sums at concrete masses; the correction Δm²_H; the tree mass
    Roles:    the loop sum — radiative-correction role; m² — the decoupling dial
              (heavier ⟹ smaller loop); the −N_c factor — the sign role
    Rules:    loop formulas are INPUTS (posited cutoff model); GIVEN them: positivity,
              concrete values, and DECOUPLING (loop strictly decreasing in mass) are forced
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: April 2026  (True-stub honesty rollback: June 2026)

    HONEST STATUS: June 2026 — REMOVED `grows_with_N : True` (no N-parametric sum exists
    in this file — only the N=4 instance; the claim had no formal carrier) and
    `need_gauge : True` (a stub).  REPLACED by real content:
    loop_sum_decreasing_in_mass — the loop sum strictly DECREASES in the fermion mass
    (decoupling), proved generally via Qdiv_lt_pos; and top_alone_negative_mass —
    tree + top alone drives m²_H NEGATIVE (1 − 11/8 = −3/8 < 0), which IS the honest
    quantitative content of "need gauge loops for the full picture".

    E/R/R разбор: Rules — формулы петель постулированы (модель обрезания); ПРИ них
    знаки/значения/убывание по массе вынуждены; Roles — масса = ручка развязки
    (тяжелее ⟹ меньше вклад), −N_c = роль знака; Elements — конкретные значения
    52/60, −11/8, −3/8. P4: «нужны калибровочные петли» — теперь арифметика
    (отрицательный m² без них), не декларация. *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(* Color factor and loop sum at N=4 cutoff                          *)
(* top_loop_sum_4(m_sq) = (1/4) * (2/(1/2 + m_sq) + 1/(1 + m_sq)) *)
(* Sum over k=1..3 with N=4: simplified to representative terms    *)
(* ================================================================= *)

Definition N_c : Q := 3.

Definition top_loop_sum_4 (m_sq : Q) : Q :=
  (1#4) * (2 / ((1#2) + m_sq) + 1 / (1 + m_sq)).

Definition delta_mH_sq (y_t loop_sum : Q) : Q :=
  -(N_c) * y_t * y_t * loop_sum.

Definition mH_sq_tree : Q := 1.

(* ================================================================= *)
(* Theorem 1: Loop sum is positive for m_sq = 1/4                   *)
(* top_loop_sum_4(1/4) = (1/4)*(2/(3/4) + 1/(5/4))                *)
(*                     = (1/4)*(8/3 + 4/5) = (1/4)*(52/15) = 52/60 *)
(* ================================================================= *)

Theorem top_loop_positive :
  top_loop_sum_4 (1#4) > 0.
Proof. unfold top_loop_sum_4. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 2: Concrete value of loop sum at m_sq=1/4                *)
(* ================================================================= *)

Theorem top_loop_value :
  top_loop_sum_4 (1#4) == 52#60.
Proof. unfold top_loop_sum_4. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 3: Top correction is negative (delta < 0)                *)
(* delta = -3 * 1 * 1 * 52/60 = -156/60 = -13/5                    *)
(* ================================================================= *)

Theorem top_loop_negative :
  delta_mH_sq 1 (top_loop_sum_4 (1#4)) < 0.
Proof.
  unfold delta_mH_sq, N_c, top_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 4: Concrete value of top correction                      *)
(* ================================================================= *)

Theorem top_correction_value :
  delta_mH_sq 1 (top_loop_sum_4 (1#4)) == -(13#5).
Proof.
  unfold delta_mH_sq, N_c, top_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 5: Tree + top < tree (top pushes mass down)              *)
(* ================================================================= *)

Theorem tree_plus_top :
  mH_sq_tree + delta_mH_sq 1 (top_loop_sum_4 (1#4)) < mH_sq_tree.
Proof.
  unfold mH_sq_tree, delta_mH_sq, N_c, top_loop_sum_4.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 6: Loop sum at m_sq=1 (used later in GaugeLoops)         *)
(* top_loop_sum_4(1) = (1/4)*(2/(3/2) + 1/2) = (1/4)*(4/3+1/2)   *)
(*                   = (1/4)*(11/6) = 11/24                         *)
(* ================================================================= *)

Theorem top_loop_at_m1 :
  top_loop_sum_4 1 == 11#24.
Proof. unfold top_loop_sum_4. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 7: Top correction at m_sq=1                              *)
(* delta = -3 * 1 * 11/24 = -33/24 = -11/8                         *)
(* ================================================================= *)

Theorem top_correction_at_m1 :
  delta_mH_sq 1 (top_loop_sum_4 1) == -(11#8).
Proof.
  unfold delta_mH_sq, N_c, top_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 8: Loop sum positive at m_sq=1                           *)
(* ================================================================= *)

Theorem top_loop_positive_m1 :
  top_loop_sum_4 1 > 0.
Proof. unfold top_loop_sum_4. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* June 2026 — real general layer (replaces the removed True-stubs   *)
(* grows_with_N [no N-parametric sum exists here] and need_gauge)    *)
(* ================================================================= *)

(** Helper: for a positive numerator, a larger positive denominator gives a
    smaller quotient. *)
Lemma Qdiv_lt_pos : forall a b c : Q,
  0 < a -> 0 < b -> b < c -> a / c < a / b.
Proof.
  intros a b c Ha Hb Hbc.
  assert (Hc : 0 < c) by lra.
  assert (Hd : a / b - a / c == a * (c - b) / (b * c)).
  { field. split; intro Hx; lra. }
  assert (Hpos : 0 < a * (c - b) / (b * c)).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - nra.
    - apply Qinv_lt_0_compat. nra. }
  lra.
Qed.

(** ★ DECOUPLING: the loop sum strictly DECREASES in the fermion mass —
    heavier fermions contribute less (general, not an instance). *)
Theorem loop_sum_decreasing_in_mass : forall m1 m2 : Q,
  0 <= m1 -> m1 < m2 -> top_loop_sum_4 m2 < top_loop_sum_4 m1.
Proof.
  intros m1 m2 H0 H12. unfold top_loop_sum_4.
  assert (HA : 2 / ((1#2) + m2) < 2 / ((1#2) + m1)).
  { apply Qdiv_lt_pos; lra. }
  assert (HB : 1 / (1 + m2) < 1 / (1 + m1)).
  { apply Qdiv_lt_pos; lra. }
  lra.
Qed.

(** ★ Tree + top ALONE drives m²_H negative (1 − 11/8 = −3/8 < 0) — the honest
    quantitative content of "gauge loops are needed for the full picture". *)
Theorem top_alone_negative_mass :
  mH_sq_tree + delta_mH_sq 1 (top_loop_sum_4 1) < 0.
Proof.
  unfold mH_sq_tree, delta_mH_sq, N_c, top_loop_sum_4.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Synthesis                                                         *)
(* ================================================================= *)

Theorem top_loop_synthesis :
  top_loop_sum_4 (1#4) > 0 /\
  delta_mH_sq 1 (top_loop_sum_4 (1#4)) < 0 /\
  mH_sq_tree + delta_mH_sq 1 (top_loop_sum_4 (1#4)) < mH_sq_tree /\
  top_loop_sum_4 1 == 11#24.
Proof.
  unfold top_loop_sum_4, delta_mH_sq, N_c, mH_sq_tree.
  repeat split; vm_compute; reflexivity.
Qed.
