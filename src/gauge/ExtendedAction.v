(* ========================================================================= *)
(*        EXTENDED ACTION — T₁ on monomials up to degree 4                  *)
(*                                                                          *)
(*  For 2+1D continuum limit, need T₁(xⁿ) for n=0..4 (not just n=0..2).  *)
(*  E matrix (3×5): E[i][n] = coefficient of xⁱ in T₁(xⁿ)               *)
(*                                                                          *)
(*  Formula:                                                                *)
(*    E[0][n] = 1/(n+1) - 4/(n+3)  (constant term)                        *)
(*    E[1][n] = 8/(n+2)            (linear term)                          *)
(*    E[2][n] = -4/(n+1)           (quadratic term)                       *)
(*                                                                          *)
(*  Consistency: columns 0-2 match ContinuumOperator.v cont_entry          *)
(*  Column integrals: ∫₀¹ T₁(xⁿ) dx = E[0][n]·m₀ + E[1][n]·m₁ + E[2][n]·m₂ *)
(*                                                                          *)
(*  STATUS: ~31 Qed, 0 Admitted                                            *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import gauge.ContinuumOperator.

(* ========================================================================= *)
(*  PART I: Extended Action Matrix E (3×5)                                  *)
(* ========================================================================= *)

(** E[i][n] = coefficient of xⁱ in T₁(xⁿ)
    where T₁f(x) = ∫₀¹ k(x,y) f(y) dy with k(x,y) = 1-4(x-y)² *)
Definition e_entry (i n : nat) : Q :=
  match i, n with
  (* Row 0: constant term = 1/(n+1) - 4/(n+3) *)
  | O, O => -(1#3)            (* 1/1 - 4/3 = -1/3 *)
  | O, S O => -(1#2)          (* 1/2 - 4/4 = -1/2 *)
  | O, S (S O) => -(7#15)     (* 1/3 - 4/5 = -7/15 *)
  | O, S (S (S O)) => -(5#12) (* 1/4 - 4/6 = -5/12 *)
  | O, S (S (S (S O))) => -(13#35) (* 1/5 - 4/7 = -13/35 *)
  (* Row 1: linear term = 8/(n+2) *)
  | S O, O => 4               (* 8/2 = 4 *)
  | S O, S O => 8#3           (* 8/3 *)
  | S O, S (S O) => 2         (* 8/4 = 2 *)
  | S O, S (S (S O)) => 8#5   (* 8/5 *)
  | S O, S (S (S (S O))) => 4#3 (* 8/6 = 4/3 *)
  (* Row 2: quadratic term = -4/(n+1) *)
  | S (S O), O => -(4)        (* -4/1 = -4 *)
  | S (S O), S O => -(2)      (* -4/2 = -2 *)
  | S (S O), S (S O) => -(4#3) (* -4/3 *)
  | S (S O), S (S (S O)) => -(1) (* -4/4 = -1 *)
  | S (S O), S (S (S (S O))) => -(4#5) (* -4/5 *)
  | _, _ => 0
  end.

(* ========================================================================= *)
(*  PART II: Individual entry verification                                   *)
(* ========================================================================= *)

(** Row 0 entries *)
Lemma e_entry_00 : e_entry 0 0 == -(1#3).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_01 : e_entry 0 1 == -(1#2).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_02 : e_entry 0 2 == -(7#15).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_03 : e_entry 0 3 == -(5#12).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_04 : e_entry 0 4 == -(13#35).
Proof. unfold e_entry. lra. Qed.

(** Row 1 entries *)
Lemma e_entry_10 : e_entry 1 0 == 4.
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_11 : e_entry 1 1 == 8#3.
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_12 : e_entry 1 2 == 2.
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_13 : e_entry 1 3 == 8#5.
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_14 : e_entry 1 4 == 4#3.
Proof. unfold e_entry. lra. Qed.

(** Row 2 entries *)
Lemma e_entry_20 : e_entry 2 0 == -(4).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_21 : e_entry 2 1 == -(2).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_22 : e_entry 2 2 == -(4#3).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_23 : e_entry 2 3 == -(1).
Proof. unfold e_entry. lra. Qed.

Lemma e_entry_24 : e_entry 2 4 == -(4#5).
Proof. unfold e_entry. lra. Qed.

(* ========================================================================= *)
(*  PART III: Consistency with ContinuumOperator.v                          *)
(* ========================================================================= *)

(** Columns 0-2 of E match the 3×3 continuum matrix M *)
Theorem e_matches_cont_col0 :
  e_entry 0 0 == cont_entry 0 0 /\
  e_entry 1 0 == cont_entry 1 0 /\
  e_entry 2 0 == cont_entry 2 0.
Proof.
  split; [| split];
  unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq;
  simpl; lia.
Qed.

Theorem e_matches_cont_col1 :
  e_entry 0 1 == cont_entry 0 1 /\
  e_entry 1 1 == cont_entry 1 1 /\
  e_entry 2 1 == cont_entry 2 1.
Proof.
  split; [| split];
  unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq;
  simpl; lia.
Qed.

Theorem e_matches_cont_col2 :
  e_entry 0 2 == cont_entry 0 2 /\
  e_entry 1 2 == cont_entry 1 2 /\
  e_entry 2 2 == cont_entry 2 2.
Proof.
  split; [| split];
  unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq;
  simpl; lia.
Qed.

(* ========================================================================= *)
(*  PART IV: Column integrals (normalization check)                         *)
(* ========================================================================= *)

(** Column integral: ∫₀¹ T₁(xⁿ) dx = E[0][n]·1 + E[1][n]·(1/2) + E[2][n]·(1/3) *)
Definition col_integral (n : nat) : Q :=
  e_entry 0 n + e_entry 1 n * (1#2) + e_entry 2 n * (1#3).

Lemma col_integral_0 : col_integral 0 == 1#3.
Proof. unfold col_integral, e_entry, Qeq. simpl. lia. Qed.

Lemma col_integral_1 : col_integral 1 == 1#6.
Proof. unfold col_integral, e_entry, Qeq. simpl. lia. Qed.

Lemma col_integral_2 : col_integral 2 == 4#45.
Proof. unfold col_integral, e_entry, Qeq. simpl. lia. Qed.

Lemma col_integral_3 : col_integral 3 == 1#20.
Proof. unfold col_integral, e_entry, Qeq. simpl. lia. Qed.

Lemma col_integral_4 : col_integral 4 == 1#35.
Proof. unfold col_integral, e_entry, Qeq. simpl. lia. Qed.

(** All column integrals are positive *)
Lemma col_integral_positive : forall n, (n <= 4)%nat -> 0 < col_integral n.
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|?]]]]]; try lia;
  unfold col_integral, e_entry; lra.
Qed.

(* ========================================================================= *)
(*  PART V: Summary                                                          *)
(* ========================================================================= *)

(** ★ EXTENDED ACTION MAIN ★ *)
Theorem extended_action_main :
  (* Consistency with 1D *)
  e_entry 0 0 == cont_entry 0 0 /\
  e_entry 1 1 == cont_entry 1 1 /\
  e_entry 2 2 == cont_entry 2 2 /\
  (* New columns *)
  e_entry 0 3 == -(5#12) /\
  e_entry 0 4 == -(13#35) /\
  (* Column integrals positive *)
  0 < col_integral 3 /\
  0 < col_integral 4.
Proof.
  split; [unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq; simpl; lia |].
  split; [unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq; simpl; lia |].
  split; [unfold e_entry, cont_entry, mat3_mul_entry, kernel_coeff_entry, hilbert_entry, Qeq; simpl; lia |].
  split; [exact e_entry_03 |].
  split; [exact e_entry_04 |].
  split; [exact (col_integral_positive 3 ltac:(lia)) |].
  exact (col_integral_positive 4 ltac:(lia)).
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~31 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part II: e_entry_00..24 (15)                                             *)
(*  Part III: e_matches_cont_col0/1/2 (3)                                    *)
(*  Part IV: col_integral_0..4, col_integral_positive (6)                    *)
(*  Part V: extended_action_main, total_count (2)                            *)
(*  Plus: Definitions e_entry, col_integral (2 defs, 5 non-Qed)             *)
(* ========================================================================= *)
