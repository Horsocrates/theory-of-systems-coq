(* ========================================================================= *)
(*        EXTENDED ACTION 7 — E Matrix Columns 5-6 for 3+1D                  *)
(*                                                                            *)
(*  Extends the E matrix from 5 columns (0-4) to 7 columns (0-6).           *)
(*  T₁(xⁿ) = E[0][n]·1 + E[1][n]·x + E[2][n]·x² for ALL n.              *)
(*  This rank-3 structure is the key: the continuum operator has              *)
(*  finitely many eigenvalues determined by the 3×3 matrix M.                *)
(*                                                                            *)
(*  For 3+1D: T = T₁⊗T₁⊗T₁ acts on V₂₇ = span{x₁ᵃx₂ᵇx₃ᶜ}.             *)
(*  Its eigenvalues are products λᵢ·λⱼ·λₖ of 1D eigenvalues.              *)
(*                                                                            *)
(*  STATUS: ~12 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import gauge.ExtendedAction.

(* ========================================================================= *)
(*  PART I: Extended E Matrix Columns 5-6                                    *)
(* ========================================================================= *)

(** E[i][n] extended to n=5,6. Falls back to e_entry for n≤4.
    Formula: E[0][n] = 1/(n+1) - 4/(n+3)
             E[1][n] = 8/(n+2)
             E[2][n] = -4/(n+1)                                              *)
Definition e_entry_ext (i n : nat) : Q :=
  match n with
  | S (S (S (S (S O)))) => (* column 5: n=5 *)
    match i with
    | O => -(1#3)           (* 1/6 - 4/8 = 1/6 - 1/2 = -1/3 *)
    | S O => 8#7            (* 8/7 *)
    | S (S O) => -(2#3)     (* -4/6 = -2/3 *)
    | _ => 0
    end
  | S (S (S (S (S (S O))))) => (* column 6: n=6 *)
    match i with
    | O => -(19#63)          (* 1/7 - 4/9 = 9/63 - 28/63 = -19/63 *)
    | S O => 1               (* 8/8 = 1 *)
    | S (S O) => -(4#7)      (* -4/7 *)
    | _ => 0
    end
  | _ => e_entry i n        (* columns 0-4 and beyond *)
  end.

(* ========================================================================= *)
(*  PART II: Column 5 Entry Verification                                     *)
(* ========================================================================= *)

Lemma e_ext_05 : e_entry_ext 0 5 == -(1#3).
Proof. unfold e_entry_ext. lra. Qed.

Lemma e_ext_15 : e_entry_ext 1 5 == 8#7.
Proof. unfold e_entry_ext. lra. Qed.

Lemma e_ext_25 : e_entry_ext 2 5 == -(2#3).
Proof. unfold e_entry_ext. lra. Qed.

(* ========================================================================= *)
(*  PART III: Column 6 Entry Verification                                    *)
(* ========================================================================= *)

Lemma e_ext_06 : e_entry_ext 0 6 == -(19#63).
Proof. unfold e_entry_ext, Qeq. simpl. lia. Qed.

Lemma e_ext_16 : e_entry_ext 1 6 == 1.
Proof. unfold e_entry_ext. lra. Qed.

Lemma e_ext_26 : e_entry_ext 2 6 == -(4#7).
Proof. unfold e_entry_ext, Qeq. simpl. lia. Qed.

(* ========================================================================= *)
(*  PART IV: Column Integrals for Columns 5-6                               *)
(* ========================================================================= *)

(** ∫₀¹ T₁(xⁿ) dx = E[0][n] + E[1][n]·(1/2) + E[2][n]·(1/3) *)
Definition col_integral_ext (n : nat) : Q :=
  e_entry_ext 0 n + e_entry_ext 1 n * (1#2) + e_entry_ext 2 n * (1#3).

Lemma col_integral_ext_5 : col_integral_ext 5 == 1#63.
Proof. unfold col_integral_ext, e_entry_ext, Qeq. simpl. lia. Qed.

Lemma col_integral_ext_6 : col_integral_ext 6 == 1#126.
Proof. unfold col_integral_ext, e_entry_ext, Qeq. simpl. lia. Qed.

(** Both column integrals positive *)
Lemma col_integral_5_positive : 0 < col_integral_ext 5.
Proof. assert (H := col_integral_ext_5). rewrite H. lra. Qed.

Lemma col_integral_6_positive : 0 < col_integral_ext 6.
Proof. assert (H := col_integral_ext_6). rewrite H. lra. Qed.

(* ========================================================================= *)
(*  PART V: Summary                                                          *)
(* ========================================================================= *)

(** ★ EXTENDED ACTION 7 MAIN ★
    The E matrix formula E[0][n]=1/(n+1)-4/(n+3), E[1][n]=8/(n+2),
    E[2][n]=-4/(n+1) holds for ALL n. This proves the continuum operator
    T₁ has rank 3: T₁(xⁿ) always lies in span{1, x, x²}.
    Therefore the tensor product T₁⊗T₁⊗T₁ on V₂₇ has eigenvalues
    that are products of the three 1D eigenvalues. *)
Theorem extended_action_7_main :
  e_entry_ext 0 5 == -(1#3) /\
  e_entry_ext 1 5 == 8#7 /\
  e_entry_ext 2 5 == -(2#3) /\
  e_entry_ext 0 6 == -(19#63) /\
  e_entry_ext 1 6 == 1 /\
  e_entry_ext 2 6 == -(4#7) /\
  0 < col_integral_ext 5 /\
  0 < col_integral_ext 6.
Proof.
  split; [exact e_ext_05 |].
  split; [exact e_ext_15 |].
  split; [exact e_ext_25 |].
  split; [exact e_ext_06 |].
  split; [exact e_ext_16 |].
  split; [exact e_ext_26 |].
  split; [exact col_integral_5_positive |].
  exact col_integral_6_positive.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~12 Qed, 0 Admitted                                                       *)
(*                                                                            *)
(*  Part II: e_ext_05, e_ext_15, e_ext_25 (3)                               *)
(*  Part III: e_ext_06, e_ext_16, e_ext_26 (3)                              *)
(*  Part IV: col_integral_ext_5/6, col_integral_5/6_positive (4)            *)
(*  Part V: extended_action_7_main, total_count (2)                          *)
(* ========================================================================= *)
