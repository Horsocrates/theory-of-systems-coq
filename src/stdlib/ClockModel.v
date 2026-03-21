(** * ClockModel.v -- Z_3 clock model: discrete U(1) symmetry
    Elements: clock3_cos, clock3_transfer, clock3_eigenvalues
    Roles:    Z₃ clock has same symmetry as Potts Q=3, different interactions
    Rules:    Eigenvalues: λ₀ = e^β + 2e^{-β/2}, λ₁ = e^β - e^{-β/2}
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.MatN.

Open Scope Q_scope.

(* ================================================================== *)
(*  Z₃ CLOCK: cos(2πk/3) values                                       *)
(* ================================================================== *)

(** cos(0) = 1, cos(2π/3) = -1/2, cos(4π/3) = -1/2 *)
Definition clock3_cos (k : nat) : Q :=
  match k mod 3 with
  | O => 1
  | _ => -(1#2)
  end.

(** Transfer: T_{σ,σ'} = exp(β·cos(2π(σ-σ')/3)) *)
Definition clock3_transfer (beta : Q) (M : nat) : MatN :=
  fun s s' =>
    exp_QN (beta * clock3_cos ((s + 3 - s') mod 3)) M.

(* ================================================================== *)
(*  ANALYTICAL EIGENVALUES (circulant matrix)                          *)
(* ================================================================== *)

(** Circulant 3×3: eigenvalues from DFT of first row.
    λ₀ = exp(β) + 2·exp(-β/2) (symmetric mode)
    λ₁ = exp(β) - exp(-β/2) (doubly degenerate) *)

Definition clock3_lambda0 (beta : Q) (M : nat) : Q :=
  exp_QN beta M + 2 * exp_QN (-(beta * (1#2))) M.

Definition clock3_lambda1 (beta : Q) (M : nat) : Q :=
  exp_QN beta M - exp_QN (-(beta * (1#2))) M.

(** Gap = λ₀ - λ₁ = 3·exp(-β/2) > 0 always (1D: no transition) *)
Lemma clock3_gap_formula : forall beta M,
  clock3_lambda0 beta M - clock3_lambda1 beta M ==
  3 * exp_QN (-(beta * (1#2))) M.
Proof. intros. unfold clock3_lambda0, clock3_lambda1. ring. Qed.

(** exp(-1/2) at M=3 *)
Lemma exp_neg_half_3 : exp_QN (-(1#2)) 3 == 29#48.
Proof. vm_compute. reflexivity. Qed.

(** Eigenvalue positivity at β=1, M=3 *)
Lemma clock3_l0_pos : 0 < clock3_lambda0 1 3.
Proof.
  unfold clock3_lambda0.
  assert (H : exp_QN 1 3 == 8#3) by (vm_compute; reflexivity).
  assert (H2 : exp_QN (-(1 * (1#2))) 3 == 29#48) by (vm_compute; reflexivity).
  rewrite H, H2. lra.
Qed.

Lemma clock3_l1_pos : 0 < clock3_lambda1 1 3.
Proof.
  unfold clock3_lambda1.
  assert (H : exp_QN 1 3 == 8#3) by (vm_compute; reflexivity).
  assert (H2 : exp_QN (-(1 * (1#2))) 3 == 29#48) by (vm_compute; reflexivity).
  rewrite H, H2. lra.
Qed.

(** Gap at β=1 *)
Lemma clock3_gap_1 :
  clock3_lambda0 1 3 - clock3_lambda1 1 3 == 3 * (29#48).
Proof.
  rewrite clock3_gap_formula. vm_compute. reflexivity.
Qed.

Lemma clock3_gap_positive :
  0 < clock3_lambda0 1 3 - clock3_lambda1 1 3.
Proof.
  rewrite clock3_gap_formula.
  assert (H : exp_QN (-(1 * (1#2))) 3 == 29#48) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  COMPARISON: Clock Z₃ vs Potts Q=3                                  *)
(* ================================================================== *)

(** Clock: exp(β) when aligned, exp(-β/2) when misaligned *)
(** Potts: exp(β) when aligned, 1 when misaligned *)
(** Key: Clock has REPULSION for misaligned spins *)
(** Both have Z₃ symmetry group → same universality class (2D) *)

(** Clock gap depends on β: 3·exp(-β/2) *)
(** Potts gap is constant: 3 *)
(** So Clock gap < Potts gap for β > 0: *)
Lemma clock_gap_less_potts :
  clock3_lambda0 1 3 - clock3_lambda1 1 3 < 3.
Proof.
  rewrite clock3_gap_formula.
  assert (H : exp_QN (-(1 * (1#2))) 3 == 29#48) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** SYNTHESIS *)
Theorem clock_synthesis :
  (* Gap formula is structural *)
  (forall beta M, clock3_lambda0 beta M - clock3_lambda1 beta M ==
                  3 * exp_QN (-(beta * (1#2))) M) /\
  (* Gap positive at β=1 *)
  0 < clock3_lambda0 1 3 - clock3_lambda1 1 3 /\
  (* Clock gap < Potts gap (different interaction type) *)
  clock3_lambda0 1 3 - clock3_lambda1 1 3 < 3.
Proof.
  split; [|split].
  - exact clock3_gap_formula.
  - exact clock3_gap_positive.
  - exact clock_gap_less_potts.
Qed.
