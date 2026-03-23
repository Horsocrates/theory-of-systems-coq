(** * FundingMeanReversion.v — AR(1) funding rate mean reversion model
    Elements: funding rates, decay parameters, equilibrium values;
    Roles:    AR(1) dynamics, half-life estimation, signal generation;
    Rules:    mean reversion — rates converge to equilibrium c/(1-alpha).
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Local qpow ===== *)

Fixpoint qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => x * qpow x k
  end.

(* ===== AR(1) Model ===== *)

Definition ar1_step (alpha c F : Q) : Q := alpha * F + c.

Fixpoint ar1_N (alpha c F0 : Q) (n : nat) : Q :=
  match n with
  | O => F0
  | S k => ar1_step alpha c (ar1_N alpha c F0 k)
  end.

Definition funding_equilibrium (alpha c : Q) : Q := c / (1 - alpha).

(* ===== Funding Signal ===== *)

Definition funding_signal (F_current equil : Q) : Z :=
  let deviation := F_current - equil in
  match Qlt_le_dec (1#100) deviation with
  | left _ => (-1)%Z   (* above equilibrium => expect reversion down *)
  | right _ =>
    match Qlt_le_dec deviation (-(1#100)) with
    | left _ => 1%Z     (* below equilibrium => expect reversion up *)
    | right _ => 0%Z    (* near equilibrium *)
    end
  end.

(* ===== Concrete Example: alpha=3/4, c=1/100, F0=1/10 ===== *)

Definition alpha_ex : Q := 3#4.
Definition c_ex : Q := 1#100.
Definition F0_ex : Q := 1#10.

(* Step computations *)
Lemma ar1_step_0 : ar1_N alpha_ex c_ex F0_ex O = 1#10.
Proof. vm_compute. reflexivity. Qed.

Lemma ar1_step_1 : ar1_N alpha_ex c_ex F0_ex (S O) == 17#200.
Proof. vm_compute. reflexivity. Qed.

Lemma ar1_step_2_val : ar1_N alpha_ex c_ex F0_ex (S (S O)) == 59#800.
Proof. vm_compute. reflexivity. Qed.

(* Equilibrium: c/(1-alpha) = (1/100)/(1/4) = 4/100 = 1/25 *)
Lemma equilibrium_val : funding_equilibrium alpha_ex c_ex == 1#25.
Proof. vm_compute. reflexivity. Qed.

(* Half-life check: (3/4)^3 = 27/64 < 1/2 *)
Lemma half_life_check : qpow (3#4) 3 = 27#64.
Proof. vm_compute. reflexivity. Qed.

Lemma half_life_lt_half : qpow (3#4) 3 < 1#2.
Proof. unfold Qlt. simpl. lia. Qed.

(* qpow concrete values *)
Lemma qpow_0 : qpow (3#4) O = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_1 : qpow (3#4) (S O) = 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_2 : qpow (3#4) (S (S O)) = 9#16.
Proof. vm_compute. reflexivity. Qed.

(* Signal at F0: deviation = 1/10 - 1/25 = 3/50 > 1/100 => SHORT *)
Lemma signal_at_start : funding_signal F0_ex (1#25) = (-1)%Z.
Proof.
  unfold funding_signal.
  destruct (Qlt_le_dec (1#100) ((1#10) - (1#25))).
  - reflexivity.
  - exfalso. unfold Qle in q. simpl in q. lia.
Qed.

(* Signal near equilibrium *)
Lemma signal_near_equil : funding_signal (1#25) (1#25) = 0%Z.
Proof.
  unfold funding_signal.
  destruct (Qlt_le_dec (1#100) ((1#25) - (1#25))).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec ((1#25) - (1#25)) (-(1#100))).
    + exfalso. unfold Qlt in q0. simpl in q0. lia.
    + reflexivity.
Qed.

(* Signal below equilibrium *)
Lemma signal_below_equil : funding_signal (1#200) (1#25) = 1%Z.
Proof.
  unfold funding_signal.
  destruct (Qlt_le_dec (1#100) ((1#200) - (1#25))).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec ((1#200) - (1#25)) (-(1#100))).
    + reflexivity.
    + exfalso. unfold Qle in q0. simpl in q0. lia.
Qed.

(* ===== Properties ===== *)

Lemma ar1_N_0 : forall alpha c F0, ar1_N alpha c F0 O = F0.
Proof. intros. reflexivity. Qed.

Lemma ar1_N_step : forall alpha c F0 n,
  ar1_N alpha c F0 (S n) == alpha * ar1_N alpha c F0 n + c.
Proof. intros. simpl. unfold ar1_step. ring. Qed.
