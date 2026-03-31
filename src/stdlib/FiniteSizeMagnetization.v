(** * FiniteSizeMagnetization.v — Ising magnetization scaling with system size
    Elements: qpow, ising_magnetization, concrete values at r=28/37
    Roles:    model magnetization as (1-r^N)/(1+r^N) for transfer matrix ratio r
    Rules:    monotone approach to 1 as N grows; concrete N=1,2,3 values
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Local qpow --- *)
Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => b * qpow b k
  end.

(* --- Ising magnetization --- *)
Definition ising_magnetization (r : Q) (N : nat) : Q :=
  (1 - qpow r N) / (1 + qpow r N).

Definition ising_r : Q := 28 # 37.

(* 1 *)
Lemma qpow_0 : forall b, qpow b O == 1.
Proof. intros. vm_compute. reflexivity. Qed.

(* 2 *)
Lemma qpow_1 : forall b, qpow b 1%nat == b.
Proof. intros. simpl. ring. Qed.

(* 3: magnetization at N=0 is 0 *)
Lemma mag_N0 : forall r, ising_magnetization r O == 0.
Proof. intros. unfold ising_magnetization. simpl. field. Qed.

(* 4: concrete r^1 *)
Lemma ising_r_pow1 : qpow ising_r 1%nat == 28 # 37.
Proof. unfold ising_r. vm_compute. reflexivity. Qed.

(* 5: concrete r^2 *)
Lemma ising_r_pow2 : qpow ising_r 2%nat == 784 # 1369.
Proof. unfold ising_r. vm_compute. reflexivity. Qed.

(* 6: concrete r^3 *)
Lemma ising_r_pow3 : qpow ising_r 3%nat == 21952 # 50653.
Proof. unfold ising_r. vm_compute. reflexivity. Qed.

(* 7: magnetization at N=1 *)
Lemma mag_N1 : ising_magnetization ising_r 1%nat == 9 # 65.
Proof. unfold ising_magnetization, ising_r. vm_compute. reflexivity. Qed.

(* 8: magnetization at N=2 *)
Lemma mag_N2 : ising_magnetization ising_r 2%nat == 585 # 2153.
Proof. unfold ising_magnetization, ising_r. vm_compute. reflexivity. Qed.

(* 9: magnetization at N=3 *)
Lemma mag_N3 : ising_magnetization ising_r 3%nat == 28701 # 72605.
Proof. unfold ising_magnetization, ising_r. vm_compute. reflexivity. Qed.

(* 10: monotonicity: mag(N=1) < mag(N=2) *)
Lemma mag_mono_12 : ising_magnetization ising_r 1%nat < ising_magnetization ising_r 2%nat.
Proof.
  assert (H1 : ising_magnetization ising_r 1%nat == 9#65)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  assert (H2 : ising_magnetization ising_r 2%nat == 585#2153)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* 11: monotonicity: mag(N=2) < mag(N=3) *)
Lemma mag_mono_23 : ising_magnetization ising_r 2%nat < ising_magnetization ising_r 3%nat.
Proof.
  assert (H2 : ising_magnetization ising_r 2%nat == 585#2153)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  assert (H3 : ising_magnetization ising_r 3%nat == 28701#72605)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  rewrite H2, H3. lra.
Qed.

(* 12: Qabs of ising_r *)
Lemma ising_r_abs : Qabs ising_r == 28 # 37.
Proof. unfold ising_r. vm_compute. reflexivity. Qed.

(* 13: r is strictly between 0 and 1 *)
Lemma ising_r_bounds : 0 < ising_r /\ ising_r < 1.
Proof. unfold ising_r. split; lra. Qed.

(* 14: magnetization at N=1 is positive *)
Lemma mag_N1_positive : 0 < ising_magnetization ising_r 1%nat.
Proof.
  assert (H1 : ising_magnetization ising_r 1%nat == 9#65)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  rewrite H1. lra.
Qed.

(* 15: all three magnetizations are less than 1 *)
Lemma mag_all_less_one :
  ising_magnetization ising_r 1%nat < 1 /\
  ising_magnetization ising_r 2%nat < 1 /\
  ising_magnetization ising_r 3%nat < 1.
Proof.
  assert (H1 : ising_magnetization ising_r 1%nat == 9#65)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  assert (H2 : ising_magnetization ising_r 2%nat == 585#2153)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  assert (H3 : ising_magnetization ising_r 3%nat == 28701#72605)
    by (unfold ising_magnetization, ising_r; vm_compute; reflexivity).
  rewrite H1, H2, H3. repeat split; lra.
Qed.
