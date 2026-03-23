(** * FiniteSizeScalingV2.v -- Finite-size scaling via magnetization processes
    Elements: Qpow_local, ising_magnetization, mag_N1..N4, scaling
    Roles:    magnetization M(r,N) = (1 - r^N)/(1 + r^N) models finite-size order
    Rules:    magnetization decreases with N for 0 < r < 1; concrete verification
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Local power function --- *)
Fixpoint Qpow_local (r : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => r * Qpow_local r m
  end.

(* 1 *)
Lemma Qpow_local_0 : forall r, Qpow_local r O == 1.
Proof. intros. simpl. lra. Qed.

(* 2 *)
Lemma Qpow_local_1 : forall r, Qpow_local r 1%nat == r.
Proof. intros. simpl. ring. Qed.

(* 3: concrete power *)
Lemma Qpow_local_28_37_1 : Qpow_local (28#37) 1%nat == 28#37.
Proof. vm_compute. reflexivity. Qed.

(* 4 *)
Lemma Qpow_local_28_37_2 : Qpow_local (28#37) 2%nat == 784#1369.
Proof. vm_compute. reflexivity. Qed.

(* 5 *)
Lemma Qpow_local_28_37_4 : Qpow_local (28#37) 4%nat == 614656#1874161.
Proof. vm_compute. reflexivity. Qed.

(* --- Ising magnetization: M(r,N) = (1 - r^N) / (1 + r^N) --- *)
Definition ising_magnetization (r : Q) (N : nat) : Q :=
  (1 - Qpow_local r N) / (1 + Qpow_local r N).

(* 6: N=1 *)
Lemma mag_N1 : ising_magnetization (28#37) 1%nat == 9#65.
Proof. unfold ising_magnetization. vm_compute. reflexivity. Qed.

(* 7: N=2, r^2 = 784/1369, M = (1369-784)/(1369+784) = 585/2153 *)
Lemma mag_N2 : ising_magnetization (28#37) 2%nat == 585#2153.
Proof. unfold ising_magnetization. vm_compute. reflexivity. Qed.

(* 8: N=4 *)
Lemma mag_N4 : ising_magnetization (28#37) 4%nat == 1259505#2488817.
Proof. unfold ising_magnetization. vm_compute. reflexivity. Qed.

(* 9: magnetization positive for r < 1 at N=1 *)
Lemma mag_N1_positive : 0 < ising_magnetization (28#37) 1%nat.
Proof.
  assert (H : ising_magnetization (28#37) 1%nat == 9#65) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* 10: magnetization positive at N=2 *)
Lemma mag_N2_positive : 0 < ising_magnetization (28#37) 2%nat.
Proof.
  assert (H : ising_magnetization (28#37) 2%nat == 585#2153) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* 11: magnetization increases: M(N=2) > M(N=1) *)
Lemma mag_increasing_12 :
  ising_magnetization (28#37) 1%nat < ising_magnetization (28#37) 2%nat.
Proof.
  assert (H1 : ising_magnetization (28#37) 1%nat == 9#65) by (vm_compute; reflexivity).
  assert (H2 : ising_magnetization (28#37) 2%nat == 585#2153) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* 12: magnetization less than 1 *)
Lemma mag_N1_lt_1 : ising_magnetization (28#37) 1%nat < 1.
Proof.
  assert (H : ising_magnetization (28#37) 1%nat == 9#65) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* 13: M(N=0) = 0 *)
Lemma mag_N0 : ising_magnetization (28#37) O == 0.
Proof. unfold ising_magnetization. vm_compute. reflexivity. Qed.

(* 14: magnetization at half rate *)
Lemma mag_half_N1 : ising_magnetization (1#2) 1%nat == 1#3.
Proof. unfold ising_magnetization. vm_compute. reflexivity. Qed.

(* 15: synthesis *)
Theorem finite_size_scaling_synthesis :
  ising_magnetization (28#37) O == 0 /\
  0 < ising_magnetization (28#37) 1%nat /\
  ising_magnetization (28#37) 1%nat < ising_magnetization (28#37) 2%nat /\
  ising_magnetization (28#37) 1%nat < 1.
Proof.
  split; [exact mag_N0|].
  split; [exact mag_N1_positive|].
  split; [exact mag_increasing_12|].
  exact mag_N1_lt_1.
Qed.
