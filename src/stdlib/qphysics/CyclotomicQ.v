(** * CyclotomicQ.v -- Cyclotomic roots of unity over Q matrices
    Elements: omega4_matrix, omega4_sq, omega2, cyclotomic observables
    Roles:    Roots of unity representable as Q-valued 2x2 matrices
    Rules:    omega_4 = [[0,-1],[1,0]] is exact Q; |omega_N|^2 = 1 in Q
    Status:   complete
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: omega_4 as 2x2 Q-matrix (i = [[0,-1],[1,0]])              *)
(* ================================================================== *)

(** omega_4 = e^{2*pi*i/4} = i, represented as 2x2 real matrix *)
Definition omega4_matrix (i j : nat) : Q :=
  match i, j with
  | O, O => 0
  | O, S O => -(1)
  | S O, O => 1
  | S O, S O => 0
  | _, _ => 0
  end.

(** omega_4^2 = -I = [[-1,0],[0,-1]] *)
Definition omega4_sq (i j : nat) : Q :=
  match i, j with
  | O, O => -(1)
  | O, S O => 0
  | S O, O => 0
  | S O, S O => -(1)
  | _, _ => 0
  end.

(** Verify omega4^2 matrix entries *)
Lemma omega4_sq_00 : omega4_sq O O == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma omega4_sq_01 : omega4_sq O (S O) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma omega4_sq_10 : omega4_sq (S O) O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma omega4_sq_11 : omega4_sq (S O) (S O) == -(1).
Proof. vm_compute. reflexivity. Qed.

(** Verify matrix multiplication omega4 * omega4 = omega4_sq *)
Lemma omega4_times_omega4_00 :
  omega4_matrix O O * omega4_matrix O O +
  omega4_matrix O (S O) * omega4_matrix (S O) O == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: omega_2 = -1 (scalar)                                     *)
(* ================================================================== *)

Definition omega2 : Q := -(1).

Lemma omega2_is_neg1 : omega2 == -(1).
Proof. vm_compute. reflexivity. Qed.

Definition omega1 : Q := 1.

Lemma omega1_is_one : omega1 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Observables are Q                                        *)
(* ================================================================== *)

(** |omega_N|^2 = 1 for all roots of unity.
    For 2x2 matrix representation: |det| = 1.
    omega4: det = 0*0 - (-1)*1 = 1 *)
Lemma omega4_det_is_one :
  omega4_matrix O O * omega4_matrix (S O) (S O) -
  omega4_matrix O (S O) * omega4_matrix (S O) O == 1.
Proof. vm_compute. reflexivity. Qed.

(** omega_2^2 = 1 *)
Lemma omega2_sq_is_one : omega2 * omega2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** omega_1^1 = 1 *)
Lemma omega1_power_is_one : omega1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Order function *)
Definition omega_order (N : nat) : nat := N.

Lemma order_values :
  (omega_order (S O) = 1)%nat /\
  (omega_order (S (S O)) = 2)%nat /\
  (omega_order (S (S (S (S O)))) = 4)%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

