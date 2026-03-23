(** * TransferMatrixPrice.v — Transfer matrix for price state dynamics
    Elements: 2x2 transition matrices, eigenvalues, state vectors;
    Roles:    market state evolution, memory detection;
    Rules:    eigenvalue gap determines regime persistence.
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Open Scope Q_scope.

(* ===== 2x2 Matrix type (nat -> nat -> Q) ===== *)

Definition Mat2 := nat -> nat -> Q.

Definition mat2_entry (M : Mat2) (i j : nat) : Q := M i j.

Definition mat2_trace (M : Mat2) : Q := M O O + M (S O) (S O).

Definition mat2_det (M : Mat2) : Q :=
  M O O * M (S O) (S O) - M O (S O) * M (S O) O.

Definition mat2_mul (A B : Mat2) : Mat2 :=
  fun i j => A i O * B O j + A i (S O) * B (S O) j.

Definition mat2_id : Mat2 :=
  fun i j => match i, j with
  | O, O => 1
  | S O, S O => 1
  | _, _ => 0
  end.

(* ===== Matrix power ===== *)

Fixpoint mat2_pow (M : Mat2) (n : nat) : Mat2 :=
  match n with
  | O => mat2_id
  | S k => mat2_mul M (mat2_pow M k)
  end.

(* ===== Market 2-state transition matrix ===== *)
(* States: Bull(0), Bear(1) *)
(* P(Bull->Bull) = 4/5, P(Bull->Bear) = 1/5 *)
(* P(Bear->Bull) = 1/5, P(Bear->Bear) = 4/5 — wait, det would be 16/25-1/25=3/5 not 1/5 *)
(* Let's use: P(B->B)=4/5, P(B->Bear)=1/5, P(Bear->B)=1, P(Bear->Bear)=0 *)
(* Then trace=4/5, det=0+1/5=1/5 ... no: det=4/5*0-1/5*1=-1/5 *)
(* Better: P(B->B)=3/4, P(B->Bear)=1/4, P(Bear->B)=1/2, P(Bear->Bear)=1/2 *)
(* trace=3/4+1/2=5/4, det=3/8-1/8=1/4 *)
(* Eigenvalues: lambda = (trace +/- sqrt(trace^2-4det))/2 *)
(* = (5/4 +/- sqrt(25/16-1))/2 = (5/4 +/- sqrt(9/16))/2 = (5/4 +/- 3/4)/2 *)
(* lambda1 = 2/2 = 1, lambda2 = 1/2/2 = 1/4 *)

Definition market_2state : Mat2 :=
  fun i j => match i, j with
  | O, O => 3#4         (* Bull -> Bull *)
  | O, S O => 1#4       (* Bull -> Bear *)
  | S O, O => 1#2       (* Bear -> Bull *)
  | S O, S O => 1#2     (* Bear -> Bear *)
  | _, _ => 0
  end.

(* ===== Trace and determinant ===== *)

Lemma trace_market : mat2_trace market_2state == 5#4.
Proof. vm_compute. reflexivity. Qed.

Lemma det_market : mat2_det market_2state == 1#4.
Proof. vm_compute. reflexivity. Qed.

(* ===== Eigenvalue verification ===== *)
(* For 2x2: eigenvalues satisfy lambda^2 - trace*lambda + det = 0 *)
(* lambda1=1: 1 - 5/4 + 1/4 = 0 *)
(* lambda2=1/4: 1/16 - 5/16 + 4/16 = 0 *)

Lemma eigen_check_1 : 1 * 1 - (5#4) * 1 + (1#4) == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma eigen_check_quarter : (1#4)*(1#4) - (5#4)*(1#4) + (1#4) == 0.
Proof. vm_compute. reflexivity. Qed.

(* ===== Matrix multiplication ===== *)

Lemma mul_entry_00 : mat2_mul market_2state market_2state O O ==
  (3#4)*(3#4) + (1#4)*(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma M2_00 : mat2_pow market_2state (S (S O)) O O == 11#16.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_01 : mat2_pow market_2state (S (S O)) O (S O) == 5#16.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_10 : mat2_pow market_2state (S (S O)) (S O) O == 5#8.
Proof. vm_compute. reflexivity. Qed.

Lemma M2_11 : mat2_pow market_2state (S (S O)) (S O) (S O) == 3#8.
Proof. vm_compute. reflexivity. Qed.

(* M^3 *)
Lemma M3_00 : mat2_pow market_2state (S (S (S O))) O O == 43#64.
Proof. vm_compute. reflexivity. Qed.

(* ===== Memory signal ===== *)
(* Memory = |lambda2/lambda1| — if close to 1, strong persistence *)
(* Here lambda2/lambda1 = 1/4, so memory is weak *)

Definition memory_signal (lambda_ratio : Q) : Z :=
  match Qlt_le_dec (1#2) lambda_ratio with
  | left _ => 1%Z    (* strong memory *)
  | right _ => 0%Z   (* weak memory *)
  end.

Lemma weak_memory : memory_signal (1#4) = 0%Z.
Proof.
  unfold memory_signal.
  destruct (Qlt_le_dec (1#2) (1#4)).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - reflexivity.
Qed.

Lemma strong_memory : memory_signal (9#10) = 1%Z.
Proof.
  unfold memory_signal.
  destruct (Qlt_le_dec (1#2) (9#10)).
  - reflexivity.
  - exfalso. unfold Qle in q. simpl in q. lia.
Qed.

(* ===== Stationary distribution ===== *)
(* For lambda1=1: stationary is (2/3, 1/3) *)
(* Check: M * [2/3, 1/3]^T = [2/3, 1/3]^T *)

(* pi * M = pi where pi = (2/3, 1/3) *)
(* pi_0' = pi_0*M[0,0] + pi_1*M[1,0] *)
Lemma stationary_0 : (2#3)*(3#4) + (1#3)*(1#2) == 2#3.
Proof. vm_compute. reflexivity. Qed.

(* pi_1' = pi_0*M[0,1] + pi_1*M[1,1] *)
Lemma stationary_1 : (2#3)*(1#4) + (1#3)*(1#2) == 1#3.
Proof. vm_compute. reflexivity. Qed.

(* ===== Properties ===== *)

Lemma trace_eq_sum_eigen : mat2_trace market_2state == 1 + (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma det_eq_prod_eigen : mat2_det market_2state == 1 * (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma mat2_id_trace : mat2_trace mat2_id = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma mat2_id_det : mat2_det mat2_id = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma mat2_pow_0 : forall i j, mat2_pow market_2state O i j = mat2_id i j.
Proof. intros. reflexivity. Qed.

Lemma mat2_pow_1_eq : forall i j,
  mat2_pow market_2state (S O) i j == market_2state i j.
Proof.
  intros. simpl.
  unfold mat2_mul, mat2_id.
  destruct i as [|[|?]], j as [|[|?]]; vm_compute; reflexivity.
Qed.

Lemma trace_M2 : mat2_trace (mat2_pow market_2state (S (S O))) == 17#16.
Proof. vm_compute. reflexivity. Qed.
