(* BoltzmannProcess.v *)
(* Elements: T_bp matrix, symmetric stochastic kernel *)
(* Roles: transition probabilities for 2-state Boltzmann process *)
(* Rules: symmetry, stochasticity, concrete computations *)

From Coq Require Import QArith Lia Lqa.

Open Scope Q_scope.

(* ===== Boltzmann Process: 2x2 Symmetric Stochastic Matrix ===== *)

Definition T_bp (p : Q) (i j : nat) : Q :=
  if andb (Nat.eqb i 0%nat) (Nat.eqb j 0%nat) then 1 - p
  else if andb (Nat.eqb i 0%nat) (Nat.eqb j 1%nat) then p
  else if andb (Nat.eqb i 1%nat) (Nat.eqb j 0%nat) then p
  else if andb (Nat.eqb i 1%nat) (Nat.eqb j 1%nat) then 1 - p
  else 0.

(* --- Concrete values for p = 1/3 --- *)

Lemma T_bp_00 : T_bp (1#3) 0 0 == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_01 : T_bp (1#3) 0 1 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_10 : T_bp (1#3) 1 0 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_11 : T_bp (1#3) 1 1 == 2#3.
Proof. vm_compute. reflexivity. Qed.

(* --- Symmetry: T_bp p i j == T_bp p j i for i,j in {0,1} --- *)

Lemma T_bp_symmetric_01 : forall p, T_bp p 0 1 == T_bp p 1 0.
Proof. intros p. unfold T_bp. simpl. ring. Qed.

Lemma T_bp_symmetric : forall p i j,
  (i < 2)%nat -> (j < 2)%nat -> T_bp p i j == T_bp p j i.
Proof.
  intros p i j Hi Hj.
  destruct i as [|[|n]]; destruct j as [|[|m]]; unfold T_bp; simpl; try ring; try lia.
Qed.

(* --- Stochastic: row sums = 1 --- *)

Lemma T_bp_row0_sum : forall p, T_bp p 0 0 + T_bp p 0 1 == 1.
Proof. intros p. unfold T_bp. simpl. ring. Qed.

Lemma T_bp_row1_sum : forall p, T_bp p 1 0 + T_bp p 1 1 == 1.
Proof. intros p. unfold T_bp. simpl. ring. Qed.

(* --- T^2: matrix square via sum over intermediate --- *)

Definition T_bp_sq (p : Q) (i j : nat) : Q :=
  T_bp p i 0 * T_bp p 0 j + T_bp p i 1 * T_bp p 1 j.

Lemma T_bp_sq_00 : T_bp_sq (1#3) 0 0 == 5#9.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_sq_01 : T_bp_sq (1#3) 0 1 == 4#9.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_sq_symmetric : forall p, T_bp_sq p 0 1 == T_bp_sq p 1 0.
Proof.
  intros p. unfold T_bp_sq, T_bp. simpl. ring.
Qed.

(* --- Time-symmetric kernel property --- *)

Lemma time_symmetric_kernel : forall p,
  T_bp_sq p 0 1 == T_bp_sq p 1 0.
Proof. exact T_bp_sq_symmetric. Qed.

(* --- Equilibrium: at p=0 identity --- *)

Lemma T_bp_identity_00 : T_bp 0 0 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma T_bp_identity_01 : T_bp 0 0 1 == 0.
Proof. vm_compute. reflexivity. Qed.
