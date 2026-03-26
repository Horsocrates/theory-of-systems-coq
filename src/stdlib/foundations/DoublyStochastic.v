(* DoublyStochastic.v *)
(* Elements: T_distinction matrix, doubly stochastic kernel *)
(* Roles: symmetric + row/column stochastic = doubly stochastic *)
(* Rules: symmetry, row sums, column sums, concrete values *)

From Coq Require Import QArith Lia Lqa.

Open Scope Q_scope.

(* ===== Doubly Stochastic Matrix for Distinction Process ===== *)

Definition T_distinction (p : Q) (i j : nat) : Q :=
  if andb (Nat.eqb i 0%nat) (Nat.eqb j 0%nat) then 1 - p
  else if andb (Nat.eqb i 0%nat) (Nat.eqb j 1%nat) then p
  else if andb (Nat.eqb i 1%nat) (Nat.eqb j 0%nat) then p
  else if andb (Nat.eqb i 1%nat) (Nat.eqb j 1%nat) then 1 - p
  else 0.

(* --- Symmetry: universal for i,j in {0,1} --- *)

Lemma T_symmetric : forall p i j,
  (i < 2)%nat -> (j < 2)%nat -> T_distinction p i j == T_distinction p j i.
Proof.
  intros p i j Hi Hj.
  destruct i as [|[|n]]; destruct j as [|[|m]]; unfold T_distinction; simpl; try ring; try lia.
Qed.

(* --- Row sums = 1 (stochastic) --- *)

Lemma T_row0_sum : forall p, T_distinction p 0 0 + T_distinction p 0 1 == 1.
Proof. intros p. unfold T_distinction. simpl. ring. Qed.

Lemma T_row1_sum : forall p, T_distinction p 1 0 + T_distinction p 1 1 == 1.
Proof. intros p. unfold T_distinction. simpl. ring. Qed.

(* --- Column sums = 1 (doubly stochastic) --- *)

Lemma T_col0_sum : forall p, T_distinction p 0 0 + T_distinction p 1 0 == 1.
Proof. intros p. unfold T_distinction. simpl. ring. Qed.

Lemma T_col1_sum : forall p, T_distinction p 0 1 + T_distinction p 1 1 == 1.
Proof. intros p. unfold T_distinction. simpl. ring. Qed.

(* --- Concrete values for p = 1/3 --- *)

Lemma T_concrete_00 : T_distinction (1#3) 0 0 == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_concrete_01 : T_distinction (1#3) 0 1 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_concrete_10 : T_distinction (1#3) 1 0 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma T_concrete_11 : T_distinction (1#3) 1 1 == 2#3.
Proof. vm_compute. reflexivity. Qed.

(* --- Concrete values for p = 1/4 --- *)

Lemma T_quarter_00 : T_distinction (1#4) 0 0 == 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma T_quarter_01 : T_distinction (1#4) 0 1 == 1#4.
Proof. vm_compute. reflexivity. Qed.

(* --- Concrete values for p = 1/2 (fully mixing) --- *)

Lemma T_half_00 : T_distinction (1#2) 0 0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma T_half_01 : T_distinction (1#2) 0 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* --- Doubly stochastic = symmetric + row stochastic --- *)

Theorem T_doubly_stochastic : forall p,
  (T_distinction p 0 0 + T_distinction p 0 1 == 1) /\
  (T_distinction p 1 0 + T_distinction p 1 1 == 1) /\
  (T_distinction p 0 0 + T_distinction p 1 0 == 1) /\
  (T_distinction p 0 1 + T_distinction p 1 1 == 1).
Proof.
  intros p. unfold T_distinction. simpl.
  split; [ring | split; [ring | split; ring]].
Qed.
