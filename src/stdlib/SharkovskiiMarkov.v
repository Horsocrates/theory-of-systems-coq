(** SharkovskiiMarkov.v — Markov graph from periodic orbit *)
(** E/R/R: Elements = intervals I1,I2; Roles = covering relations; Rules = adjacency matrix *)
From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(** covers: does f([left,right]) contain [j_left, j_right]? *)
Definition covers (f_left f_right j_left j_right : Q) : bool :=
  let fmin := if Qle_bool f_left f_right then f_left else f_right in
  let fmax := if Qle_bool f_left f_right then f_right else f_left in
  Qle_bool fmin j_left && Qle_bool j_right fmax.

(** Period-3: a < b < c, f(a)=b, f(b)=c, f(c)=a *)
(** I1=[a,b], I2=[b,c] *)
(** Concrete: a=0, b=1/2, c=1 *)

(** f maps I1=[0,1/2]: f(0)=1/2, f(1/2)=1. Image=[1/2,1] superset I2=[1/2,1] *)
Lemma period3_I1_covers_I2 : covers (1#2) 1 (1#2) 1 = true.
Proof. vm_compute. reflexivity. Qed.

(** f maps I2=[1/2,1]: f(1/2)=1, f(1)=0. Image=[0,1] superset I1=[0,1/2] *)
Lemma period3_I2_covers_I1 : covers 1 0 0 (1#2) = true.
Proof. vm_compute. reflexivity. Qed.

(** Image=[0,1] superset I2=[1/2,1] *)
Lemma period3_I2_covers_I2 : covers 1 0 (1#2) 1 = true.
Proof. vm_compute. reflexivity. Qed.

(** Adjacency matrix: M = [[0,1],[1,1]] = golden mean matrix *)
Definition period3_adj (i j : nat) : nat :=
  match i, j with
  | O, O => O | O, S O => S O
  | S O, O => S O | S O, S O => S O
  | _, _ => O
  end.

Lemma adj_01 : period3_adj O (S O) = S O.
Proof. reflexivity. Qed.

Lemma adj_10 : period3_adj (S O) O = S O.
Proof. reflexivity. Qed.

Lemma adj_11 : period3_adj (S O) (S O) = S O.
Proof. reflexivity. Qed.

Lemma adj_00 : period3_adj O O = O.
Proof. reflexivity. Qed.

(** I1 does NOT self-cover *)
Lemma period3_I1_not_self : covers (1#2) 1 0 (1#2) = false.
Proof. vm_compute. reflexivity. Qed.

(** Trace = 1: tr(M) = M(0,0) + M(1,1) = 0 + 1 = 1 *)
Lemma adj_trace : (period3_adj O O + period3_adj (S O) (S O) = S O)%nat.
Proof. simpl. reflexivity. Qed.

(** Determinant = -1 (golden characteristic): det = M(0,0)*M(1,1) - M(0,1)*M(1,0) = 0-1 = -1 *)
Lemma adj_det : (period3_adj O O * period3_adj (S O) (S O) -
                 period3_adj O (S O) * period3_adj (S O) O = 0)%nat.
(* In nat: 0*1 - 1*1 wraps to 0. We verify over Z instead. *)
Proof. simpl. reflexivity. Qed.

Lemma adj_det_Z : ((Z.of_nat (period3_adj O O) * Z.of_nat (period3_adj (S O) (S O)) -
                    Z.of_nat (period3_adj O (S O)) * Z.of_nat (period3_adj (S O) O)) = -1)%Z.
Proof. vm_compute. reflexivity. Qed.

(** Row sums *)
Lemma adj_row0_sum : (period3_adj O O + period3_adj O (S O) = S O)%nat.
Proof. simpl. reflexivity. Qed.

Lemma adj_row1_sum : (period3_adj (S O) O + period3_adj (S O) (S O) = S (S O))%nat.
Proof. simpl. reflexivity. Qed.

(** Characteristic polynomial: lambda^2 - lambda - 1 = 0 *)
(** Golden ratio phi = (1+sqrt5)/2 is eigenvalue *)
(** Verify: phi^2 = phi+1 concretely via trace/det *)
Lemma golden_char :
  (period3_adj O O + period3_adj (S O) (S O) = S O)%nat /\
  ((Z.of_nat (period3_adj O O) * Z.of_nat (period3_adj (S O) (S O)) -
    Z.of_nat (period3_adj O (S O)) * Z.of_nat (period3_adj (S O) O)) = -1)%Z.
Proof.
  split.
  - exact adj_trace.
  - exact adj_det_Z.
Qed.
