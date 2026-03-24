(** * HydrogenTwoMatrices.v -- Product eigenvalue structure for hydrogen
    Elements: T_angular, eigenvalue products, t_j² values
    Roles:    Angular matrix T and its squared eigenvalues
    Rules:    t_j² concrete values for small j, product structure
    Status:   Stdlib
    STATUS: 11 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

(* ================================================================== *)
(*  ANGULAR MATRIX T (tridiagonal, Jacobi-like)                       *)
(* ================================================================== *)

(** Angular coupling matrix entry T(l, l', lmax).
    Tridiagonal: T(l,l) = 0, T(l,l±1) = coupling coefficient *)
Definition T_angular (lmax l l' : nat) : Q :=
  let lq := inject_Z (Z.of_nat l) in
  let lmaxq := inject_Z (Z.of_nat lmax) in
  if Nat.eqb l l' then 0
  else if Nat.eqb (S l) l' then
    (* T(l, l+1) = (l+1) / sqrt((2l+1)(2l+3)) approximated rationally *)
    (inject_Z (Z.of_nat (S l))) / (2 * lq + 2)
  else if Nat.eqb l (S l') then
    (inject_Z (Z.of_nat l)) / (2 * lq)
  else 0.

Open Scope Q_scope.

(** Diagonal entries are zero *)
Lemma T_diag_0 : T_angular 3 0 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma T_diag_1 : T_angular 3 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma T_diag_2 : T_angular 3 2 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Off-diagonal: T(0,1) = 1/2 *)
Lemma T_off_01 : T_angular 3 0 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** Off-diagonal: T(1,2) = 2/4 = 1/2 *)
Lemma T_off_12 : T_angular 3 1 2 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SQUARED EIGENVALUES: t_j²                                         *)
(* ================================================================== *)

(** For the 2×2 angular matrix (lmax=2), the squared eigenvalue
    t₁² = T(0,1) * T(1,0) = 1/4 *)
Definition t_sq_1 : Q := T_angular 2 0 1 * T_angular 2 1 0.

Lemma t_sq_1_value : t_sq_1 == 1#4.
Proof. vm_compute. reflexivity. Qed.

(** For a 3×3 case, product structure *)
Definition angular_product_3 : Q :=
  T_angular 3 0 1 * T_angular 3 1 0 +
  T_angular 3 1 2 * T_angular 3 2 1.

Lemma angular_product_3_value : angular_product_3 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF T²                                                        *)
(* ================================================================== *)

Definition trace_T2 (lmax : nat) : Q :=
  let fix sum_diag (k : nat) : Q :=
    match k with
    | O => 0
    | S k' =>
      sum_diag k' +
      (let fix row_sum (j : nat) : Q :=
        match j with
        | O => T_angular lmax k' 0 * T_angular lmax 0 k'
        | S j' => row_sum j' + T_angular lmax k' (S j') * T_angular lmax (S j') k'
        end
      in row_sum (pred lmax))
    end
  in sum_diag lmax.

Lemma trace_T2_lmax2 : trace_T2 2 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_T2_lmax3 : trace_T2 3 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Trace grows with lmax *)
Lemma trace_T2_grows : trace_T2 2 < trace_T2 3.
Proof. vm_compute. reflexivity. Qed.

(** Product eigenvalue symmetry: T(i,j)*T(j,i) is the same pair *)
Lemma product_symmetric : T_angular 3 0 1 * T_angular 3 1 0 ==
                           T_angular 3 1 0 * T_angular 3 0 1.
Proof. vm_compute. reflexivity. Qed.
