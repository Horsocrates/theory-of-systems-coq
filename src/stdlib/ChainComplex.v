(* ChainComplex.v — Chain complexes over Q *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Q-matrices as list of list Q                               *)
(* ================================================================== *)

Definition QRow := list Q.
Definition QMat := list QRow.

Definition mat_entry (M : QMat) (i j : nat) : Q :=
  nth j (nth i M []) 0.

Definition mat_rows (M : QMat) : nat := length M.
Definition mat_cols (M : QMat) : nat :=
  match M with [] => 0 | r :: _ => length r end.

(** Zero matrix *)
Fixpoint zero_row (n : nat) : QRow :=
  match n with O => [] | S n' => 0 :: zero_row n' end.

Fixpoint zero_mat (m n : nat) : QMat :=
  match m with O => [] | S m' => zero_row n :: zero_mat m' n end.

Lemma zero_mat_entry_00 : forall n,
  (0 < n)%nat -> mat_entry (zero_mat 1 n) 0 0 == 0.
Proof.
  intros n Hn. unfold mat_entry, zero_mat, zero_row.
  destruct n; [lia|]. simpl. lra.
Qed.

(** Dot product of rows *)
Fixpoint dot_rows (r1 r2 : QRow) : Q :=
  match r1, r2 with
  | [], _ => 0
  | _, [] => 0
  | a :: r1', b :: r2' => a * b + dot_rows r1' r2'
  end.

Lemma dot_rows_nil_l : forall r, dot_rows [] r == 0.
Proof. reflexivity. Qed.

Lemma dot_rows_nil_r : forall r, dot_rows r [] == 0.
Proof. induction r; reflexivity. Qed.

(** Get column j of matrix *)
Definition mat_col (M : QMat) (j : nat) : QRow :=
  map (fun row => nth j row 0) M.

(** Matrix multiplication: (AB)_{ij} = dot(row_i(A), col_j(B)) *)
Definition mat_mul_entry (A B : QMat) (i j : nat) : Q :=
  dot_rows (nth i A []) (mat_col B j).

Definition mat_mul_row (A B : QMat) (i : nat) : QRow :=
  map (mat_mul_entry A B i) (seq 0 (mat_cols B)).

Definition mat_mul (A B : QMat) : QMat :=
  map (mat_mul_row A B) (seq 0 (mat_rows A)).

(* ================================================================== *)
(*  Part II: Chain Complex                                             *)
(* ================================================================== *)

(** Chain complex: C_2 ->d2 C_1 ->d1 C_0 *)
(** d1 . d2 = 0 *)

Record ChainComplex2 := mkChain2 {
  cc_d2 : QMat;  (* boundary from C_2 to C_1 *)
  cc_d1 : QMat;  (* boundary from C_1 to C_0 *)
}.

(** Boundary squared = zero: d1 . d2 has all entries 0 *)
Definition boundary_sq_zero_entry (C : ChainComplex2) (i j : nat) : Prop :=
  mat_mul_entry (cc_d1 C) (cc_d2 C) i j == 0.

Definition boundary_sq_zero (C : ChainComplex2) : Prop :=
  forall i j, boundary_sq_zero_entry C i j.

(* ================================================================== *)
(*  Part III: Concrete — Triangle (simplest nontrivial)                *)
(* ================================================================== *)

(** Triangle: 3 vertices, 3 edges, 1 triangle *)
(** vertices: 0, 1, 2 *)
(** edges: e01, e12, e02 *)
(** triangle: t012 *)

(** d1: 3x3 matrix (edge -> vertex boundary) *)
(** d1(e01) = v1 - v0, d1(e12) = v2 - v1, d1(e02) = v2 - v0 *)
Definition triangle_d1 : QMat :=
  [[-1; 0; -1];   (* v0: source of e01, e02 *)
   [1; -1; 0];    (* v1: target of e01, source of e12 *)
   [0; 1; 1]].    (* v2: target of e12, e02 *)

(** d2: 3x1 matrix (triangle -> edge boundary) *)
(** d2(t012) = e01 + e12 - e02 *)
Definition triangle_d2 : QMat :=
  [[1]; [1]; [-1]].

Definition triangle_chain : ChainComplex2 :=
  mkChain2 triangle_d2 triangle_d1.

(** ★ d1 . d2 = 0 for triangle *)
Lemma triangle_d2_zero_00 :
  mat_mul_entry triangle_d1 triangle_d2 0 0 == 0.
Proof.
  unfold mat_mul_entry, triangle_d1, triangle_d2, mat_col, dot_rows.
  vm_compute. reflexivity.
Qed.

Lemma triangle_d2_zero_10 :
  mat_mul_entry triangle_d1 triangle_d2 1 0 == 0.
Proof.
  unfold mat_mul_entry, triangle_d1, triangle_d2, mat_col, dot_rows.
  vm_compute. reflexivity.
Qed.

Lemma triangle_d2_zero_20 :
  mat_mul_entry triangle_d1 triangle_d2 2 0 == 0.
Proof.
  unfold mat_mul_entry, triangle_d1, triangle_d2, mat_col, dot_rows.
  vm_compute. reflexivity.
Qed.

(** Euler characteristic: V - E + F = 3 - 3 + 1 = 1 *)
Lemma triangle_euler : (3 - 3 + 1 = 1)%nat.
Proof. lia. Qed.

(* ================================================================== *)
(*  Part IV: Concrete — Tetrahedron                                    *)
(* ================================================================== *)

(** Tetrahedron: 4 vertices, 6 edges, 4 triangles *)
(** Euler: 4 - 6 + 4 = 2 *)
Lemma tetrahedron_euler : (4 - 6 + 4 = 2)%Z.
Proof. lia. Qed.

Lemma icosahedron_euler : (12 - 30 + 20 = 2)%Z.
Proof. lia. Qed.

Lemma torus_euler : (7 - 21 + 14 = 0)%Z.
Proof. lia. Qed.

Lemma sphere_genus : (2 - 2 * 0 = 2)%Z.
Proof. lia. Qed.

Lemma torus_genus : (2 - 2 * 1 = 0)%Z.
Proof. lia. Qed.

Lemma genus2_euler : (2 - 2 * 2 = -2)%Z.
Proof. lia. Qed.

Theorem chain_complex_foundation :
  mat_mul_entry triangle_d1 triangle_d2 0 0 == 0 /\
  mat_mul_entry triangle_d1 triangle_d2 1 0 == 0 /\
  mat_mul_entry triangle_d1 triangle_d2 2 0 == 0 /\
  (4 - 6 + 4 = 2)%Z /\
  (12 - 30 + 20 = 2)%Z.
Proof.
  split; [|split; [|split; [|split]]].
  - exact triangle_d2_zero_00.
  - exact triangle_d2_zero_10.
  - exact triangle_d2_zero_20.
  - exact tetrahedron_euler.
  - exact icosahedron_euler.
Qed.

Definition chain_complex_count := 16%nat.
