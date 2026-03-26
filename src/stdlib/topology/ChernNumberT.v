(** * ChernNumberT.v — Chern number and chiral edge states

    Elements: mass parameter M, Chern number C, chiral edge count
    Roles:    Chern number classifies 2D topological phases (QHE)
    Rules:    0 < M < 2 -> C=1; -2 < M < 0 -> C=-1; |M|>2 -> C=0
    Status:   verified | 2D topological insulator

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool ZArith.
Open Scope Q_scope.

(** Q strict less-than as bool *)
Definition Qlt_bool (a b : Q) : bool :=
  andb (Qle_bool a b) (negb (Qeq_bool a b)).

(** Chern number from mass parameter M *)
Definition chern_number (M : Q) : Z :=
  if andb (Qlt_bool 0 M) (Qlt_bool M 2) then 1%Z
  else if andb (Qlt_bool (-(2)) M) (Qlt_bool M 0) then (-1)%Z
  else 0%Z.

(** ---- Concrete Chern numbers ---- *)

Theorem chern_topo_pos : chern_number 1 = 1%Z.
Proof. simpl. reflexivity. Qed.

Theorem chern_topo_neg : chern_number (-(1)) = (-1)%Z.
Proof. simpl. reflexivity. Qed.

Theorem chern_trivial_pos : chern_number 3 = 0%Z.
Proof. simpl. reflexivity. Qed.

Theorem chern_trivial_neg : chern_number (-(3)) = 0%Z.
Proof. simpl. reflexivity. Qed.

Theorem chern_critical_0 : chern_number 0 = 0%Z.
Proof. simpl. reflexivity. Qed.

Theorem chern_critical_2 : chern_number 2 = 0%Z.
Proof. simpl. reflexivity. Qed.

(** Half-filling: M = 1/2 still topological *)
Theorem chern_half : chern_number (1#2) = 1%Z.
Proof. simpl. reflexivity. Qed.

(** M = -1/2: negative Chern *)
Theorem chern_neg_half : chern_number (-(1#2)) = (-1)%Z.
Proof. simpl. reflexivity. Qed.

(** ---- Chiral edge states ---- *)

(** Number of chiral edge modes = |C| *)
Definition n_chiral_edge (C : Z) : nat := Z.abs_nat C.

Theorem chiral_1 : n_chiral_edge 1 = 1%nat.
Proof. simpl. reflexivity. Qed.

Theorem chiral_neg1 : n_chiral_edge (-1) = 1%nat.
Proof. simpl. reflexivity. Qed.

Theorem chiral_0 : n_chiral_edge 0 = 0%nat.
Proof. simpl. reflexivity. Qed.

(** Topological has chiral edges *)
Theorem topo_has_chiral : n_chiral_edge (chern_number 1) = 1%nat.
Proof. simpl. reflexivity. Qed.

(** Trivial has no chiral edges *)
Theorem trivial_no_chiral : n_chiral_edge (chern_number 3) = 0%nat.
Proof. simpl. reflexivity. Qed.

(** Positive and negative Chern give same edge count *)
Theorem chiral_symmetry :
  n_chiral_edge (chern_number 1) = n_chiral_edge (chern_number (-(1))).
Proof. simpl. reflexivity. Qed.

(** M = 3/2: still topological (between 0 and 2) *)
Theorem chern_three_halves : chern_number (3#2) = 1%Z.
Proof. simpl. reflexivity. Qed.
