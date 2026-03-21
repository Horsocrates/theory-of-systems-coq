(** * DistinctionAsBoundary.v — Distinction as Boundary (Holographic Principle Foundation)
    Elements: boundary_dim, info_per_distinction, boundary_area, entropy_from_area
    Roles:    Boundary reduces dimension by 1; information lives on boundaries
    Rules:    boundary_dim(n) = n-1; entropy = area in natural units
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith QArith_base Lia.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Boundary Dimension                                         *)
(* ================================================================== *)

(** A distinction in n-dimensional space creates an (n-1)-dimensional boundary. *)
Definition boundary_dim (space_dim : nat) : nat := Nat.sub space_dim (S O).

Lemma boundary_of_1d : boundary_dim (S O) = O.
Proof. reflexivity. Qed.

Lemma boundary_of_2d : boundary_dim (S (S O)) = S O.
Proof. reflexivity. Qed.

Lemma boundary_of_3d : boundary_dim (S (S (S O))) = S (S O).
Proof. reflexivity. Qed.

Lemma boundary_of_4d : boundary_dim (S (S (S (S O)))) = S (S (S O)).
Proof. reflexivity. Qed.

Lemma boundary_codimension_one : forall n : nat,
  (S O <= n)%nat -> (boundary_dim n + S O = n)%nat.
Proof.
  intros n Hn. unfold boundary_dim. lia.
Qed.

(* ================================================================== *)
(*  Part II: Information per Distinction                               *)
(* ================================================================== *)

(** Each distinction carries exactly 1 bit of information (binary: inside/outside). *)
Definition info_per_distinction : Q := 1.

Lemma info_positive : 0 < info_per_distinction.
Proof. unfold info_per_distinction. reflexivity. Qed.

(** Boundary area in natural units: area = number of boundary cells. *)
Definition boundary_area (n : nat) : Q := inject_Z (Z.of_nat n).

Lemma boundary_area_0 : boundary_area O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_area_1 : boundary_area (S O) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_area_4 : boundary_area 4%nat == 4.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Entropy from Area                                        *)
(* ================================================================== *)

(** In natural units, entropy equals the boundary area. *)
Definition entropy_from_area (a : Q) : Q := a.

Lemma entropy_identity : forall a : Q, entropy_from_area a == a.
Proof. intros a. unfold entropy_from_area. reflexivity. Qed.

Lemma entropy_nonneg : forall a : Q, 0 <= a -> 0 <= entropy_from_area a.
Proof. intros a Ha. unfold entropy_from_area. exact Ha. Qed.

(* ================================================================== *)
(*  Part IV: Synthesis                                                  *)
(* ================================================================== *)

(** The holographic chain: space_dim -> boundary_dim -> boundary_area -> entropy.
    For n boundary cells in (d-1) dimensions, the entropy is n. *)
Theorem distinction_boundary_entropy : forall (d n : nat),
  (S O <= d)%nat ->
  (boundary_dim d + S O = d)%nat /\
  info_per_distinction == 1 /\
  entropy_from_area (boundary_area n) == boundary_area n.
Proof.
  intros d n Hd.
  split.
  - apply boundary_codimension_one. exact Hd.
  - split.
    + unfold info_per_distinction. reflexivity.
    + apply entropy_identity.
Qed.

Lemma entropy_scales_with_area : forall (n m : nat),
  (n <= m)%nat ->
  entropy_from_area (boundary_area n) <= entropy_from_area (boundary_area m).
Proof.
  intros n m Hnm.
  unfold entropy_from_area, boundary_area.
  unfold Qle. simpl. lia.
Qed.
