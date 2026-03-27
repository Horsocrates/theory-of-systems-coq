(* EnergyFromContent.v *)
(* E/R/R: Elements = Q matrices, Roles = energy from content, Rules = trace/det/eigenvalue *)
(* Standalone — only Stdlib imports *)
(* STATUS: 25 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.

Open Scope Q_scope.

(** * 2x2 Q matrix *)

Record Mat2 := mkMat2 {
  m00 : Q; m01 : Q;
  m10 : Q; m11 : Q
}.

(** * Trace and Determinant *)

Definition trace_M (M : Mat2) : Q := m00 M + m11 M.
Definition det_M (M : Mat2) : Q := m00 M * m11 M - m01 M * m10 M.

(** * Concrete transfer matrix T for hydrogen-like system *)

Definition T_hydrogen : Mat2 := mkMat2 (-(1#2)) 0 0 (1#4).

Lemma T_hydrogen_trace : trace_M T_hydrogen == -(1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma T_hydrogen_det : det_M T_hydrogen == -(1#8).
Proof. vm_compute. reflexivity. Qed.

(** * Energy = eigenvalue for diagonal matrix *)

Definition E_hydrogen : Q := -(1#2).

Lemma E_hydrogen_is_diagonal : m00 T_hydrogen == E_hydrogen.
Proof. vm_compute. reflexivity. Qed.

Lemma E_hydrogen_negative : E_hydrogen < 0.
Proof. unfold E_hydrogen, Qlt. simpl. lia. Qed.

(** * Helium-like system *)

Definition T_helium : Mat2 := mkMat2 (-(729#256)) 0 0 (-(81#64)).

Definition E_helium : Q := -(729#256).

Lemma T_helium_trace : trace_M T_helium == -(1053#256).
Proof. vm_compute. reflexivity. Qed.

Lemma T_helium_det : det_M T_helium == 59049 # 16384.
Proof. vm_compute. reflexivity. Qed.

Lemma E_helium_is_diagonal : m00 T_helium == E_helium.
Proof. vm_compute. reflexivity. Qed.

Lemma E_helium_negative : E_helium < 0.
Proof. unfold E_helium, Qlt. simpl. lia. Qed.

(** * Energies are distinct *)

Lemma energies_distinct : ~ (E_hydrogen == E_helium).
Proof.
  unfold E_hydrogen, E_helium. intro H. vm_compute in H. discriminate.
Qed.

(** * Energy ordering *)

Lemma helium_lower : E_helium < E_hydrogen.
Proof. unfold E_helium, E_hydrogen, Qlt. simpl. lia. Qed.

(** * Trace determines sum of eigenvalues *)

Lemma trace_is_eigenvalue_sum : forall (a b : Q),
  trace_M (mkMat2 a 0 0 b) == a + b.
Proof. intros. unfold trace_M. simpl. unfold Qeq. simpl. lia. Qed.

Lemma det_is_eigenvalue_product : forall (a b : Q),
  det_M (mkMat2 a 0 0 b) == a * b.
Proof. intros. unfold det_M. simpl. unfold Qeq. simpl. lia. Qed.

(** * Content determines energy: same matrix -> same trace *)

Lemma content_determines_trace : forall M1 M2 : Mat2,
  m00 M1 == m00 M2 -> m11 M1 == m11 M2 ->
  trace_M M1 == trace_M M2.
Proof.
  intros M1 M2 H00 H11. unfold trace_M.
  apply Qplus_comp; assumption.
Qed.

(** * Zero matrix has zero energy *)

Definition T_zero : Mat2 := mkMat2 0 0 0 0.

Lemma zero_trace : trace_M T_zero == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_det : det_M T_zero == 0.
Proof. vm_compute. reflexivity. Qed.

(** * Identity matrix *)

Definition T_identity : Mat2 := mkMat2 1 0 0 1.

Lemma identity_trace : trace_M T_identity == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma identity_det : det_M T_identity == 1.
Proof. vm_compute. reflexivity. Qed.

(** * Trace vanishes for traceless matrix *)

Definition T_traceless : Mat2 := mkMat2 1 0 0 (-(1)).

Lemma traceless_trace : trace_M T_traceless == 0.
Proof. vm_compute. reflexivity. Qed.

(** * Trace additivity for diagonal matrices *)

Lemma trace_additive_diag : forall a1 b1 a2 b2 : Q,
  trace_M (mkMat2 a1 0 0 b1) + trace_M (mkMat2 a2 0 0 b2) ==
  trace_M (mkMat2 (a1 + a2) 0 0 (b1 + b2)).
Proof. intros. unfold trace_M. simpl. unfold Qeq. simpl. lia. Qed.

(** * Different diagonal -> different trace *)

Lemma distinct_diagonal_distinct_trace : forall a1 b1 a2 b2 : Q,
  ~ (a1 + b1 == a2 + b2) ->
  ~ (trace_M (mkMat2 a1 0 0 b1) == trace_M (mkMat2 a2 0 0 b2)).
Proof. intros. unfold trace_M. simpl. exact H. Qed.
