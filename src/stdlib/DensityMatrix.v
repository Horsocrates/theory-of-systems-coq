(* DensityMatrix.v — Density matrix and partial trace over Q *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(** Pure state |ψ⟩ ∈ Q^n. Density matrix ρ = |ψ⟩⟨ψ| *)
Definition density_matrix (psi : nat -> Q) (i j : nat) : Q :=
  psi i * psi j.

(** Diagonal: ρ_{ii} = |ψ_i|² *)
Lemma density_diagonal : forall psi i,
  density_matrix psi i i == psi i * psi i.
Proof. intros. reflexivity. Qed.

(** Symmetry: ρ_{ij} = ρ_{ji} *)
Lemma density_symmetric : forall psi i j,
  density_matrix psi i j == density_matrix psi j i.
Proof. intros. unfold density_matrix. ring. Qed.

(** Rank 1: ρ_{ij}·ρ_{kl} = ρ_{il}·ρ_{kj} *)
Lemma density_rank1 : forall psi i j k l,
  density_matrix psi i j * density_matrix psi k l ==
  density_matrix psi i l * density_matrix psi k j.
Proof. intros. unfold density_matrix. ring. Qed.

(** ★ PARTIAL TRACE for bipartite system *)
(** System A ⊗ B, dim_A × dim_B total *)
(** ρ_A(iA,jA) = Σ_kB ψ(iA·nB+kB) · ψ(jA·nB+kB) *)

Fixpoint partial_trace_B_aux (psi : nat -> Q) (nB iA jA kB : nat) : Q :=
  match kB with
  | O => psi (iA * nB)%nat * psi (jA * nB)%nat
  | S k => partial_trace_B_aux psi nB iA jA k +
           psi (iA * nB + S k)%nat * psi (jA * nB + S k)%nat
  end.

Definition partial_trace_B (psi : nat -> Q) (nB iA jA : nat) : Q :=
  partial_trace_B_aux psi nB iA jA (nB - 1).

(** For product state ψ(i,j) = α_i · β_j: *)
(** ρ_A(i,j) = α_i · α_j · Σ_k β_k² = α_i · α_j (if β normalized) *)
(** = pure state → zero entropy *)

(** Concrete: 2×2 system = 2 qubits *)
(** |00⟩ = ψ(0)=1, ψ(1)=ψ(2)=ψ(3)=0 *)
Definition psi_00 (n : nat) : Q :=
  match n with O => 1%Q | _ => 0%Q end.

Lemma rho_00_diagonal : partial_trace_B psi_00 2 0 0 == 1.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_00. simpl. ring. Qed.

Lemma rho_00_offdiag : partial_trace_B psi_00 2 0 1 == 0.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_00. simpl. ring. Qed.

Lemma rho_00_11 : partial_trace_B psi_00 2 1 1 == 0.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_00. simpl. ring. Qed.

(** |00⟩: ρ_A = [[1,0],[0,0]] — pure, eigenvalues (1,0), entropy = 0 *)

(** Bell state: ψ(0)=1/√2, ψ(3)=1/√2 → approximate over Q *)
(** Use ψ(0)=1, ψ(3)=1 (unnormalized, norm²=2) *)
Definition psi_bell (n : nat) : Q :=
  match n with O => 1%Q | 3%nat => 1%Q | _ => 0%Q end.

Lemma rho_bell_00 : partial_trace_B psi_bell 2 0 0 == 1.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_bell. simpl. ring. Qed.

Lemma rho_bell_11 : partial_trace_B psi_bell 2 1 1 == 1.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_bell. simpl. ring. Qed.

Lemma rho_bell_offdiag : partial_trace_B psi_bell 2 0 1 == 0.
Proof. unfold partial_trace_B, partial_trace_B_aux, psi_bell. simpl. ring. Qed.

(** Bell: ρ_A = [[1,0],[0,1]] (unnormalized) = I/2 after normalization *)
(** = maximally mixed → maximum entropy = ln(2) *)

(** ★ KEY DISTINCTION: *)
(** Product |00⟩: ρ_A = [[1,0],[0,0]] → pure → S=0 *)
(** Bell (|00⟩+|11⟩)/√2: ρ_A = I/2 → mixed → S=ln(2) *)
(** Entanglement = mixedness of reduced state *)

Theorem density_matrix_foundation :
  partial_trace_B psi_00 2 0 0 == 1 /\
  partial_trace_B psi_00 2 1 1 == 0 /\
  partial_trace_B psi_bell 2 0 0 == 1 /\
  partial_trace_B psi_bell 2 1 1 == 1.
Proof.
  split; [|split; [|split]].
  - exact rho_00_diagonal.
  - exact rho_00_11.
  - exact rho_bell_00.
  - exact rho_bell_11.
Qed.

Definition density_matrix_count := 13%nat.
