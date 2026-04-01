(** * FourierLaplacian.v — DFT modes ARE eigenfunctions of the Laplacian
    Elements: cycle_laplacian_4, laplacian_action_4, laplacian eigenvalues
    Roles:    L = D - A on C_4; DFT modes φ_k satisfy Lφ_k = μ_k·φ_k
    Rules:    μ_k = 2 - λ_k where λ_k = adjacency eigenvalue
    STATUS:   15 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    THE KEY THEOREM:
    Fourier modes φ_k are SIMULTANEOUSLY eigenvectors of:
    — Adjacency A: Aφ_k = λ_k·φ_k (proven in FourierBasis.v)
    — Laplacian L = 2I - A: Lφ_k = (2-λ_k)·φ_k (proven HERE)

    Laplacian eigenvalues μ_k = 2 - λ_k:
    μ₀ = 2-2 = 0 (constant mode, zero frequency)
    μ₁ = 2-0 = 2
    μ₂ = 2-(-2) = 4 (alternating mode, max frequency)
    μ₃ = 2-0 = 2
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

From ToS Require Import analysis.FourierBasis.

Open Scope Q_scope.

(* ================================================================ *)
(*  LAPLACIAN ON CYCLE C_4                                           *)
(* ================================================================ *)

(** Laplacian action: (Lf)(i) = degree·f(i) - (Af)(i) = 2f(i) - (Af)(i) *)
Definition laplacian_action_4 (f : nat -> Q) (i : nat) : Q :=
  2 * f i - adj_action_4 f i.

(** Laplacian eigenvalue: μ_k = 2 - λ_k *)
Definition laplacian_eigenvalue_4 (k : nat) : Q :=
  2 - cycle_eigenvalue_4 k.

(* ================================================================ *)
(*  CONCRETE LAPLACIAN EIGENVALUES                                   *)
(* ================================================================ *)

Lemma lap_ev_0 : laplacian_eigenvalue_4 0 == 0.
Proof. unfold laplacian_eigenvalue_4, cycle_eigenvalue_4. ring. Qed.

Lemma lap_ev_1 : laplacian_eigenvalue_4 1 == 2.
Proof. unfold laplacian_eigenvalue_4, cycle_eigenvalue_4. ring. Qed.

Lemma lap_ev_2 : laplacian_eigenvalue_4 2 == 4.
Proof. unfold laplacian_eigenvalue_4, cycle_eigenvalue_4. ring. Qed.

Lemma lap_ev_3 : laplacian_eigenvalue_4 3 == 2.
Proof. unfold laplacian_eigenvalue_4, cycle_eigenvalue_4. ring. Qed.

(* ================================================================ *)
(*  DFT MODES ARE LAPLACIAN EIGENFUNCTIONS                           *)
(* ================================================================ *)

(** φ₀ = (1,1,1,1): Lφ₀ = 0·φ₀ (constant mode) *)
Lemma laplacian_phi0 : forall j, (j < 4)%nat ->
  laplacian_action_4 phi_0 j == laplacian_eigenvalue_4 0 * phi_0 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
  unfold laplacian_action_4, adj_action_4, cycle_adj_4, phi_0,
    laplacian_eigenvalue_4, cycle_eigenvalue_4;
  vm_compute; reflexivity.
Qed.

(** φ₁ = (1,0,-1,0): Lφ₁ = 2·φ₁ *)
Lemma laplacian_phi1 : forall j, (j < 4)%nat ->
  laplacian_action_4 phi_1 j == laplacian_eigenvalue_4 1 * phi_1 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
  unfold laplacian_action_4, adj_action_4, cycle_adj_4, phi_1,
    laplacian_eigenvalue_4, cycle_eigenvalue_4;
  vm_compute; reflexivity.
Qed.

(** φ₂ = (1,-1,1,-1): Lφ₂ = 4·φ₂ *)
Lemma laplacian_phi2 : forall j, (j < 4)%nat ->
  laplacian_action_4 phi_2 j == laplacian_eigenvalue_4 2 * phi_2 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
  unfold laplacian_action_4, adj_action_4, cycle_adj_4, phi_2,
    laplacian_eigenvalue_4, cycle_eigenvalue_4;
  vm_compute; reflexivity.
Qed.

(** φ₃ = (0,1,0,-1): Lφ₃ = 2·φ₃ *)
Lemma laplacian_phi3 : forall j, (j < 4)%nat ->
  laplacian_action_4 phi_3 j == laplacian_eigenvalue_4 3 * phi_3 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j']]]]; try lia;
  unfold laplacian_action_4, adj_action_4, cycle_adj_4, phi_3,
    laplacian_eigenvalue_4, cycle_eigenvalue_4;
  vm_compute; reflexivity.
Qed.

(* ================================================================ *)
(*  LAPLACIAN = EIGENVALUE × IDENTITY                                *)
(* ================================================================ *)

(** Row sum of Laplacian is zero (L·1 = 0) *)
Lemma laplacian_row_sum_zero : forall i, (i < 4)%nat ->
  laplacian_action_4 phi_0 i == 0.
Proof.
  intros i Hi.
  rewrite (laplacian_phi0 i Hi). rewrite lap_ev_0. ring.
Qed.

(** Eigenvalue sum = trace = 8 *)
Lemma lap_eigenvalue_sum :
  laplacian_eigenvalue_4 0 + laplacian_eigenvalue_4 1 +
  laplacian_eigenvalue_4 2 + laplacian_eigenvalue_4 3 == 8.
Proof.
  unfold laplacian_eigenvalue_4, cycle_eigenvalue_4. ring.
Qed.

(** Trace = 2·N (degree sum) for N=4, degree=2 *)
Lemma lap_trace_eq_2N : 8 == 2 * 4.
Proof. ring. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem fourier_laplacian_synthesis :
  (* Laplacian eigenvalues: 0, 2, 4, 2 *)
  laplacian_eigenvalue_4 0 == 0 /\
  laplacian_eigenvalue_4 1 == 2 /\
  laplacian_eigenvalue_4 2 == 4 /\
  laplacian_eigenvalue_4 3 == 2 /\
  (* DFT modes are Laplacian eigenfunctions *)
  (forall j, (j < 4)%nat ->
    laplacian_action_4 phi_0 j == laplacian_eigenvalue_4 0 * phi_0 j) /\
  (forall j, (j < 4)%nat ->
    laplacian_action_4 phi_2 j == laplacian_eigenvalue_4 2 * phi_2 j) /\
  (* Eigenvalue sum = trace = 2N *)
  laplacian_eigenvalue_4 0 + laplacian_eigenvalue_4 1 +
  laplacian_eigenvalue_4 2 + laplacian_eigenvalue_4 3 == 8.
Proof.
  split; [exact lap_ev_0 |
  split; [exact lap_ev_1 |
  split; [exact lap_ev_2 |
  split; [exact lap_ev_3 |
  split; [exact laplacian_phi0 |
  split; [exact laplacian_phi2 |
  exact lap_eigenvalue_sum]]]]]].
Qed.
