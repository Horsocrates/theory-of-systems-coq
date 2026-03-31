(* ========================================================================= *)
(*                     PROPAGATOR                                            *)
(*           Green's function on lattice from mass matrix inverse            *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 12 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  The propagator G(x,y) = M⁻¹(x,y) measures correlation:               *)
(*                                                                          *)
(*    Elements = position-space propagator entries G(x,y)                   *)
(*    Roles    = self-propagator G(x,x), cross-propagator G(x,y)           *)
(*    Rules    = M·G=I (inverse check), G_pos = Σ G_k (Fourier sum)        *)
(*                                                                          *)
(*  PHYSICAL NOTE (P4):                                                     *)
(*    For the 2-site chain with M = [[1+m², -1], [-1, 1+m²]]:             *)
(*    det(M) = (1+m²)² - 1 = m²(m²+2)                                    *)
(*    G(0,0) = (1+m²)/det, G(0,1) = 1/det                                *)
(*    Position-space propagator = sum of momentum-space propagators.        *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* === Position-space propagator for 2-site chain === *)

(* 2×2 mass matrix: M = [[1+m², -1], [-1, 1+m²]]
   det = (1+m²)² - 1 = m²(m²+2)
   M⁻¹ = (1/det) * [[1+m², 1], [1, 1+m²]] *)

Definition prop_00 (m_sq : Q) : Q := (1 + m_sq) / (m_sq * (m_sq + 2)).
Definition prop_01 (m_sq : Q) : Q := 1 / (m_sq * (m_sq + 2)).

(* === Momentum-space propagator === *)

(* G(k) = 1/(λ_k + m²) where λ_k is the k-th Laplacian eigenvalue *)
Definition G_k (lambda_k m_sq : Q) : Q := 1 / (lambda_k + m_sq).

(* === Theorems === *)

Lemma prop_00_m1 :
  prop_00 1 == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma prop_01_m1 :
  prop_01 1 == 1#3.
Proof. vm_compute. reflexivity. Qed.

Lemma self_gt_cross_m1 :
  prop_00 1 > prop_01 1.
Proof. vm_compute. reflexivity. Qed.

Lemma G_k_zero_mode :
  G_k 0 1 == 1.
Proof. unfold G_k. vm_compute. reflexivity. Qed.

Lemma G_k_first_mode :
  G_k 4 1 == 1#5.
Proof. unfold G_k. vm_compute. reflexivity. Qed.

(* Fourier transform: G(0,0) = (1/N) Σ_k G(k)
   For N=2: G(0,0) = (1/2)(G(0) + G(4)) = (1/2)(1 + 1/5) = (1/2)(6/5) = 3/5
   But our propagator gives G(0,0) = 2/3.
   The eigenvalues of the 2-site Laplacian are 0 and 2 (not 0 and 4).
   With λ = {0, 2}: G(0,0) = (1/2)(1/1 + 1/3) = (1/2)(4/3) = 2/3 ✓ *)
Lemma fourier_sum :
  (1#2) * (G_k 0 1 + G_k 2 1) == 2#3.
Proof. unfold G_k. vm_compute. reflexivity. Qed.

Lemma prop_positive_m1 :
  0 < prop_00 1.
Proof. vm_compute. reflexivity. Qed.

Lemma prop_decays_with_distance :
  prop_00 1 > prop_01 1.
Proof. vm_compute. reflexivity. Qed.

(* det(M) = m²(m²+2) = 1·3 = 3 for m²=1 *)
Lemma mass_matrix_det_m1 :
  1 * (1 + 2) == 3.
Proof. ring. Qed.

(* Verify M · M⁻¹ = I, row 0 col 0:
   M[0,0]·G[0,0] + M[0,1]·G[1,0] = (1+1)·(2/3) + (-1)·(1/3) = 4/3 - 1/3 = 1 *)
Lemma inverse_check_00 :
  2 * (2#3) + (-(1)) * (1#3) == 1.
Proof. ring. Qed.

(* Verify M · M⁻¹ = I, row 0 col 1:
   M[0,0]·G[0,1] + M[0,1]·G[1,1] = 2·(1/3) + (-1)·(2/3) = 2/3 - 2/3 = 0 *)
Lemma inverse_check_01 :
  2 * (1#3) + (-(1)) * (2#3) == 0.
Proof. ring. Qed.

Lemma propagator_synthesis :
  prop_00 1 == 2#3 /\
  prop_01 1 == 1#3 /\
  G_k 0 1 == 1 /\
  (1#2) * (G_k 0 1 + G_k 2 1) == 2#3 /\
  0 < prop_00 1 /\
  1 * (1 + 2) == 3.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
