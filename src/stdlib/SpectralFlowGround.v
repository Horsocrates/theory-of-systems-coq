(** * SpectralFlowGround.v — Ground State Approximations and π² Flow
    Elements: Newton √2 and √5 approximations, ground state λ₁(K)
    Roles:    Connect eigenvalue approximations to π² via spectral flow
    Rules:    K=2: λ₁=1, K=4: λ₁≈55/144, λ₁·(K+1)² → π²
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.MatN.
From ToS Require Import stdlib.SpectralFlowTraces.
From ToS Require Import stdlib.SpectralFlowNewton.
Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON APPROXIMATION OF √2                                        *)
(*  x_{n+1} = (x_n + 2/x_n) / 2                                      *)
(*  step 0: x=1, step 1: (1+2)/2 = 3/2, step 2: (3/2+4/3)/2 = 17/12 *)
(* ================================================================== *)

Definition newton_sqrt2_0 : Q := 1.
Definition newton_sqrt2_1 : Q := 3#2.
Definition newton_sqrt2_2 : Q := 17#12.

(** Step 0: 1² = 1 < 2 *)
Lemma newton_sqrt2_step0_sq : newton_sqrt2_0 * newton_sqrt2_0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Step 1: (3/2)² = 9/4 = 2.25 > 2 *)
Lemma newton_sqrt2_step1_sq : newton_sqrt2_1 * newton_sqrt2_1 == 9#4.
Proof. vm_compute. reflexivity. Qed.

(** Step 2: (17/12)² = 289/144 ≈ 2.0069 — very close to 2 *)
Lemma newton_sqrt2_step2_sq : newton_sqrt2_2 * newton_sqrt2_2 == 289#144.
Proof. vm_compute. reflexivity. Qed.

(** Bracket: 2 < 289/144 < 9/4 *)
Lemma newton_sqrt2_bracket : 2 < 289#144 /\ 289#144 < 9#4.
Proof. split; lra. Qed.

(* ================================================================== *)
(*  GROUND STATE: K=2 exact                                            *)
(*  H2 eigenvalues ±1, ground state λ₁ = 1                            *)
(* ================================================================== *)

Definition ground_K2 : Q := 1.

(** λ₁(2) · (2+1)² = 1 · 9 = 9 *)
Lemma ground_K2_pi_approx : ground_K2 * (3 * 3) == 9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GROUND STATE: K=3 approximation                                    *)
(*  Eigenvalues 0, ±√2. Smallest Laplacian eigenvalue = 2 - √2        *)
(*  Using Newton step 2: √2 ≈ 17/12                                   *)
(*  λ₁(3) ≈ 2 - 17/12 = 7/12                                         *)
(* ================================================================== *)

Definition ground_K3 : Q := 7#12.

(** λ₁(3) · (3+1)² = 7/12 · 16 = 112/12 = 28/3 *)
Lemma ground_K3_pi_approx : ground_K3 * (4 * 4) == 28#3.
Proof. vm_compute. reflexivity. Qed.

(** 28/3 ≈ 9.33, closer to π² ≈ 9.87 than K=2's value of 9 *)
Lemma ground_K3_closer : 9 < 28#3.
Proof. lra. Qed.

(* ================================================================== *)
(*  GROUND STATE: K=4 via discriminant 5                               *)
(*  Char poly λ⁴ - 3λ² + 1, μ = λ²: μ = (3-√5)/2                     *)
(*  Newton √5: step 0=2, step 1=9/4, step 2=161/72                    *)
(*  λ₁² ≈ (3 - 161/72)/2 = (216/72 - 161/72)/2 = 55/144              *)
(* ================================================================== *)

Definition newton_sqrt5_2 : Q := 161#72.

(** (161/72)² = 25921/5184, and 5*5184 = 25920, so error = 1/5184 *)
Lemma newton_sqrt5_step2_sq : newton_sqrt5_2 * newton_sqrt5_2 == 25921#5184.
Proof. vm_compute. reflexivity. Qed.

(** Bracket: 25920/5184 = 5 < 25921/5184 *)
Lemma newton_sqrt5_close : 5 < 25921#5184.
Proof. lra. Qed.

Definition ground_K4 : Q := 55#144.

(** λ₁(4) · (4+1)² = 55/144 · 25 = 1375/144 *)
Lemma ground_K4_pi_approx : ground_K4 * (5 * 5) == 1375#144.
Proof. vm_compute. reflexivity. Qed.

(** 1375/144 ≈ 9.549. Bracket: 9 < 1375/144 < 10 *)
Lemma ground_K4_bracket : 9 < 1375#144 /\ 1375#144 < 10.
Proof. split; lra. Qed.

(** Flow: 9 < 28/3 < 1375/144 — monotone convergence toward π² *)
Lemma pi_flow_monotone : 9 < 28#3 /\ 28#3 < 1375#144.
Proof. split; lra. Qed.

(** Newton √2 overshoot: (17/12)² > 2 *)
Lemma newton_sqrt2_overshoot : 2 < newton_sqrt2_2 * newton_sqrt2_2.
Proof. unfold newton_sqrt2_2. lra. Qed.

(** Ground state flow is strictly increasing *)
Lemma ground_flow_increasing : ground_K2 * 9 < ground_K4 * 25.
Proof. unfold ground_K2, ground_K4. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem spectral_flow_ground_synthesis :
  ground_K2 * (3 * 3) == 9 /\
  9 < 28#3 /\
  9 < 1375#144 /\ 1375#144 < 10.
Proof.
  split; [exact ground_K2_pi_approx|].
  split; [exact ground_K3_closer|].
  exact ground_K4_bracket.
Qed.
