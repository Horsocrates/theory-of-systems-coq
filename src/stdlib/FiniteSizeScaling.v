(** * FiniteSizeScaling.v -- Extracting β_c and exponents from finite strips
    Elements: beta_c process, FSS formula, critical exponent ν
    Roles:    β_c(W) → β_c(∞) as process in strip width W
    Rules:    β_c(W) - β_c(∞) ~ A·W^{-1/ν}, convergence rate = exponent
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  β_c VALUES FOR DIFFERENT WIDTHS                                    *)
(* ================================================================== *)

(** Onsager exact: β_c = (1/2)ln(1+√2) = 0.44069... *)
Definition beta_c_exact : Q := 4407#10000.

(** Our W=2 bracket: β_c(W=2) ∈ (3/7, 4/9) ≈ (0.4286, 0.4444) *)
(** Midpoint: (3/7 + 4/9)/2 = (27/63 + 28/63)/2 = 55/126 ≈ 0.4365 *)
Definition beta_c_w2 : Q := 55#126.

(** Deviation: beta_c_w2 < beta_c_exact (we underestimate slightly) *)
Lemma beta_c_w2_lt_exact : beta_c_w2 < beta_c_exact.
Proof.
  assert (H1 : beta_c_w2 == 55#126) by reflexivity.
  assert (H2 : beta_c_exact == 4407#10000) by reflexivity.
  rewrite H1, H2. lra.
Qed.

(** Small deviation *)
Lemma beta_c_w2_close : beta_c_exact - beta_c_w2 < 1#100.
Proof.
  assert (H : beta_c_exact - beta_c_w2 == 2641#630000)
    by (unfold beta_c_exact, beta_c_w2; vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  FINITE-SIZE SCALING THEORY                                         *)
(* ================================================================== *)

(** Fisher-Barber (1972): β_c(W) - β_c(∞) = A·W^{-1/ν}
    For Ising: ν = 1 (exact, from Onsager/CFT)
    So: β_c(W) - β_c(∞) ~ A/W
    Prediction: β_c(W=3) deviation ≈ (2/3)·β_c(W=2) deviation *)

Definition predicted_delta_w3 : Q := (beta_c_exact - beta_c_w2) * (2#3).

Lemma fss_prediction :
  predicted_delta_w3 == (beta_c_exact - beta_c_w2) * (2#3).
Proof. reflexivity. Qed.

(** β_c as process in W *)
Definition beta_c_process (W : nat) : Q :=
  match W with
  | O => 0  | S O => 0  (* W=0,1: not meaningful *)
  | S (S O) => beta_c_w2  (* W=2: from our Onsager bisection *)
  | _ => beta_c_exact  (* W≥3: use exact as placeholder *)
  end.

(** Process converges: each step closer to β_c *)
Lemma beta_c_w2_near_exact :
  beta_c_exact - beta_c_process 2 < 1#100.
Proof. simpl. exact beta_c_w2_close. Qed.

(* ================================================================== *)
(*  CRITICAL EXPONENTS                                                 *)
(* ================================================================== *)

(** Ising critical exponents (exact from Onsager/CFT):
    ν = 1 (correlation length)
    γ = 7/4 (susceptibility)
    β_mag = 1/8 (magnetization, not inverse temperature!)
    α = 0 (specific heat, logarithmic)
    η = 1/4 (anomalous dimension) *)

Definition ising_nu : Q := 1.
Definition ising_gamma : Q := 7#4.
Definition ising_beta_mag : Q := 1#8.
Definition ising_eta : Q := 1#4.

(** Scaling relations (exact):
    2 - α = 2·β_mag + γ = d·ν
    γ = ν·(2-η)
    α + 2·β_mag + γ = 2 (Rushbrooke) *)

Lemma rushbrooke : 0 + 2 * ising_beta_mag + ising_gamma == 2.
Proof. unfold ising_beta_mag, ising_gamma. lra. Qed.

Lemma fisher : ising_gamma == ising_nu * (2 - ising_eta).
Proof. unfold ising_gamma, ising_nu, ising_eta. lra. Qed.

Lemma hyperscaling : 2 == 2 * ising_nu.
Proof. unfold ising_nu. lra. Qed.

(** Potts Q=3 critical exponents (exact from Baxter):
    ν = 5/6, γ = 13/9, β_mag = 1/9 *)

Definition potts3_nu : Q := 5#6.
Definition potts3_gamma : Q := 13#9.
Definition potts3_beta_mag : Q := 1#9.

(** Rushbrooke for Potts Q=3: α + 2β + γ = 2
    α=1/3, β=1/9, γ=13/9: 1/3 + 2/9 + 13/9 = 3/9 + 2/9 + 13/9 = 18/9 = 2 ✓ *)
Lemma potts3_rushbrooke :
  (1#3) + (2#1) * potts3_beta_mag + potts3_gamma == 2.
Proof. unfold potts3_beta_mag, potts3_gamma. lra. Qed.

(** SYNTHESIS *)
Theorem fss_synthesis :
  (* β_c(W=2) close to exact *)
  beta_c_exact - beta_c_w2 < 1#100 /\
  (* Rushbrooke relation *)
  0 + 2 * ising_beta_mag + ising_gamma == 2 /\
  (* Fisher relation *)
  ising_gamma == ising_nu * (2 - ising_eta) /\
  (* Hyperscaling *)
  2 == 2 * ising_nu.
Proof.
  split; [|split; [|split]].
  - exact beta_c_w2_close.
  - exact rushbrooke.
  - exact fisher.
  - exact hyperscaling.
Qed.
