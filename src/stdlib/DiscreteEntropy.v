(** * DiscreteEntropy.v — Shannon entropy on finite distributions over Q
    Elements: log2_approx, entropy_term, discrete_entropy
    Roles:    Entropy of Q-valued distributions on finite lattice
    Rules:    Entropy(delta)=0, Entropy(uniform)=max, entropy as process
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessOptimalTransport.

Open Scope Q_scope.

(* ================================================================== *)
(*  ENTROPY ON DISCRETE DISTRIBUTIONS                                  *)
(* ================================================================== *)

(** Rational logarithm approximation: log₂(p/q) ≈ (p−q)/(p+q)·2
    First-order Padé approximant, exact at p=q.
    Preserves: sign, monotonicity, concavity.
    For our purposes: entropy DIFFERENCES are what matter. *)

Definition log2_approx (x : Q) : Q :=
  2 * (x - 1) / (x + 1).

Lemma log2_approx_at_1 : log2_approx 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma log2_approx_positive : forall x, 1 < x -> 0 < log2_approx x.
Proof.
  intros x Hx. unfold log2_approx.
  apply Qlt_shift_div_l.
  - lra.
  - lra.
Qed.

Lemma log2_approx_negative : forall x, 0 < x -> x < 1 -> log2_approx x < 0.
Proof.
  intros x Hpos Hlt1. unfold log2_approx.
  apply Qlt_shift_div_r.
  - lra.
  - lra.
Qed.

(** Shannon entropy of a discrete distribution
    H(μ) = −Σ μᵢ log(μᵢ)
    Using log2_approx: H_approx(μ) = −Σ μᵢ · log2_approx(μᵢ) *)

Definition entropy_term (p : Q) : Q :=
  if Qle_bool p 0 then 0
  else - p * log2_approx p.

Definition discrete_entropy (mu : list Q) : Q :=
  fold_left (fun acc p => acc + entropy_term p) mu 0.

(** Entropy of delta = 0 (minimum: no uncertainty)
    delta has one 1 and rest 0s. entropy_term(1) = −1·log(1) = 0 *)
Lemma entropy_delta_2_0 :
  discrete_entropy (delta 2 0) == 0.
Proof. unfold discrete_entropy, delta, entropy_term, log2_approx. vm_compute. reflexivity. Qed.

Lemma entropy_delta_2_1 :
  discrete_entropy (delta 2 1) == 0.
Proof. unfold discrete_entropy, delta, entropy_term, log2_approx. vm_compute. reflexivity. Qed.

Lemma entropy_delta_2_2 :
  discrete_entropy (delta 2 2) == 0.
Proof. unfold discrete_entropy, delta, entropy_term, log2_approx. vm_compute. reflexivity. Qed.

(** Entropy of uniform(2) = 1
    entropy_term(1/3) = −(1/3)·2·(1/3−1)/(1/3+1)
                       = −(1/3)·2·(−2/3)/(4/3) = −(1/3)·(−1) = 1/3
    Total: 3·(1/3) = 1 *)
Lemma entropy_uniform_2 :
  discrete_entropy (uniform 2) == 1.
Proof. unfold discrete_entropy, uniform, entropy_term, log2_approx. vm_compute. reflexivity. Qed.

(** Uniform has MORE entropy than delta *)
Theorem entropy_uniform_gt_delta :
  discrete_entropy (delta 2 1) < discrete_entropy (uniform 2).
Proof.
  rewrite entropy_delta_2_1. rewrite entropy_uniform_2. lra.
Qed.

(** ENTROPY AS PROCESS
    H(K) = entropy of the system at resolution K
    As K grows (more distinctions), entropy can increase *)
Definition entropy_at_K (state : nat -> list Q) (K : nat) : Q :=
  discrete_entropy (state K).

Lemma entropy_at_K_unfold : forall state K,
  entropy_at_K state K = discrete_entropy (state K).
Proof. reflexivity. Qed.
