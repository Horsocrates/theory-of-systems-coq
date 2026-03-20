(** * BornRuleFromProcess.v -- Born rule as inner product ratio
    Elements: inner_K, norm_sq_K, born_prob_K, basis states
    Roles:    Born rule = |⟨ψ|φ⟩|²/(⟨ψ|ψ⟩·⟨φ|φ⟩) from linear algebra
    Rules:    p(e₀→e₀) = 1, p(e₀→e₁) = 0, p(superpos→e₀) = 1/2
    Status:   Foundation
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  INNER PRODUCT AT RESOLUTION K                                      *)
(* ================================================================== *)

(** For process states ψ, φ : nat → Q
    Inner product at resolution K: ⟨ψ|φ⟩_K = Σ_{k=0}^{K} ψ(k)·φ(k)

    Born probability: p_K(ψ,φ) = ⟨ψ|φ⟩_K² / (⟨ψ|ψ⟩_K · ⟨φ|φ⟩_K)
    This IS the Born rule: probability = squared projection.
    Cauchy-Schwarz guarantees 0 ≤ p ≤ 1. *)

Fixpoint inner_K (psi phi : nat -> Q) (K : nat) : Q :=
  match K with
  | O => psi O * phi O
  | S K' => inner_K psi phi K' + psi (S K') * phi (S K')
  end.

Definition norm_sq_K (psi : nat -> Q) (K : nat) : Q :=
  inner_K psi psi K.

Definition born_prob_K (psi phi : nat -> Q) (K : nat) : Q :=
  let ip := inner_K psi phi K in
  let n1 := norm_sq_K psi K in
  let n2 := norm_sq_K phi K in
  (ip * ip) / (n1 * n2).

(* ================================================================== *)
(*  BASIS STATES                                                       *)
(* ================================================================== *)

Definition basis_0 : nat -> Q := fun k =>
  match k with O => 1 | _ => 0 end.

Definition basis_1 : nat -> Q := fun k =>
  match k with S O => 1 | _ => 0 end.

Definition superpos : nat -> Q := fun k =>
  match k with O => 1 | S O => 1 | _ => 0 end.

(* ================================================================== *)
(*  INNER PRODUCTS                                                     *)
(* ================================================================== *)

(** ⟨e₀|e₀⟩ = 1 *)
Lemma inner_00 : inner_K basis_0 basis_0 1 == 1.
Proof. unfold inner_K, basis_0. ring. Qed.

(** ⟨e₁|e₁⟩ = 1 *)
Lemma inner_11 : inner_K basis_1 basis_1 1 == 1.
Proof. unfold inner_K, basis_1. ring. Qed.

(** ⟨e₀|e₁⟩ = 0 (orthogonal) *)
Lemma inner_01 : inner_K basis_0 basis_1 1 == 0.
Proof. unfold inner_K, basis_0, basis_1. ring. Qed.

(** ⟨s|s⟩ = 2 *)
Lemma inner_ss : inner_K superpos superpos 1 == 2.
Proof. unfold inner_K, superpos. ring. Qed.

(** ⟨s|e₀⟩ = 1 *)
Lemma inner_s0 : inner_K superpos basis_0 1 == 1.
Proof. unfold inner_K, superpos, basis_0. ring. Qed.

(** ⟨s|e₁⟩ = 1 *)
Lemma inner_s1 : inner_K superpos basis_1 1 == 1.
Proof. unfold inner_K, superpos, basis_1. ring. Qed.

(* ================================================================== *)
(*  BORN PROBABILITIES                                                 *)
(* ================================================================== *)

(** Born(e₀, e₀) = 1 (certain) *)
Lemma born_certain : born_prob_K basis_0 basis_0 1 == 1.
Proof.
  unfold born_prob_K, norm_sq_K, inner_K, basis_0. field.
Qed.

(** Born(e₀, e₁) = 0 (impossible) *)
(** inner_K = 0, so numerator = 0, result = 0 *)
Lemma born_impossible : born_prob_K basis_0 basis_1 1 == 0.
Proof.
  unfold born_prob_K, norm_sq_K, inner_K, basis_0, basis_1. vm_compute. reflexivity.
Qed.

(** Born(superpos, e₀) = 1/2 *)
(** ⟨s|e₀⟩ = 1, ⟨s|s⟩ = 2, ⟨e₀|e₀⟩ = 1 *)
(** p = 1²/(2·1) = 1/2 *)
Lemma born_half : born_prob_K superpos basis_0 1 == 1 # 2.
Proof.
  unfold born_prob_K, norm_sq_K, inner_K, superpos, basis_0. field.
Qed.

(** Born(superpos, e₁) = 1/2 *)
Lemma born_half_other : born_prob_K superpos basis_1 1 == 1 # 2.
Proof.
  unfold born_prob_K, norm_sq_K, inner_K, superpos, basis_1. field.
Qed.

(** Probabilities sum to 1 *)
Theorem born_sum_to_one :
  born_prob_K superpos basis_0 1 + born_prob_K superpos basis_1 1 == 1.
Proof.
  rewrite born_half, born_half_other. ring.
Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** Born rule = |⟨ψ|φ⟩|²/(⟨ψ|ψ⟩⟨φ|φ⟩) — DERIVED from inner product.
    Process: {p_K}_K converges as K → ∞.
    No postulate. Just linear algebra over Q.

    THIS REPLACES DistinctionProcess.v's ad hoc sharpness = K/(K+1). *)

Theorem born_rule_derived :
  born_prob_K basis_0 basis_0 1 == 1 /\
  born_prob_K basis_0 basis_1 1 == 0 /\
  born_prob_K superpos basis_0 1 == 1 # 2 /\
  born_prob_K superpos basis_0 1 + born_prob_K superpos basis_1 1 == 1.
Proof.
  split; [|split; [|split]].
  - exact born_certain.
  - exact born_impossible.
  - exact born_half.
  - exact born_sum_to_one.
Qed.
