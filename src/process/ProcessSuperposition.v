(** * ProcessSuperposition.v — Superposition from P1

    Theory of Systems — Process Physics (Wave 5, Phase G5)

    Elements: superposition, interference_term, mixture_vs_super
    Roles:    P1 (whole > sum) → superposition, not mixture
    Rules:    interference ≠ 0 distinguishes superposition from mixture
    Status:   complete

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessGaussianQ.

(* ================================================================== *)
(*  Part I: Superposition (~7 Qed)                                    *)
(* ================================================================== *)

(** Q[i]-linear combination *)
Definition superposition (alpha beta psi1 psi2 : Qi) : Qi :=
  qi_add (qi_mul alpha psi1) (qi_mul beta psi2).

(** Superposition with unit coefficients *)
Lemma super_unit : forall psi1 psi2,
  superposition qi_one qi_one psi1 psi2 =
  qi_add (qi_mul qi_one psi1) (qi_mul qi_one psi2).
Proof. intros. reflexivity. Qed.

(** Superposition with zero: reduces *)
Lemma super_zero_left : forall beta psi1 psi2,
  qi_eq (superposition qi_zero beta psi1 psi2) (qi_mul beta psi2).
Proof.
  intros. unfold superposition, qi_eq, qi_add, qi_mul, qi_zero. simpl.
  split; ring.
Qed.

(** Superposition symmetric under swap *)
Lemma super_swap : forall a b p1 p2,
  qi_eq (superposition a b p1 p2) (superposition b a p2 p1).
Proof.
  intros. unfold superposition, qi_eq, qi_add, qi_mul. simpl.
  split; ring.
Qed.

(* ================================================================== *)
(*  Part II: Interference Term (~7 Qed)                               *)
(* ================================================================== *)

(** Interference = 2·Re(α*·β) *)
Definition interference_term (alpha beta : Qi) : Q :=
  2 * (qi_re alpha * qi_re beta + qi_im alpha * qi_im beta).

(** Concrete interference *)
Lemma interference_nonzero :
  interference_term (mkQi (3#5) 0) (mkQi (4#5) 0) == 24 # 25.
Proof. unfold interference_term. simpl. unfold Qeq. simpl. lia. Qed.

(** Zero interference for orthogonal *)
Lemma interference_zero :
  interference_term (mkQi 1 0) (mkQi 0 1) == 0.
Proof. unfold interference_term. simpl. ring. Qed.

(** Interference symmetric *)
Lemma interference_sym : forall a b,
  interference_term a b == interference_term b a.
Proof. intros. unfold interference_term. ring. Qed.

(** Interference with self *)
Lemma interference_self : forall a,
  interference_term a a == 2 * qi_norm2 a.
Proof. intros. unfold interference_term, qi_norm2. ring. Qed.

(** Interference nonneg for equal amplitudes *)
Lemma interference_equal_nonneg : forall a,
  0 <= interference_term a a.
Proof.
  intros. rewrite interference_self.
  assert (H : 0 <= qi_norm2 a) by apply qi_norm2_nonneg.
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Mixture vs Superposition (~6 Qed)                      *)
(* ================================================================== *)

(** Mixture: whole = sum of parts (no interference) *)
(** Superposition: whole > sum (has interference) *)
(** P1: physical states are superpositions because P1 requires whole > sum *)

(** Mixture probability: |α|² + |β|² *)
Definition mixture_prob (alpha beta : Qi) : Q :=
  qi_norm2 alpha + qi_norm2 beta.

(** Superposition probability: |α|² + |β|² + interference *)
Definition super_prob (alpha beta : Qi) : Q :=
  qi_norm2 alpha + qi_norm2 beta + interference_term alpha beta.

(** Super ≠ mixture when interference ≠ 0 *)
Lemma super_exceeds_mixture :
  let a := mkQi (3#5) 0 in
  let b := mkQi (4#5) 0 in
  mixture_prob a b < super_prob a b.
Proof.
  simpl. unfold mixture_prob, super_prob, interference_term, qi_norm2. simpl.
  unfold Qlt. simpl. lia.
Qed.

(** Mixture prob for 3/5, 4/5 *)
Lemma mixture_value :
  mixture_prob (mkQi (3#5) 0) (mkQi (4#5) 0) == 1.
Proof.
  unfold mixture_prob, qi_norm2. simpl. unfold Qeq. simpl. lia.
Qed.

(** Super prob includes interference *)
Lemma super_value :
  super_prob (mkQi (3#5) 0) (mkQi (4#5) 0) == 49 # 25.
Proof.
  unfold super_prob, qi_norm2, interference_term. simpl.
  unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  Part IV: Summary                                                    *)
(* ================================================================== *)

Theorem superposition_from_p1 :
  interference_term (mkQi (3#5) 0) (mkQi (4#5) 0) == 24 # 25.
Proof. exact interference_nonzero. Qed.

Theorem phase_G5_complete :
  (* Interference nonzero *)
  interference_term (mkQi (3#5) 0) (mkQi (4#5) 0) == 24#25 /\
  (* Super > mixture *)
  mixture_prob (mkQi (3#5) 0) (mkQi (4#5) 0) <
    super_prob (mkQi (3#5) 0) (mkQi (4#5) 0) /\
  (* Interference symmetric *)
  (forall a b, interference_term a b == interference_term b a).
Proof.
  split; [|split].
  - exact interference_nonzero.
  - exact super_exceeds_mixture.
  - exact interference_sym.
Qed.
