(** * SU3Representations.v -- SU(3) irreps: dimensions and Casimirs
    Elements: su3_dim, su3_casimir, fundamental/adjoint/decuplet
    Roles:    Irreducible representations of SU(3) labeled by (p,q) ∈ ℕ²
    Rules:    dim(p,q) = (p+1)(q+1)(p+q+2)/2, C₂ = (p²+q²+pq+3p+3q)/3
    Status:   Gauge
    STATUS: 20 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  DIMENSION FORMULA                                                  *)
(* ================================================================== *)

(** SU(3) irreps labeled by (p,q) ∈ ℕ² (Dynkin labels)
    p = number of upper indices, q = number of lower indices
    dim(p,q) = (p+1)(q+1)(p+q+2)/2 *)

Definition su3_dim (p q : nat) : nat :=
  (S p) * (S q) * (S (S (p + q))) / 2.

(* ================================================================== *)
(*  FUNDAMENTAL REPRESENTATIONS                                        *)
(* ================================================================== *)

Lemma dim_trivial : su3_dim 0 0 = 1%nat.
Proof. reflexivity. Qed.

Lemma dim_fund : su3_dim 1 0 = 3%nat.
Proof. reflexivity. Qed.

Lemma dim_antifund : su3_dim 0 1 = 3%nat.
Proof. reflexivity. Qed.

Lemma dim_adjoint : su3_dim 1 1 = 8%nat.
Proof. reflexivity. Qed.

Lemma dim_6 : su3_dim 2 0 = 6%nat.
Proof. reflexivity. Qed.

Lemma dim_10 : su3_dim 3 0 = 10%nat.
Proof. reflexivity. Qed.

Lemma dim_27 : su3_dim 2 2 = 27%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  QUADRATIC CASIMIR                                                  *)
(* ================================================================== *)

(** C₂(p,q) = (p² + q² + pq + 3p + 3q)/3 *)
Definition su3_casimir (p q : nat) : Q :=
  inject_Z (Z.of_nat (p*p + q*q + p*q + 3*p + 3*q)) * (1#3).

Lemma casimir_trivial : su3_casimir 0 0 == 0.
Proof. unfold su3_casimir. vm_compute. reflexivity. Qed.

Lemma casimir_fund : su3_casimir 1 0 == 4#3.
Proof. unfold su3_casimir. vm_compute. reflexivity. Qed.

Lemma casimir_antifund : su3_casimir 0 1 == 4#3.
Proof. unfold su3_casimir. vm_compute. reflexivity. Qed.

Lemma casimir_adjoint : su3_casimir 1 1 == 3.
Proof. unfold su3_casimir. vm_compute. reflexivity. Qed.

Lemma casimir_6 : su3_casimir 2 0 == 10#3.
Proof. unfold su3_casimir. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONJUGATION SYMMETRY                                               *)
(* ================================================================== *)

(** (p,q) ↔ (q,p): conjugation swaps Dynkin labels *)
Lemma dim_conjugate : forall p q, su3_dim p q = su3_dim q p.
Proof.
  intros p q. unfold su3_dim.
  rewrite (Nat.add_comm q p).
  rewrite (Nat.mul_comm (S q) (S p)). reflexivity.
Qed.

Lemma casimir_conjugate : forall p q, su3_casimir p q == su3_casimir q p.
Proof.
  intros p q. unfold su3_casimir.
  assert (H : (p * p + q * q + p * q + 3 * p + 3 * q =
               q * q + p * p + q * p + 3 * q + 3 * p)%nat) by lia.
  rewrite H. reflexivity.
Qed.

(* ================================================================== *)
(*  DIMENSION HIERARCHY                                                *)
(* ================================================================== *)

(** Higher representations have larger dimensions *)
Lemma dim_fund_lt_adjoint : (su3_dim 1 0 < su3_dim 1 1)%nat.
Proof. vm_compute. lia. Qed.

Lemma dim_adjoint_lt_27 : (su3_dim 1 1 < su3_dim 2 2)%nat.
Proof. vm_compute. lia. Qed.

(** Casimir increases with representation size *)
Lemma casimir_fund_lt_adj : su3_casimir 1 0 < su3_casimir 1 1.
Proof. rewrite casimir_fund, casimir_adjoint. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem su3_rep_synthesis :
  su3_dim 0 0 = 1%nat /\
  su3_dim 1 0 = 3%nat /\
  su3_dim 1 1 = 8%nat /\
  su3_dim 3 0 = 10%nat /\
  su3_dim 2 2 = 27%nat /\
  su3_casimir 1 0 == 4#3 /\
  su3_casimir 1 1 == 3.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact dim_trivial.
  - exact dim_fund.
  - exact dim_adjoint.
  - exact dim_10.
  - exact dim_27.
  - exact casimir_fund.
  - exact casimir_adjoint.
Qed.
