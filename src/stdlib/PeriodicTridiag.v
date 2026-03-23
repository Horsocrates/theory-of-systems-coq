(** * PeriodicTridiag.v — Periodic vs Open Tridiagonal Matrices
    Elements: Periodic tridiag definition, trace comparison, ring vs chain
    Roles:    Compare spectral properties of ring and chain geometries
    Rules:    Ring trace ≠ chain trace; periodic boundary adds terms
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.
Open Scope Q_scope.

(* ================================================================== *)
(*  TRIDIAGONAL MATRICES                                               *)
(*  Open chain: H_ij = delta(|i-j|, 1)                               *)
(*  Ring: H_ij = delta(|i-j|, 1) + delta(|i-j|, K-1) for K sites    *)
(* ================================================================== *)

Definition abs_diff (a b : nat) : nat :=
  if Nat.leb a b then (b - a)%nat else (a - b)%nat.

Definition chain_entry (K : nat) (i j : nat) : Q :=
  if Nat.eqb (abs_diff i j) 1%nat then 1 else 0.

Definition ring_entry (K : nat) (i j : nat) : Q :=
  if orb (Nat.eqb (abs_diff i j) 1%nat)
         (Nat.eqb (abs_diff i j) (K - 1)%nat) then 1
  else 0.

(* ================================================================== *)
(*  TRACE: always 0 for both (diagonal = 0)                           *)
(* ================================================================== *)

(* Trace for K=3 chain *)
Definition chain_trace_3 : Q :=
  chain_entry 3%nat O O + chain_entry 3%nat (S O) (S O) +
  chain_entry 3%nat (S (S O)) (S (S O)).

Lemma chain_trace_3_zero : chain_trace_3 == 0.
Proof. vm_compute. reflexivity. Qed.

Definition ring_trace_3 : Q :=
  ring_entry 3%nat O O + ring_entry 3%nat (S O) (S O) +
  ring_entry 3%nat (S (S O)) (S (S O)).

Lemma ring_trace_3_zero : ring_trace_3 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  TRACE OF H²: counts number of nonzero off-diagonal entries        *)
(*  Chain: 2*(K-1), Ring: 2*K                                         *)
(* ================================================================== *)

(* H² for 3-chain: (H²)_ii = sum_j H_ij * H_ji *)
Definition chain_h2_diag (K : nat) (i : nat) : Q :=
  let f := chain_entry K in
  f i O * f O i + f i (S O) * f (S O) i + f i (S (S O)) * f (S (S O)) i.

Definition chain_trace_sq_3 : Q :=
  chain_h2_diag 3%nat O + chain_h2_diag 3%nat (S O) + chain_h2_diag 3%nat (S (S O)).

Lemma chain_trace_sq_3_val : chain_trace_sq_3 == 4.
Proof. vm_compute. reflexivity. Qed.

Definition ring_h2_diag (K : nat) (i : nat) : Q :=
  let f := ring_entry K in
  f i O * f O i + f i (S O) * f (S O) i + f i (S (S O)) * f (S (S O)) i.

Definition ring_trace_sq_3 : Q :=
  ring_h2_diag 3%nat O + ring_h2_diag 3%nat (S O) + ring_h2_diag 3%nat (S (S O)).

Lemma ring_trace_sq_3_val : ring_trace_sq_3 == 6.
Proof. vm_compute. reflexivity. Qed.

(* Ring has more connectivity than chain *)
Lemma ring_more_connected : chain_trace_sq_3 < ring_trace_sq_3.
Proof.
  assert (H1 : chain_trace_sq_3 == 4) by (vm_compute; reflexivity).
  assert (H2 : ring_trace_sq_3 == 6) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(* ================================================================== *)
(*  OFF-DIAGONAL ELEMENT COUNTS                                        *)
(* ================================================================== *)

(* Chain K=3: 2 bonds *)
Lemma chain_3_bond_01 : chain_entry 3%nat O (S O) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_3_bond_12 : chain_entry 3%nat (S O) (S (S O)) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma chain_3_no_wrap : chain_entry 3%nat O (S (S O)) == 0.
Proof. vm_compute. reflexivity. Qed.

(* Ring K=3: 3 bonds (adds wraparound) *)
Lemma ring_3_wrap : ring_entry 3%nat O (S (S O)) == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem periodic_tridiag_synthesis :
  chain_trace_3 == 0 /\
  ring_trace_3 == 0 /\
  chain_trace_sq_3 < ring_trace_sq_3 /\
  ring_entry 3%nat O (S (S O)) == 1.
Proof.
  split; [exact chain_trace_3_zero|].
  split; [exact ring_trace_3_zero|].
  split; [exact ring_more_connected|].
  exact ring_3_wrap.
Qed.
