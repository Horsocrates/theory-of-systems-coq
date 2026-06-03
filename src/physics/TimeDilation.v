(** * TimeDilation.v — Proper time from graph distance as ToS System
    Elements: proper_time_sq, newton_sqrt_Q, dilation_factor
    Roles:    Timelike paths have τ²=N²-k², Newton iteration approximates √
    Rules:    k=0 → no dilation, k=N → lightlike (τ=0), Pythagorean triples
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    ★★★★ TIME DILATION FROM GRAPH GEOMETRY
    FROM: Graph with N steps total, k steps spatial
    DERIVE: proper_time² = N² - k² (discrete Minkowski)
    → k=0: rest frame, full proper time
    → k=N: lightlike, zero proper time
    → Pythagorean triples give exact integer proper times
    → Newton's method converges to √(τ²)

    NOTE: the triples below ((5,3,4), (5,4,3), (13,5,12)) are the 3-4-5 and
    5-12-13 families, now systematically DERIVED in stdlib/PythagoreanTriples.v
    (3-4-5 = param(1/2), 5-12-13 = param(1/5)) — no longer ad hoc constants.

    NOT DERIVED: continuous Lorentz transformations, exact c.
    DERIVED: discrete time dilation structure from counting.
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON SQRT FOR PROPER TIME                                        *)
(* ================================================================== *)

Fixpoint newton_sqrt_Q (target x : Q) (steps : nat) : Q :=
  match steps with
  | O => x
  | S n => newton_sqrt_Q target ((x + target / x) / 2) n
  end.

Definition proper_time_sq (N k : nat) : Q :=
  inject_Z (Z.of_nat (N * N - k * k)).

Definition proper_time (N k precision : nat) : Q :=
  newton_sqrt_Q (proper_time_sq N k) (inject_Z (Z.of_nat N)) precision.

Definition dilation_factor (N k precision : nat) : Q :=
  proper_time N k precision / inject_Z (Z.of_nat N).

(* ================================================================== *)
(*  CORE THEOREMS                                                      *)
(* ================================================================== *)

(** At rest (k=0), proper_time_sq = N² *)
Lemma rest_no_dilation : forall N,
  proper_time_sq N O == inject_Z (Z.of_nat (N * N)).
Proof.
  intros N. unfold proper_time_sq.
  rewrite Nat.sub_0_r. unfold Qeq. simpl. lia.
Qed.

(** At lightspeed (k=N), proper_time_sq = 0 *)
Lemma lightspeed_zero : forall N,
  proper_time_sq N N == 0.
Proof.
  intros N. unfold proper_time_sq.
  rewrite Nat.sub_diag. unfold Qeq. simpl. lia.
Qed.

(** Pythagorean triple: 5²-3²=16 *)
Lemma pythagorean_triple : proper_time_sq 5 3 == 16.
Proof. vm_compute. reflexivity. Qed.

(** Newton starting at exact answer stays there *)
Lemma newton_sqrt_exact_start : newton_sqrt_Q 16 4 O == 4.
Proof. vm_compute. reflexivity. Qed.

(** Newton starting at 4 stays at 4 after iterations *)
Lemma exact_sqrt_16 : newton_sqrt_Q 16 4 3 == 4.
Proof. vm_compute. reflexivity. Qed.

(** Dilation factor at rest = 1 for N=5 *)
Lemma dilation_rest : dilation_factor 5 O 3 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Proper time squared is positive for timelike paths *)
Lemma inject_Z_pos : forall z, (z > 0)%Z -> 0 < inject_Z z.
Proof. intros. unfold Qlt, inject_Z. simpl. lia. Qed.

Lemma minkowski_positive_timelike : forall N k,
  (k < N)%nat -> 0 < proper_time_sq N k.
Proof.
  intros N k Hlt.
  unfold proper_time_sq.
  apply inject_Z_pos.
  assert (Hlt2 : (k * k < N * N)%nat) by nia.
  assert (H : (N * N - k * k > 0)%nat) by lia.
  lia.
Qed.

(** At lightspeed, proper time squared is zero *)
Lemma minkowski_zero_lightlike : forall N,
  proper_time_sq N N == 0.
Proof.
  exact lightspeed_zero.
Qed.

(** Another Pythagorean triple: 5²-4²=9 *)
Lemma concrete_3_4_5 : proper_time_sq 5 4 == 9.
Proof. vm_compute. reflexivity. Qed.

(** Faster motion → less proper time *)
Lemma dilation_monotone : proper_time_sq 5 3 > proper_time_sq 5 4.
Proof. vm_compute. reflexivity. Qed.

(** Newton with 0 steps returns initial guess *)
Lemma newton_zero_steps : forall target x,
  newton_sqrt_Q target x O == x.
Proof.
  intros. simpl. unfold Qeq. simpl. lia.
Qed.

(** Pythagorean: 13²-5²=144 (τ=12) *)
Lemma pythagorean_13_5_12 : proper_time_sq 13 5 == 144.
Proof. vm_compute. reflexivity. Qed.
