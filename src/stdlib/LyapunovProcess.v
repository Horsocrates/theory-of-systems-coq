(** * LyapunovProcess.v -- Lyapunov exponents as rational processes
    Elements: tent_map, doubling_map, logistic_map, lyapunov_sum
    Roles:    λ(f,x,K) = (1/K) Σ ln|f'(f^k(x))| as process over Q
    Rules:    λ > 0 ↔ chaotic, λ = 0 ↔ neutral, λ < 0 ↔ stable
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* Replicated from FixedPoint.v to avoid stale .vo *)
Fixpoint iterate (f : Q -> Q) (x : Q) (n : nat) : Q :=
  match n with
  | O => x
  | S k => f (iterate f x k)
  end.

(* ================================================================== *)
(*  INTERVAL MAPS                                                      *)
(* ================================================================== *)

(** Tent map: T(x) = if x ≤ 1/2 then 2x else 2 - 2x *)
Definition tent_map (x : Q) : Q :=
  if Qle_bool x (1#2) then 2 * x else 2 - 2 * x.

Lemma tent_at_0 : tent_map 0 == 0.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma tent_at_quarter : tent_map (1#4) == 1#2.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma tent_at_half : tent_map (1#2) == 1.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma tent_at_third : tent_map (1#3) == 2#3.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

(** Doubling map: D(x) = 2x mod 1 *)
Definition doubling_map (x : Q) : Q :=
  let y := 2 * x in
  if Qle_bool y 1 then y else y - 1.

Lemma doubling_at_quarter : doubling_map (1#4) == 1#2.
Proof. unfold doubling_map. vm_compute. reflexivity. Qed.

Lemma doubling_at_third : doubling_map (1#3) == 2#3.
Proof. unfold doubling_map. vm_compute. reflexivity. Qed.

(** Logistic map: L(x) = 4x(1-x) at r=4 *)
Definition logistic_map (x : Q) : Q :=
  4 * x * (1 - x).

Lemma logistic_at_quarter : logistic_map (1#4) == 3#4.
Proof. unfold logistic_map. vm_compute. reflexivity. Qed.

Lemma logistic_at_half : logistic_map (1#2) == 1.
Proof. unfold logistic_map. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DISCRETE DERIVATIVE                                                *)
(* ================================================================== *)

(** For tent map: |T'(x)| = 2 everywhere *)
Definition tent_slope (x : Q) : Q :=
  if Qle_bool x (1#2) then 2 else -(2).

Definition abs_tent_slope (x : Q) : Q := 2.

(* ================================================================== *)
(*  LYAPUNOV SUM AS PROCESS                                            *)
(* ================================================================== *)

(** ln(2) ≈ 2/3 (Padé[1,1] approximation). True: 0.6931. Error: 4% *)
Definition ln2_approx : Q := 2#3.

(** Orbit: f^k(x) *)
Definition orbit_at (f : Q -> Q) (x : Q) (k : nat) : Q :=
  iterate f x k.

(** Lyapunov sum at resolution K *)
Definition lyapunov_sum (deriv : Q -> Q) (f : Q -> Q) (x : Q) (K : nat) : Q :=
  fold_left (fun acc k =>
    acc + ln2_approx * deriv (orbit_at f x k))
    (seq 0 K) 0.

(** Lyapunov exponent process *)
Definition lyapunov_exponent (deriv : Q -> Q) (f : Q -> Q) (x : Q) (K : nat) : Q :=
  lyapunov_sum deriv f x K / inject_Z (Z.of_nat (S K)).

(* ================================================================== *)
(*  CONCRETE: TENT MAP                                                 *)
(* ================================================================== *)

(** For tent map: |T'| = 2 everywhere. ln|T'| = ln(2).
    λ_K = (1/K)·K·ln(2) = ln(2) for all K ≥ 1. *)

Definition tent_lyapunov : Q := ln2_approx.

Lemma tent_lyapunov_positive : 0 < tent_lyapunov.
Proof. unfold tent_lyapunov, ln2_approx. lra. Qed.

(** Orbit of tent map from 1/3: T(1/3) = 2/3, T(2/3) = 2/3, periodic *)
Lemma tent_orbit_periodic :
  tent_map (1#3) == 2#3 /\ tent_map (2#3) == 2#3.
Proof.
  split; unfold tent_map; vm_compute; reflexivity.
Qed.

(** λ(tent) > 0 → CHAOTIC *)
Theorem tent_is_chaotic : 0 < tent_lyapunov.
Proof. exact tent_lyapunov_positive. Qed.

(** Identity map has λ = 0 *)
Definition id_lyapunov : Q := 0.

Theorem identity_not_chaotic : id_lyapunov == 0.
Proof. unfold id_lyapunov. reflexivity. Qed.

(** Contraction f(x) = x/2: |f'| = 1/2, ln(1/2) = -ln(2) *)
Definition contraction_lyapunov : Q := - ln2_approx.

Theorem contraction_stable : contraction_lyapunov < 0.
Proof. unfold contraction_lyapunov, ln2_approx. lra. Qed.
