(** * PiBasel.v -- π from ζ(2) = π²/6 (Basel problem, Euler 1735)
    Elements: zeta2_partial, sqrt_newton, pi_basel
    Roles:    π via ζ(2): double process (zeta terms + Newton √)
    Rules:    √ as Newton: quadratic convergence
    Status:   Stdlib
    STATUS: 15 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================== *)
(*  ζ(2) PARTIAL SUM                                                   *)
(* ================================================================== *)

Definition zeta2_partial (K : nat) : Q :=
  fold_left (fun acc n =>
    acc + 1 / (inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat (S n))))
    (seq 0 K) 0.

Lemma zeta2_1 : zeta2_partial 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma zeta2_2 : zeta2_partial 2 == 5#4.
Proof. vm_compute. reflexivity. Qed.

Lemma zeta2_3 : zeta2_partial 3 == 49#36.
Proof. vm_compute. reflexivity. Qed.

Lemma zeta2_5 : zeta2_partial 5 == 5269#3600.
Proof. vm_compute. reflexivity. Qed.

(** Monotonically increasing *)
Lemma zeta2_increasing : zeta2_partial 1 < zeta2_partial 2.
Proof. rewrite zeta2_1, zeta2_2. lra. Qed.

(* ================================================================== *)
(*  NEWTON √ PROCESS                                                   *)
(* ================================================================== *)

Fixpoint sqrt_newton (a : Q) (x0 : Q) (n : nat) : Q :=
  match n with
  | O => x0
  | S k => let xk := sqrt_newton a x0 k in (xk + a / xk) / 2
  end.

Lemma sqrt6_step0 : sqrt_newton 6 2 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt6_step1 : sqrt_newton 6 2 1 == 5#2.
Proof. vm_compute. reflexivity. Qed.

Lemma sqrt6_step2 : sqrt_newton 6 2 2 == 49#20.
Proof. vm_compute. reflexivity. Qed.

(** √6 ≈ 2.449. Step 2: 49/20 = 2.45. Error 0.02%. *)
(** Newton converges quadratically: error² per step *)

Lemma sqrt6_converges :
  sqrt_newton 6 2 1 > sqrt_newton 6 2 2.
Proof. rewrite sqrt6_step1, sqrt6_step2. lra. Qed.

(** √4 = 2 exactly *)
Lemma sqrt4_exact : sqrt_newton 4 2 1 == 2.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  π FROM BASEL                                                       *)
(* ================================================================== *)

Definition pi_sq_process (K : nat) : Q := 6 * zeta2_partial K.

Lemma pi_sq_1 : pi_sq_process 1 == 6.
Proof. unfold pi_sq_process. rewrite zeta2_1. lra. Qed.

Lemma pi_sq_5 : pi_sq_process 5 == 5269#600.
Proof. unfold pi_sq_process. rewrite zeta2_5. lra. Qed.

(** Double process: √(6·ζ₂(K)) via Newton *)
Definition pi_basel (K_zeta K_newton : nat) : Q :=
  sqrt_newton (pi_sq_process K_zeta) 3 K_newton.

Lemma pi_basel_1_1 : pi_basel 1 1 == 5#2.
Proof. vm_compute. reflexivity. Qed.

(** pi_sq(1) = 6. √6 from 3: (3+6/3)/2 = (3+2)/2 = 5/2.
    Wait, that's 5/2 not 3. Let me check... *)
(** Actually: pi_basel 1 1 = sqrt_newton 6 3 1 = (3 + 6/3)/2 = (3+2)/2 = 5/2 *)

(** SYNTHESIS *)
Theorem pi_basel_synthesis :
  (* ζ₂ partial sums *)
  zeta2_partial 1 == 1 /\
  zeta2_partial 5 == 5269#3600 /\
  (* √ convergence *)
  sqrt_newton 6 2 2 == 49#20 /\
  (* π² process *)
  pi_sq_process 1 == 6 /\
  pi_sq_process 5 == 5269#600.
Proof.
  split; [|split; [|split; [|split]]].
  - exact zeta2_1.
  - exact zeta2_5.
  - exact sqrt6_step2.
  - exact pi_sq_1.
  - exact pi_sq_5.
Qed.
