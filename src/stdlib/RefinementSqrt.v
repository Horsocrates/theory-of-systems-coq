(** * RefinementSqrt.v -- Process refinement for √2: Newton vs CF
    CLASSICAL: √2 = 1.41421... One number.
    PROCESS Newton: 1, 3/2, 17/12, 577/408, ... (quadratic convergence)
    PROCESS CF:     1, 3/2, 7/5, 17/12, ... (linear convergence)
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.ProcessRefinement.

Open Scope Q_scope.

(* ================================================================== *)
(*  NEWTON PROCESS FOR √2: x_{n+1} = (x_n + 2/x_n)/2                  *)
(* ================================================================== *)

Fixpoint sqrt2_newton (K : nat) : Q :=
  match K with
  | O => 1
  | S k => let x := sqrt2_newton k in (x + 2 / x) / 2
  end.

(* ================================================================== *)
(*  CF PROCESS FOR √2: [1; 2, 2, 2, ...] → p_K/q_K                    *)
(* ================================================================== *)

Fixpoint sqrt2_cf_p (K : nat) : Z :=
  match K with
  | O => 1
  | S O => 3
  | S (S m as p) => (2 * sqrt2_cf_p p + sqrt2_cf_p m)%Z
  end.

Fixpoint sqrt2_cf_q (K : nat) : Z :=
  match K with
  | O => 1
  | S O => 2
  | S (S m as p) => (2 * sqrt2_cf_q p + sqrt2_cf_q m)%Z
  end.

Definition sqrt2_cf (K : nat) : Q :=
  inject_Z (sqrt2_cf_p K) / inject_Z (sqrt2_cf_q K).

(* ================================================================== *)
(*  CONCRETE VALUES                                                    *)
(* ================================================================== *)

Lemma newton_0 : sqrt2_newton 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_1 : sqrt2_newton 1%nat == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_2 : sqrt2_newton 2%nat == 17#12.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_0 : sqrt2_cf 0%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_1 : sqrt2_cf 1%nat == 3#2.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_2 : sqrt2_cf 2%nat == 7#5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SAME AT SOME STEPS, DIFFERENT AT OTHERS                            *)
(* ================================================================== *)

Lemma agree_at_0 : sqrt2_newton 0%nat == sqrt2_cf 0%nat.
Proof. rewrite newton_0, cf_0. reflexivity. Qed.

Lemma agree_at_1 : sqrt2_newton 1%nat == sqrt2_cf 1%nat.
Proof. rewrite newton_1, cf_1. reflexivity. Qed.

Lemma differ_at_2 : ~ (sqrt2_newton 2%nat == sqrt2_cf 2%nat).
Proof.
  rewrite newton_2, cf_2. unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  QUALITY: |x² - 2| measures proximity to √2                        *)
(* ================================================================== *)

Definition sqrt2_quality (x : Q) : Q := Qabs (x * x - 2).

Lemma newton_quality_2 : sqrt2_quality (17#12) == 1#144.
Proof. unfold sqrt2_quality. vm_compute. reflexivity. Qed.

Lemma cf_quality_2 : sqrt2_quality (7#5) == 1#25.
Proof. unfold sqrt2_quality. vm_compute. reflexivity. Qed.

Lemma newton_better_at_2 :
  sqrt2_quality (sqrt2_newton 2%nat) < sqrt2_quality (sqrt2_cf 2%nat).
Proof.
  assert (H1 : sqrt2_quality (sqrt2_newton 2%nat) == 1#144) by (vm_compute; reflexivity).
  assert (H2 : sqrt2_quality (sqrt2_cf 2%nat) == 1#25) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.

(** ★ SQRT2 STRICT REFINEMENT *)
Theorem sqrt2_strict_refinement :
  sqrt2_newton 0%nat == sqrt2_cf 0 /\
  sqrt2_newton 1%nat == sqrt2_cf 1 /\
  ~ (sqrt2_newton 2%nat == sqrt2_cf 2%nat) /\
  sqrt2_quality (sqrt2_newton 2%nat) < sqrt2_quality (sqrt2_cf 2%nat).
Proof.
  split; [|split; [|split]].
  - exact agree_at_0.
  - exact agree_at_1.
  - exact differ_at_2.
  - exact newton_better_at_2.
Qed.
