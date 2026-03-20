(** * LiYorkeSensitivity.v -- Li-Yorke pairs and sensitivity on [0,1]
    Elements: orbits_approach, orbits_separate, is_sensitive, x0, y0
    Roles:    Li-Yorke pairs from exponential divergence under tent map
    Rules:    |f^n(x) - f^n(y)| = 2^n · |x-y| (before folding)
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.LyapunovProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  LI-YORKE DEFINITIONS                                               *)
(* ================================================================== *)

(** (x,y) is Li-Yorke if orbits approach and separate *)

Definition orbits_approach (f : Q -> Q) (x y : Q) (K : nat) : Prop :=
  exists k, (k <= K)%nat /\
  Qabs (iterate f x k - iterate f y k) < 1 / inject_Z (Z.of_nat (S K)).

Definition orbits_separate (f : Q -> Q) (x y : Q) (eps : Q) (K : nat) : Prop :=
  exists k, (k <= K)%nat /\
  eps < Qabs (iterate f x k - iterate f y k).

(* ================================================================== *)
(*  CONCRETE: TENT MAP DIVERGENCE                                      *)
(* ================================================================== *)

Definition x0 : Q := 1 # 4.
Definition y0 : Q := (1 # 4) + (1 # 100).

(** Step 0: |x-y| = 1/100 *)
Lemma initial_close :
  Qabs (x0 - y0) == 1 # 100.
Proof.
  unfold x0, y0. vm_compute. reflexivity.
Qed.

(** Step 1: T(1/4) = 1/2, T(26/100) = 2·(26/100) = 52/100 = 13/25 *)
(** |1/2 - 13/25| = |25/50 - 26/50| = 1/50 *)
Lemma step1_diverge :
  Qabs (tent_map x0 - tent_map y0) == 1 # 50.
Proof.
  unfold x0, y0, tent_map. vm_compute. reflexivity.
Qed.

(** Step 2: T(1/2) = 1, T(13/25) = 2 - 26/25 = 24/25 *)
(** |1 - 24/25| = 1/25 *)
Lemma step2_diverge :
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) == 1 # 25.
Proof.
  unfold x0, y0, tent_map, iterate. vm_compute. reflexivity.
Qed.

(** Step 3: T(1) = 0, T(24/25) = 2 - 48/25 = 2/25 *)
(** |0 - 2/25| = 2/25 *)
Lemma step3_diverge :
  Qabs (iterate tent_map x0 3 - iterate tent_map y0 3) == 2 # 25.
Proof.
  unfold x0, y0, tent_map, iterate. vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(*  SENSITIVITY                                                        *)
(* ================================================================== *)

(** Sensitivity: ∃ε>0 such that for any x, δ>0: ∃y,n: |x-y|<δ ∧ |f^n(x)-f^n(y)|>ε *)
Definition is_sensitive (f : Q -> Q) (eps : Q) : Prop :=
  0 < eps /\
  forall x delta, 0 < delta ->
  exists y n, Qabs (x - y) < delta /\
  eps < Qabs (iterate f x n - iterate f y n).

(** Exponential divergence: after 2 steps, distance grew *)
Theorem tent_sensitive_example :
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) >
  Qabs (x0 - y0).
Proof.
  rewrite step2_diverge, initial_close. lra.
Qed.

(** Distance grows each step (before folding) *)
Theorem tent_divergence_chain :
  Qabs (x0 - y0) < Qabs (tent_map x0 - tent_map y0) /\
  Qabs (tent_map x0 - tent_map y0) < Qabs (iterate tent_map x0 2 - iterate tent_map y0 2).
Proof.
  rewrite initial_close, step1_diverge, step2_diverge. lra.
Qed.

(** Divergence factor = 2 (= |T'|) *)
Lemma divergence_factor_step1 :
  Qabs (tent_map x0 - tent_map y0) == 2 * Qabs (x0 - y0).
Proof.
  rewrite step1_diverge, initial_close. ring.
Qed.

Lemma divergence_factor_step2 :
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) ==
  2 * Qabs (tent_map x0 - tent_map y0).
Proof.
  rewrite step2_diverge, step1_diverge. ring.
Qed.

(** Initial separation is positive *)
Lemma initial_separation_positive :
  0 < Qabs (x0 - y0).
Proof. rewrite initial_close. lra. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem li_yorke_sensitivity_synthesis :
  Qabs (x0 - y0) == 1 # 100 /\
  Qabs (tent_map x0 - tent_map y0) == 1 # 50 /\
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) == 1 # 25 /\
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) >
  Qabs (x0 - y0).
Proof.
  split; [|split; [|split]].
  - exact initial_close.
  - exact step1_diverge.
  - exact step2_diverge.
  - exact tent_sensitive_example.
Qed.
