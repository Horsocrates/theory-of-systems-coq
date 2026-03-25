(** * HydrogenPhaseTransition.v — Reentrant phase transition in screened hydrogen
    Elements: phase classification (symmetric/broken), transition points
    Roles:    Screening drives symmetric -> broken -> symmetric reentrant transition
    Rules:    Breaking threshold defines phases; reentrance proven from symmetry_breaking data
    Status:   complete
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Qabs Lia.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.HydrogenScreening.
From ToS Require Import stdlib.HydrogenSymmetryBreaking.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Phase classification                                       *)
(* ================================================================== *)

(** A phase is "symmetric" if breaking < threshold, "broken" otherwise.
    We use threshold = 1/400 = 25/10000 *)

Definition phase_threshold : Q := 25#10000.

Definition is_symmetric (r_s_tenth : nat) : bool :=
  Qle_bool (symmetry_breaking r_s_tenth) phase_threshold.

(* ================================================================== *)
(*  Part II: Phase at specific screening values                        *)
(* ================================================================== *)

Lemma phase_zero_symmetric : is_symmetric 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma phase_1_symmetric : is_symmetric 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma phase_5_broken : is_symmetric 5 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma phase_10_broken : is_symmetric 10 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma phase_50_symmetric : is_symmetric 50 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Reentrant transition — symmetric -> broken -> symmetric  *)
(* ================================================================== *)

Lemma reentrant_phase1 : is_symmetric 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma reentrant_phase2 : is_symmetric 10 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma reentrant_phase3 : is_symmetric 50 = true.
Proof. vm_compute. reflexivity. Qed.

(** The full reentrant statement: there exist r1 < r2 < r3 such that
    symmetric at r1, broken at r2, symmetric at r3 *)
Lemma reentrant_transition :
  exists r1 r2 r3 : nat,
    (r1 < r2)%nat /\ (r2 < r3)%nat /\
    is_symmetric r1 = true /\
    is_symmetric r2 = false /\
    is_symmetric r3 = true.
Proof.
  exists 0%nat, 10%nat, 50%nat.
  repeat split; try lia; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  Part IV: Breaking at maximum exceeds threshold                     *)
(* ================================================================== *)

Lemma max_breaking_exceeds_threshold : symmetry_breaking 10 > phase_threshold.
Proof.
  unfold phase_threshold.
  assert (H10 : symmetry_breaking 10 == 50#10000)
    by (unfold symmetry_breaking; vm_compute; reflexivity).
  rewrite H10. lra.
Qed.
