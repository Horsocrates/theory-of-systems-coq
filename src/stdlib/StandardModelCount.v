(** * StandardModelCount.v -- Standard Model Gauge Group Generator Count as ToS System
    Elements: U(1) x SU(2) x SU(3) generator counts, SU(5) embedding
    Roles:    SM has 1+3+8=12 generators; SU(5) GUT has 24, extra 12 for leptoquarks
    Rules:    Generator counting from GaugeFromPlanes decomposition
    Status:   Stdlib -- Six Directions Phase 2, Section D5
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import Lia Arith.
From ToS Require Import stdlib.GaugeFromPlanes.

(* ================================================================== *)
(*  STANDARD MODEL: U(1) x SU(2) x SU(3)                               *)
(*  U(1): 1 generator                                                  *)
(*  SU(2): 3 generators                                                *)
(*  SU(3): 8 generators                                                *)
(*  Total: 12                                                           *)
(* ================================================================== *)

Definition u1_generators : nat := 1.

Definition sm_total : nat := u1_generators + su_generators 2 + su_generators 3.

Lemma standard_model_count : sm_total = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma sm_breakdown : (1 + 3 + 8 = 12)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SU(5) GUT EMBEDDING                                                 *)
(* ================================================================== *)

Lemma su5_total : su_generators 5 = 24.
Proof. exact su5_generators. Qed.

Lemma su5_extra : (su_generators 5 - sm_total = 12)%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma su5_contains_sm : (sm_total <= su_generators 5)%nat.
Proof. vm_compute. lia. Qed.

(* ================================================================== *)
(*  DECOMPOSITION CHECKS                                                *)
(* ================================================================== *)

Lemma su2_in_sm : su_generators 2 = 3.
Proof. exact su2_generators. Qed.

Lemma su3_in_sm : su_generators 3 = 8.
Proof. exact su3_generators. Qed.

Lemma u1_is_1 : u1_generators = 1.
Proof. reflexivity. Qed.

Lemma sm_total_sum : sm_total = (u1_generators + su_generators 2 + su_generators 3)%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                           *)
(* ================================================================== *)

Theorem sm_count_synthesis :
  (sm_total = 12) /\
  (su_generators 5 = 24) /\
  (su_generators 5 - sm_total = 12)%nat.
Proof.
  split. { exact standard_model_count. }
  split. { exact su5_total. }
  exact su5_extra.
Qed.
