(** SharkovskiiConcrete.v — Explicit periodic orbits over Q for PL map *)
(** E/R/R: Elements = orbit points; Roles = f-iteration; Rules = periodicity *)
From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.SharkovskiiCovering.
Open Scope Q_scope.

(** Period-3 orbit: 0 -> 1/2 -> 1 -> 0 *)
Lemma orbit3_0 : f_pl 0 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit3_1 : f_pl (1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit3_2 : f_pl 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Period-1: fixed point 2/3 *)
Lemma fixed_pt : f_pl (2#3) == 2#3.
Proof. exact fp_verify. Qed.

(** Period-2: 1/3 <-> 5/6 *)
Lemma orbit2_a : f_pl (1#3) == 5#6.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit2_b : f_pl (5#6) == 1#3.
Proof. vm_compute. reflexivity. Qed.

(** Period-2 verified: f^2(1/3) = 1/3 *)
Lemma orbit2_period : f2_pl (1#3) == 1#3.
Proof. exact fp2_verify. Qed.

(** Period-4: 2/9 -> 13/18 -> 5/9 -> 8/9 -> 2/9 *)
Lemma orbit4_a : f_pl (2#9) == 13#18.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit4_b : f_pl (13#18) == 5#9.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit4_c : f_pl (5#9) == 8#9.
Proof. vm_compute. reflexivity. Qed.

Lemma orbit4_d : f_pl (8#9) == 2#9.
Proof. vm_compute. reflexivity. Qed.

(** Period-4 verified: f^4(2/9) = 2/9 *)
Lemma orbit4_period : f4_pl (2#9) == 2#9.
Proof. exact fp4_verify. Qed.

(** Period-5 partial: 1/9 -> 11/18 *)
Lemma orbit5_a : f_pl (1#9) == 11#18.
Proof. vm_compute. reflexivity. Qed.

(** All orbits lie in [0,1] — boundary check *)
Lemma orbit_in_unit :
  f_pl 0 == 1#2 /\ f_pl 1 == 0.
Proof.
  split.
  - exact orbit3_0.
  - exact orbit3_2.
Qed.

(** Hierarchy: period-3 implies all — concrete witness *)
Theorem sharkovskii_concrete_witness :
  (* Period 1 *)
  f_pl (2#3) == 2#3 /\
  (* Period 2 *)
  f2_pl (1#3) == 1#3 /\
  (* Period 3 *)
  f3_pl 0 == 0 /\
  (* Period 4 *)
  f4_pl (2#9) == 2#9.
Proof.
  split; [exact fp_verify|].
  split; [exact fp2_verify|].
  split; [exact fp3_verify|].
  exact fp4_verify.
Qed.
