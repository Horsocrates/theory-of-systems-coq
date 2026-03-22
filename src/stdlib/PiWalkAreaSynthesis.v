(* PiWalkAreaSynthesis.v — Grand synthesis: discrete circle, pi approximations, dimensions *)
(* E/R/R: Elements = all Pi constructions, Roles = synthesis, Rules = cross-file consistency *)

From Stdlib Require Import ZArith QArith.
From ToS Require Import DiscreteCircle PiFromArea PiDimensional.

(** P = 8R + 4 at R = 10 *)
Lemma synth_P_10 : P_circle 10 = (8 * 10 + 4)%Z.
Proof. reflexivity. Qed.

(** N = 317 at R = 10 *)
Lemma synth_N_10 : N_circle 10 = 317%Z.
Proof. reflexivity. Qed.

(** pi_area(10) = 317/100 *)
Lemma synth_pi_area_10 : Qeq (pi_area 10) (317 # 100).
Proof. vm_compute. reflexivity. Qed.

(** pi_walk(10) = 21/5 = 4.2 *)
Lemma synth_pi_walk_10 : Qeq (pi_walk 10) (21 # 5).
Proof. vm_compute. reflexivity. Qed.

(** pi_count(4) = 2: four dimensions need pi^2 *)
Lemma synth_pi_count_4 : pi_count 4%nat = 2%nat.
Proof. simpl. reflexivity. Qed.

(** Walk decreases monotonically toward 4 *)
Lemma synth_walk_mono : Qlt (pi_walk 20) (pi_walk 10) /\ Qlt (pi_walk 10) (pi_walk 5).
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Area and walk both approximate pi from different sides *)
Lemma synth_area_vs_walk_10 : Qlt (pi_area 10) (pi_walk 10).
Proof. vm_compute. reflexivity. Qed.

(** 3D = 1 plane + 1 line, 4D = 2 planes + 0 lines *)
Lemma synth_decomp_3_4 :
  n_planes 3%nat = 1%nat /\ has_extra_line 3%nat = true /\
  n_planes 4%nat = 2%nat /\ has_extra_line 4%nat = false.
Proof. repeat split; simpl; reflexivity. Qed.

(** N grows: N(5) < N(10) *)
Lemma synth_N_growth : (N_circle 5 < N_circle 10)%Z.
Proof. vm_compute. reflexivity. Qed.

(** Pi count grows with dimension *)
Lemma synth_pi_count_growth : Nat.ltb (pi_count 2%nat) (pi_count 6%nat) = true.
Proof. simpl. reflexivity. Qed.
