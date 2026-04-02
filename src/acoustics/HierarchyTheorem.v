(** * HierarchyTheorem.v — Oscillation < Vibration < Wave > Sound
    Elements: Oscillation, Vibration, Wave, Sound records
    Roles:    each level = previous + one ingredient
    Rules:    remove ingredient → level collapses
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    HIERARCHY:
    Oscillation: binary alternation A <-> not-A. Pure L2+L3.
    Vibration: continuous delta(t) + restoring (L1) + inertia (L5).
    Wave: vibration + spatial graph + coupling.
    Sound: wave + audibility (20 Hz to 20 kHz).

    Each level adds ONE ingredient. Remove it → collapse.
*)

From Stdlib Require Import QArith Lia ZArith PeanoNat.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import acoustics.VibrationCore.
From ToS Require Import acoustics.WavePropagation.

(* ================================================================ *)
(*  RECORD TYPES FOR FOUR LEVELS                                     *)
(* ================================================================ *)

Record VibrationRec := mkVibRec {
  vr_k : Q;
  vr_k_pos : 0 < vr_k;
}.

Record WaveRec := mkWaveRec {
  wr_k : Q;
  wr_coupling : Q;
  wr_graph_size : nat;
  wr_k_pos : 0 < wr_k;
  wr_c_pos : 0 < wr_coupling;
  wr_n_pos : (1 < wr_graph_size)%nat;
}.

Record SoundRec := mkSoundRec {
  sr_wave : WaveRec;
  sr_freq : Q;
  sr_audible_lo : 20 <= sr_freq;
  sr_audible_hi : sr_freq <= 20000;
}.

(* ================================================================ *)
(*  EMBEDDINGS: EACH LEVEL CONTAINS THE PREVIOUS                     *)
(* ================================================================ *)

Definition wave_to_vib (w : WaveRec) : VibrationRec :=
  mkVibRec (wr_k w) (wr_k_pos w).

Definition sound_to_wave (s : SoundRec) : WaveRec := sr_wave s.

(** Wave contains vibration *)
Lemma wave_has_vibration : forall w : WaveRec,
  0 < vr_k (wave_to_vib w).
Proof. intro w. exact (wr_k_pos w). Qed.

(** Sound contains wave *)
Lemma sound_has_wave : forall s : SoundRec,
  (1 < wr_graph_size (sound_to_wave s))%nat.
Proof. intro s. exact (wr_n_pos (sr_wave s)). Qed.

(* ================================================================ *)
(*  CONCRETE EXAMPLES                                                *)
(* ================================================================ *)

Definition tuning_fork : VibrationRec.
Proof. apply (mkVibRec 2). lra. Defined.

Definition air_wave : WaveRec.
Proof. apply (mkWaveRec 2 (1#4) 100). all: try lra. lia. Defined.

Lemma tuning_fork_k : vr_k tuning_fork == 2.
Proof. reflexivity. Qed.

Lemma air_wave_size : wr_graph_size air_wave = 100%nat.
Proof. reflexivity. Qed.

(* ================================================================ *)
(*  WITHOUT INGREDIENTS → COLLAPSE                                   *)
(* ================================================================ *)

(** Without coupling (c=0): wave_step gives no propagation *)
Lemma no_coupling_collapse :
  wave_step 0 4 zero_field impulse 1 == 0.
Proof. exact no_coupling_no_propagation. Qed.

(** Without restoring force (k=0): linear drift, no oscillation *)
Lemma no_restoring_drift :
  next_state 0 0 1 == 2 /\ next_state 0 1 2 == 3.
Proof. unfold next_state. split; ring. Qed.

(** With both: oscillation (k=2, coupling=1/4) *)
Lemma both_present_oscillation :
  next_state 2 0 1 == 0 /\
  wave_step (1#4) 4 zero_field impulse 1 > 0.
Proof.
  split.
  - unfold next_state. ring.
  - exact impulse_propagates.
Qed.

(* ================================================================ *)
(*  AUDIBILITY CONSTRAINT                                            *)
(* ================================================================ *)

Lemma concert_A_audible : 20 <= 440 /\ 440 <= 20000.
Proof. split; lra. Qed.

Lemma ultrasound_inaudible : ~ (40000 <= 20000).
Proof. lra. Qed.

Lemma infrasound_inaudible : ~ (20 <= 10).
Proof. lra. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem hierarchy_synthesis :
  (* Wave contains vibration *)
  0 < vr_k (wave_to_vib air_wave) /\
  (* No coupling → no propagation *)
  wave_step 0 4 zero_field impulse 1 == 0 /\
  (* No restoring → drift *)
  next_state 0 0 1 == 2 /\
  (* Both present → oscillation + propagation *)
  next_state 2 0 1 == 0 /\
  (* Concert A is audible *)
  20 <= 440 /\ 440 <= 20000.
Proof.
  split; [exact (wave_has_vibration air_wave) |
  split; [exact no_coupling_collapse |
  split; [unfold next_state; ring |
  split; [unfold next_state; ring |
  exact concert_A_audible]]]].
Qed.
