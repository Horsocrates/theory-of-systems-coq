(* ================================================================== *)
(*  ColorSpectrum.v                                                    *)
(*  Color as edge mode number — June 2026 honesty rollback: 4 True-   *)
(*  stubs (color_is_frequency, white_is_all_modes, blackbody,          *)
(*  vision_as_GFT) removed; real layer: mode_frequency_increasing       *)
(*  (color=frequency injective), literal mode_list (white=all modes),  *)
(*  n_edge_modes_monotone (general).  blackbody/vision RETIRED          *)
(*  (no statistics/GFT layer here).                                     *)
(*  STATUS: 8 Qed, 0 Admitted, 0 axioms                                *)
(*  Author: Horsocrates | Date: April 2026 (rollback: June 2026)       *)
(* ================================================================== *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** Number of standing-wave modes on a chain of N vertices.
    A chain of N vertices has N-1 edges, hence N-1 modes. *)
Definition n_edge_modes (N : nat) : nat := (N - 1)%nat.

(** Frequency of mode k on N vertices (in units of base frequency) *)
Definition mode_frequency (k N : nat) : Q :=
  inject_Z (Z.of_nat k) / inject_Z (Z.of_nat N).

(* ------------------------------------------------------------------ *)
(*  Theorems                                                           *)
(* ------------------------------------------------------------------ *)

(** 5 vertices give 4 modes (colors) *)
Theorem five_vertices_four_colors : n_edge_modes 5 = 4%nat.
Proof. reflexivity. Qed.

(** 8 vertices give 7 modes *)
Theorem eight_vertices_seven_colors : n_edge_modes 8 = 7%nat.
Proof. reflexivity. Qed.

(** More vertices => more colors *)
Theorem more_vertices_more_colors :
  (n_edge_modes 5 < n_edge_modes 8)%nat.
Proof. vm_compute. lia. Qed.

(* June 2026 honesty rollback: four True-stubs REMOVED (color_is_frequency,
   white_is_all_modes, blackbody, vision_as_GFT).  blackbody needed statistics/
   temperature and vision_as_GFT needed a GFT layer — neither exists here; those
   claims are RETIRED.  The other two are replaced by real content below. *)

(** ★ "Color = frequency" made real: distinct modes have DISTINCT frequencies —
    the labeling k ↦ k/N is strictly increasing, hence injective. *)
Theorem mode_frequency_increasing : forall (k1 k2 N : nat),
  (0 < N)%nat -> (k1 < k2)%nat ->
  mode_frequency k1 N < mode_frequency k2 N.
Proof.
  intros k1 k2 N HN Hk. unfold mode_frequency, Qdiv.
  apply Qmult_lt_compat_r.
  - apply Qinv_lt_0_compat.
    change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
  - rewrite <- Zlt_Qlt. lia.
Qed.

(** "White = all modes" made real: the literal mode list 1..N−1. *)
Definition mode_list (N : nat) : list nat := seq 1 (n_edge_modes N).

Theorem white_mode_count : forall N, length (mode_list N) = n_edge_modes N.
Proof. intro N. unfold mode_list. apply length_seq. Qed.

Theorem white_contains_every_mode : forall N k : nat,
  (1 <= k)%nat -> (k <= n_edge_modes N)%nat -> In k (mode_list N).
Proof. intros N k H1 H2. unfold mode_list. apply in_seq. lia. Qed.

(** More vertices ⟹ more colors — GENERAL (was only the 5-vs-8 instance). *)
Theorem n_edge_modes_monotone : forall N M : nat,
  (1 <= N)%nat -> (N < M)%nat -> (n_edge_modes N < n_edge_modes M)%nat.
Proof. intros N M H1 H2. unfold n_edge_modes. lia. Qed.

(** === SYNTHESIS === *)
Theorem color_spectrum_synthesis :
  n_edge_modes 5 = 4%nat /\
  n_edge_modes 8 = 7%nat /\
  (n_edge_modes 5 < n_edge_modes 8)%nat /\
  (forall N M : nat, (1 <= N)%nat -> (N < M)%nat ->
     (n_edge_modes N < n_edge_modes M)%nat).
Proof.
  split. { reflexivity. }
  split. { reflexivity. }
  split. { vm_compute. lia. }
  exact n_edge_modes_monotone.
Qed.
