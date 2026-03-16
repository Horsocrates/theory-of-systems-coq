(** * ProcessFermion3D.v - 3+1D Fermion Hopping and 16 Doublers

    Theory of Systems - Phase 35: 3+1D Fermion Doubling (File 1)

    Elements: BZCorner, all_corners, wilson_mass_3plus1
    Roles:    Brillouin zone corners, dispersion, Wilson mass in 3+1D
    Rules:    2^D corners, origin light, doublers heavy with Wilson term
    Status:   complete

    In D dimensions: the Brillouin zone has 2^D corners.
    Each corner is a minimum of the dispersion -> a "species."
    In 3+1D: 16 corners -> 16 naive fermion species.

    STATUS: 16 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessFermionSpectrum.
From ToS Require Import process.ProcessFermionDoubling.

(* ================================================================== *)
(*  Part I: D-dimensional Brillouin Zone  (~8 lemmas)                 *)
(* ================================================================== *)

(** A corner of the Brillouin zone: vector of {0,pi} in D dimensions *)
(** true = pi, false = 0 *)
Fixpoint all_corners (D : nat) : list (list bool) :=
  match D with
  | 0%nat => [[]]
  | S d => map (cons false) (all_corners d) ++
           map (cons true) (all_corners d)
  end.

(** 2^D corners *)
Lemma n_corners : forall D, length (all_corners D) = Nat.pow 2 D.
Proof.
  induction D as [|d IH].
  - simpl. reflexivity.
  - simpl. rewrite length_app. rewrite !length_map. rewrite IH.
    lia.
Qed.

(** Concrete counts *)
Lemma corners_1D : length (all_corners 1) = 2%nat.
Proof. simpl. reflexivity. Qed.

Lemma corners_2D : length (all_corners 2) = 4%nat.
Proof. simpl. reflexivity. Qed.

Lemma corners_3D : length (all_corners 3) = 8%nat.
Proof. simpl. reflexivity. Qed.

Lemma corners_4D : length (all_corners 4) = 16%nat.
Proof. simpl. reflexivity. Qed.

(** Consistency with doublers_in_D from Phase 30 *)
Lemma corners_match_doublers : forall D,
  length (all_corners D) = doublers_in_D D.
Proof.
  intros D. rewrite n_corners. unfold doublers_in_D. reflexivity.
Qed.

(* ================================================================== *)
(*  Part II: Counting pi-directions  (~4 lemmas)                     *)
(* ================================================================== *)

(** Number of pi-directions at a corner *)
Definition n_pi_dirs (corner : list bool) : nat :=
  length (filter (fun b => b) corner).

(** Origin: 0 pi-directions *)
Lemma origin_n_pi : n_pi_dirs [false; false; false; false] = 0%nat.
Proof. unfold n_pi_dirs. simpl. reflexivity. Qed.

(** All-pi corner: 4 pi-directions *)
Lemma allpi_n_pi : n_pi_dirs [true; true; true; true] = 4%nat.
Proof. unfold n_pi_dirs. simpl. reflexivity. Qed.

(** Single-pi corner: 1 pi-direction *)
Lemma singlepi_n_pi : n_pi_dirs [true; false; false; false] = 1%nat.
Proof. unfold n_pi_dirs. simpl. reflexivity. Qed.

(** Two-pi corner: 2 pi-directions *)
Lemma twopi_n_pi : n_pi_dirs [true; true; false; false] = 2%nat.
Proof. unfold n_pi_dirs. simpl. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Wilson Fermions in 3+1D  (~6 lemmas)                    *)
(* ================================================================== *)

(** Wilson mass correction in 3+1D *)
(** Mass correction = 2r per pi-direction *)
Definition wilson_mass_3plus1 (r : Q) (corner : list bool) : Q :=
  r * inject_Z (Z.of_nat (2 * n_pi_dirs corner)).

(** Physical mode (origin): no Wilson mass *)
Lemma wilson_origin_mass :
  wilson_mass_3plus1 1 [false; false; false; false] == 0.
Proof.
  unfold wilson_mass_3plus1, n_pi_dirs. simpl. ring.
Qed.

(** Worst doubler (all pi): maximum Wilson mass *)
Lemma wilson_allpi_mass :
  wilson_mass_3plus1 1 [true; true; true; true] == 8.
Proof.
  unfold wilson_mass_3plus1, n_pi_dirs. simpl. ring.
Qed.

(** Single-pi doubler: mass = 2 *)
Lemma wilson_singlepi_mass :
  wilson_mass_3plus1 1 [true; false; false; false] == 2.
Proof.
  unfold wilson_mass_3plus1, n_pi_dirs. simpl. ring.
Qed.

(** Two-pi doubler: mass = 4 *)
Lemma wilson_twopi_mass :
  wilson_mass_3plus1 1 [true; true; false; false] == 4.
Proof.
  unfold wilson_mass_3plus1, n_pi_dirs. simpl. ring.
Qed.

(** All 15 doublers get mass >= 2r (any non-origin corner has >= 1 pi) *)
Lemma wilson_doubler_heavy : forall corner,
  (1 <= n_pi_dirs corner)%nat ->
  2 <= wilson_mass_3plus1 1 corner.
Proof.
  intros corner Hge. unfold wilson_mass_3plus1.
  assert (H : (2 <= 2 * n_pi_dirs corner)%nat) by lia.
  assert (Hinj : 2 <= inject_Z (Z.of_nat (2 * n_pi_dirs corner))).
  { unfold Qle, inject_Z. simpl. lia. }
  lra.
Qed.

Theorem fermion_3d_complete :
  (* 3+1D lattice: 2^4 = 16 Brillouin zone corners *)
  (* Each corner = massless fermion species *)
  (* Wilson term: physical mode (origin) stays light *)
  (* All 15 doublers get mass >= 2r *)
  length (all_corners 4) = 16%nat /\
  wilson_mass_3plus1 1 [false; false; false; false] == 0 /\
  wilson_mass_3plus1 1 [true; true; true; true] == 8.
Proof.
  split; [apply corners_4D|].
  split; [apply wilson_origin_mass|].
  apply wilson_allpi_mass.
Qed.
