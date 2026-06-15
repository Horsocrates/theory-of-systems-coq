(** * ERRGrandTour.v — the theory in action: ONE concrete system through the whole apparatus.

    A capstone DEMONSTRATION (not new abstract theory): the simplest nontrivial E/R/R system — the
    discrete two-element system SDisc (carrier bool, Roles = equality, Rules = equivalence) — exhibited
    through every layer of the core built in this thread, all instantiated and computed concretely.

      object/triad → operator/dynamics → 2-cell → equalizer ∥ coequalizer → image → level tower.

    The H1 signature appears in miniature on this single system: the equalizer of (id, const-true)
    CARVES the Element-side locus {true}; the coequalizer of the same pair MERGES false ~ true at the
    Roles tier; and the level tower over SDisc never completes (P4).

    ============================== E/R/R разбор ==============================
    This file applies the theory to itself on one Element-minimal system.  SDisc's triad: Elements =
    bool (two distinctions), Roles = equality (discrete — rigid), Rules = equivalence.  Its inside-
    operator fconst (collapse to true) has true as equilibrium.  Its 2-cells are rigid (Roles2 =
    equality on the discrete target).  The carve/merge duality (equalizer {true} vs coequalizer
    false~true) and the never-completing level tower are the H1/P4 boundary, in miniature.
    Honesty wall: a demonstration — every lemma instantiates an already-proved result of the core on
    SDisc; nothing new is claimed.  Reuses the whole foundation.ERR* stack.  0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.       (* err_id, err_map, err_morph_eq *)
From ToS Require Import foundation.ERRDynamics.            (* equilibrium *)
From ToS Require Import foundation.ERR2Category.           (* Roles2, Roles2_on_discrete_iff_eq *)
From ToS Require Import foundation.ERREqualizer.           (* fs_equalizer *)
From ToS Require Import foundation.ERRCoequalizer.         (* fs_coequalizer, gc_gen *)
From ToS Require Import foundation.ERRImageFactorization.  (* im_pred, image_fconst_* *)
From ToS Require Import foundation.ERRActualization.       (* fs_lift *)
From ToS Require Import foundation.ERRLevelTower.          (* lvl_iter, no_completed_tower *)
From ToS Require Import foundation.ERRQuotient.            (* SDisc *)
From ToS Require Import foundation.ERRFirstIso.            (* fconst, SDisc_equiv *)

Open Scope nat_scope.

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.

(* ===================================================================== *)
(*  1. The OBJECT — SDisc's triad                                          *)
(* ===================================================================== *)

(** Elements = bool, Roles = equality, Rules = equivalence. *)
Lemma tour_triad :
  get_Elements SDisc = bool
  /\ get_Roles SDisc = @eq bool
  /\ fs_constitution SDisc = EquivalenceConstitution.
Proof. split; [ reflexivity | split; [ reflexivity | exact SDisc_equiv ] ]. Qed.

(* ===================================================================== *)
(*  2. The OPERATOR — fconst as an inside-operator with an equilibrium     *)
(* ===================================================================== *)

(** fconst (collapse to true) has `true` as a fixed point. *)
Lemma tour_equilibrium : equilibrium fconst true.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  3. The 2-CELL — rigid (Roles2 on the discrete target = equality)       *)
(* ===================================================================== *)

(** On the discrete SDisc the 2-structure is rigid: id and const-true are NOT joined by a 2-cell. *)
Lemma tour_2cell_rigid : ~ Roles2 (err_id SDisc) fconst.
Proof.
  intro H. apply (Roles2_on_discrete_iff_eq SDisc) in H.
  specialize (H false). discriminate H.
Qed.

(* ===================================================================== *)
(*  4. The CARVE/MERGE DUALITY — equalizer vs coequalizer (H1 in miniature)*)
(* ===================================================================== *)

(** The EQUALIZER of (id, const-true) CARVES the agreement locus {true} (Element side). *)
Lemma tour_equalizer_carrier :
  get_Elements (fs_equalizer SDisc_equiv (err_id SDisc) fconst)
    = { x : bool | err_map (err_id SDisc) x = err_map fconst x }.
Proof. reflexivity. Qed.

(** The COEQUALIZER of the SAME pair MERGES false ~ true (Roles side). *)
Lemma tour_coequalizer_merges :
  get_Roles (fs_coequalizer (err_id SDisc) fconst) false true.
Proof. exact (gc_gen (err_id SDisc) fconst false). Qed.

(* ===================================================================== *)
(*  5. The IMAGE — of the collapse is exactly {true}                       *)
(* ===================================================================== *)

Lemma tour_image : im_pred fconst true /\ ~ im_pred fconst false.
Proof. split; [ exact image_fconst_true | exact image_fconst_not_false ]. Qed.

(* ===================================================================== *)
(*  6. The LEVEL TOWER — SDisc lifts (same carrier), never completes (P4)  *)
(* ===================================================================== *)

(** The lift preserves SDisc's carrier. *)
Lemma tour_lift_carrier : get_Elements (fs_lift SDisc) = bool.
Proof. reflexivity. Qed.

(** The tower over SDisc's level never completes — no bounding level (P4). *)
Lemma tour_tower_no_completion :
  ~ exists M : Level, forall n, level_depth (lvl_iter n L2) <= level_depth M.
Proof. exact (@no_completed_tower L2). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE THEORY IN ACTION ON ONE SYSTEM.
    SDisc (bool, discrete) seen through the whole core:
      object (triad) · operator (fconst, equilibrium true) · 2-cell (rigid) ·
      equalizer {true} ∥ coequalizer false~true (the H1 carve/merge duality) ·
      image {true} · level tower (same carrier, never completes = P4).
    Every clause instantiates an already-proved result of the core; the demonstration shows the
    finitization boundary (H1) and the no-completed-tower (P4) emerging on the simplest system. *)
Theorem err_grand_tour :
  (get_Elements SDisc = bool /\ get_Roles SDisc = @eq bool
     /\ fs_constitution SDisc = EquivalenceConstitution)
  /\ equilibrium fconst true
  /\ ~ Roles2 (err_id SDisc) fconst
  /\ get_Elements (fs_equalizer SDisc_equiv (err_id SDisc) fconst)
       = { x : bool | err_map (err_id SDisc) x = err_map fconst x }
  /\ get_Roles (fs_coequalizer (err_id SDisc) fconst) false true
  /\ (im_pred fconst true /\ ~ im_pred fconst false)
  /\ get_Elements (fs_lift SDisc) = bool
  /\ ~ exists M : Level, forall n, level_depth (lvl_iter n L2) <= level_depth M.
Proof.
  split; [ exact tour_triad | ].
  split; [ exact tour_equilibrium | ].
  split; [ exact tour_2cell_rigid | ].
  split; [ exact tour_equalizer_carrier | ].
  split; [ exact tour_coequalizer_merges | ].
  split; [ exact tour_image | ].
  split; [ exact tour_lift_carrier | exact tour_tower_no_completion ].
Qed.

Print Assumptions err_grand_tour.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The theory in action: the discrete two-element system SDisc through every  *)
(*  layer of the core.  tour_triad (object) · tour_equilibrium (operator) ·   *)
(*  tour_2cell_rigid (2-cell) · tour_equalizer_carrier ∥ tour_coequalizer_     *)
(*  merges (the H1 carve/merge duality on one pair) · tour_image · tour_lift_  *)
(*  carrier + tour_tower_no_completion (P4).  Capstone err_grand_tour.  A      *)
(*  demonstration — every clause instantiates an already-proved core result;   *)
(*  H1 (carve {true} vs merge false~true) and P4 (no completed tower) emerge   *)
(*  on the simplest system.                                                   *)
(* ========================================================================= *)
