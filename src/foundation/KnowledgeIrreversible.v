(** * KnowledgeIrreversible.v — Теория Знания: the DUAL of the distillate thesis — the distillation
      присутствие+как -> знание-о is IRREVERSIBLE.  Знание-о recovers NEITHER присутствие nor как:
      the map has NO section.  (Ryle's regress: знание-как is not reducible to a stock of знание-о.)

    KnowledgeSourceOrder.v proved знание-о (KThat) is a LOSSY distillate, sourced from присутствие
    (KPresence) + как (KHow).  This file proves the companion: that loss is IRREVERSIBLE — you cannot
    reconstitute the encounter or the ability from the proposition.  Two underdeterminations + a
    no-section theorem, all over the existing ladder (read_content).

      (A) ПРИСУТСТВИЕ NOT RECOVERABLE — the distillation is NOT injective in the encounter: DIFFERENT
          encounters yield the SAME distillate (a deep distinction a shallow witness cannot read is
          invisible in the proposition).  Hence NO SECTION: there is no inverse s with
          s (read_content w data) = data.  The meeting is not reconstitutable from знание-о.

      (B) КАК NOT REDUCIBLE TO О (Ryle) — знание-как is an OPERATION (read_content w : Data -> ...,
          defined on ALL encounters = an ability/disposition); знание-о is its VALUE at ONE encounter.
          A value does not fix the operation: two different hows agree at one encounter (same знание-о)
          yet diverge at another.  So knowing-that cannot BE knowing-how — the regress.

    Together with the lossiness (KnowledgeSourceOrder.that_is_distillate): the distillate is a strictly
    ONE-WAY reduction — reachable from the encounter, never back.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) the distillation присутствие+как -> знание-о has NO section (no inverse);
      (2) знание-о does not recover присутствие (different encounters collapse to one distillate);
      (3) знание-о does not recover как (one distillate is produced by different abilities) — Ryle.
    Roles (L4): read_content = the distillation; its non-injectivity (in the encounter / in the
      witness) = the irreversibility; the (non-existent) section s = the would-be inverse; the
      diverge-elsewhere witness = the ability exceeding the proposition.
    Elements (L1+P4): encounters (data); witnesses/depths (hows); the distillate; the collision
      witnesses.
    P4 diagnostic (could it be otherwise?):
      no — the distillation FORCED-ly collapses (a depth-0 witness cannot tell an empty encounter from
      one bearing a deep distinction), so no inverse can exist (one distillate, two pre-images).
      знание-как is an OPERATION (a whole function on all encounters), знание-о a VALUE (one point); a
      value cannot force the operation.  Reconstruction is impossible in principle, not merely
      unperformed — the formal shadow of Ryle's regress.
    Honesty wall:
      "irreversible" = no section / non-injective (a structural impossibility-of-inverse), not the
      phenomenology of acquaintance or skill.  Shown for a concrete lossy how (depth 0); whenever the
      how loses anything, no section exists.  Builds on KnowledgeInformation + KnowledgeSourceOrder.
      0 axioms.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From ToS Require Import foundation.KnowledgeInformation.  (* Distinction, Data, Witness, read_content *)
From ToS Require Import foundation.KnowledgeSourceOrder.  (* that_is_distillate (the lossiness) *)

(* ===================================================================== *)
(*  (A) ПРИСУТСТВИЕ NOT RECOVERABLE — non-injective, no section            *)
(* ===================================================================== *)

(** ★★ Присутствие is UNDERDETERMINED by знание-о: two DIFFERENT encounters (empty vs one bearing a
    depth-1 distinction) yield the SAME distillate for a depth-0 witness — the deep distinction is
    invisible in the proposition.  The encounter cannot be read off the знание-о. *)
Lemma presence_underdetermined_by_that :
  exists (data1 data2 : Data) (w : Witness),
    data1 <> data2 /\ read_content w data1 = read_content w data2.
Proof.
  exists [], [ mkDist 0 1 0 ], (mkWit 0 0).
  split; [ discriminate | reflexivity ].
Qed.

(** ★★★ NO SECTION: there is no inverse s reconstituting the encounter from its distillate.  Any such
    s would have to send the single shared distillate to BOTH pre-encounters — impossible.  The
    direct meeting is not recoverable from знание-о. *)
Lemma no_section_for_distillation :
  ~ exists s : list Distinction -> Data, forall data, s (read_content (mkWit 0 0) data) = data.
Proof.
  intros [s Hs].
  assert (E : read_content (mkWit 0 0) [] = read_content (mkWit 0 0) [ mkDist 0 1 0 ]) by reflexivity.
  pose proof (Hs []) as H1.
  pose proof (Hs [ mkDist 0 1 0 ]) as H2.
  rewrite <- E in H2. rewrite H1 in H2. discriminate H2.
Qed.

(* ===================================================================== *)
(*  (B) КАК NOT REDUCIBLE TO О — Ryle's regress (operation vs value)       *)
(* ===================================================================== *)

(** ★★ КАК is UNDERDETERMINED by знание-о: two different hows (depth-1 vs depth-2 witnesses) AGREE on
    the empty encounter (same знание-о = []) yet DIVERGE on a depth-2 encounter.  знание-как is the
    whole operation (defined on every encounter); знание-о is its value at one — the value does not
    fix the operation.  Knowing-that cannot BE knowing-how (Ryle). *)
Lemma how_underdetermined_by_that :
  exists (w1 w2 : Witness) (data : Data),
    read_content w1 data = read_content w2 data
    /\ exists data', read_content w1 data' <> read_content w2 data'.
Proof.
  exists (mkWit 0 1), (mkWit 1 2), [].
  split.
  - reflexivity.
  - exists [ mkDist 0 2 0 ]. unfold read_content. simpl. discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the distillate is one-way (lossy AND irreversible)          *)
(* ===================================================================== *)

(** ★★★ THE DISTILLATION IS IRREVERSIBLE (and lossy): знание-о recovers neither присутствие (different
    encounters collapse to one distillate; no section) nor как (one distillate, different abilities —
    Ryle), and it is generically thinner than the encounter (KnowledgeSourceOrder).  The distillate
    присутствие+как -> знание-о is a strictly ONE-WAY reduction — reachable, never reversible. *)
Theorem distillation_is_irreversible :
  (exists (data1 data2 : Data) (w : Witness),
     data1 <> data2 /\ read_content w data1 = read_content w data2)
  /\ (~ exists s : list Distinction -> Data, forall data, s (read_content (mkWit 0 0) data) = data)
  /\ (exists (w1 w2 : Witness) (data : Data),
        read_content w1 data = read_content w2 data
        /\ exists data', read_content w1 data' <> read_content w2 data')
  /\ (exists (data : Data) (w : Witness), length (read_content w data) < length data).
Proof.
  split; [ exact presence_underdetermined_by_that | ].
  split; [ exact no_section_for_distillation | ].
  split; [ exact how_underdetermined_by_that | exact that_is_distillate ].
Qed.

Print Assumptions distillation_is_irreversible.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  4 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The DUAL of the distillate thesis: the distillation присутствие+как ->     *)
(*  знание-о is IRREVERSIBLE.  (A) presence_underdetermined_by_that (different *)
(*  encounters, same distillate) + no_section_for_distillation (no inverse —   *)
(*  the meeting is not reconstitutable from знание-о).  (B)                     *)
(*  how_underdetermined_by_that (same знание-о, different abilities diverging   *)
(*  elsewhere — знание-как is an operation, знание-о its value; Ryle's regress).*)
(*  Capstone distillation_is_irreversible bundles both with the lossiness      *)
(*  (that_is_distillate, KnowledgeSourceOrder): the distillate is strictly     *)
(*  ONE-WAY.  Builds on KnowledgeInformation + KnowledgeSourceOrder.  HONEST:   *)
(*  no-section / non-injectivity (structural), not the phenomenology of skill   *)
(*  or acquaintance.                                                          *)
(* ========================================================================= *)
