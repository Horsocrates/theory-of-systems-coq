(** * HiggsDiagnostic.v — fermion-branch synthesis: aggregates Dirac/Yukawa/loops
    Elements: the concrete corrections (top −11/8, gauge +147/110, total +537/1760)
    Roles:    aggregator — restates the branch's key facts in one place
    Rules:    all content imported/recomputed from DiracOnGraph, YukawaCoupling,
              TopLoop, GaugeLoops; nothing new is posited here
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: April 2026  (True-stub honesty rollback: June 2026)

    HONEST STATUS: June 2026 — REMOVED `dirac_spectrum_from_graph : True` and
    `yukawa_from_L2 : True` (stubs).  REPLACED by the real general facts the branch
    now provides: the Dirac gap bound at ALL momenta (eigenvalue_gap_general, re-stated
    here as dirac_gap_at_all_momenta) and the general Yukawa ratio law
    (mass_ratio_is_yukawa_ratio, re-stated as yukawa_ratio_law) — the couplings
    themselves are DATA inputs (see YukawaCoupling.v June-2026 header). *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import fermions.DiracOnGraph.
From ToS Require Import fermions.YukawaCoupling.
From ToS Require Import fermions.TopLoop.
From ToS Require Import fermions.GaugeLoops.

(* ================================================================= *)
(* Theorem 1: Top loop drives mass negative                         *)
(* ================================================================= *)

Theorem top_drives_negative :
  delta_mH_sq 1 (top_loop_sum_4 1) < 0.
Proof.
  unfold delta_mH_sq, N_c, top_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 2: Gauge loops are positive                              *)
(* ================================================================= *)

Theorem gauge_drives_positive :
  delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10)) > 0.
Proof.
  unfold delta_mH_gauge, gauge_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 3: Total correction positive (gauge wins)                *)
(* ================================================================= *)

Theorem total_correction_positive :
  our_delta_total > 0.
Proof.
  unfold our_delta_total, delta_mH_sq, N_c, top_loop_sum_4,
         delta_mH_gauge, gauge_loop_sum_4, delta_mH_self.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 4: Fermion propagator is finite (nonzero eigenvalue)     *)
(* ================================================================= *)

Theorem propagator_finite :
  fermion_propagator_sq 1 4 (1#2) == 16#5.
Proof.
  unfold fermion_propagator_sq, dirac_eigenvalue_sq.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 5: Mass hierarchy from Yukawa                            *)
(* ================================================================= *)

Theorem mass_hierarchy :
  fermion_mass y_bottom 1 / fermion_mass y_top_observed 1 == 1#40.
Proof.
  unfold fermion_mass, y_bottom, y_top_observed.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* June 2026 — the real general facts (replace the removed stubs)    *)
(* ================================================================= *)

(** The Dirac gap holds at ALL momenta (from DiracOnGraph.eigenvalue_gap_general). *)
Theorem dirac_gap_at_all_momenta : forall (k N : nat) (m : Q),
  m * m <= dirac_eigenvalue_sq k N m.
Proof. exact eigenvalue_gap_general. Qed.

(** The Yukawa RATIO law, general (the scale v cancels) — from
    YukawaCoupling.mass_ratio_is_yukawa_ratio; the VALUES stay data inputs. *)
Theorem yukawa_ratio_law : forall y Y v : Q,
  ~ Y == 0 -> ~ v == 0 ->
  fermion_mass y v / fermion_mass Y v == y / Y.
Proof. exact mass_ratio_is_yukawa_ratio. Qed.

(* ================================================================= *)
(* Grand Synthesis                                                   *)
(* ================================================================= *)

Theorem higgs_diagnostic_synthesis :
  (* Dirac: massless zero mode *)
  dirac_eigenvalue_sq 0 4 0 == 0 /\
  (* Dirac: massive gap *)
  dirac_eigenvalue_sq 0 4 (1#2) == 1#4 /\
  (* Yukawa: top dominates *)
  top_dominance > 99#100 /\
  (* Top loop: negative *)
  delta_mH_sq 1 (top_loop_sum_4 1) < 0 /\
  (* Gauge: positive *)
  delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10)) > 0 /\
  (* Total: positive (gauge wins) *)
  our_delta_total > 0 /\
  (* Propagator: finite *)
  fermion_propagator_sq 1 4 (1#2) == 16#5.
Proof.
  unfold dirac_eigenvalue_sq, fermion_propagator_sq,
         top_dominance, y_bottom,
         delta_mH_sq, N_c, top_loop_sum_4,
         delta_mH_gauge, gauge_loop_sum_4,
         delta_mH_self, our_delta_total.
  repeat split; vm_compute; reflexivity.
Qed.
