(** * SU3ObservablesSynthesis.v -- SU(3) observables complete
    Elements: su3_observables_complete
    Roles:    Unify gap, string tension, glueball, partition function
    Rules:    All exact Q, strong coupling, machine-checked
    Status:   Gauge
    STATUS: 6 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Representations.
From ToS Require Import gauge.SU3Transfer.
From ToS Require Import gauge.SU3StringTension.
From ToS Require Import gauge.SU3Glueball.

Open Scope Q_scope.

(** ★★★ SU(3) OBSERVABLES COMPLETE ★★★

    COMPARISON WITH QCD LATTICE DATA:

    Observable         ToS (exact Q)       QCD MC        Status
    ──────────────────────────────────────────────────────────
    gap(β=1)          5/6 ≈ 0.833         —             strong coupling
    Z(β=1)            44/9 ≈ 4.89         —             strong coupling
    σ(β=6)            2/3                  0.044 a²      strong ≠ continuum
    glueball          5/6 (lattice units)  1730 MeV      needs continuum limit
    mass ratio        71/60 ≈ 1.18        ~1.39          qualitative agreement

    HONEST: all results are at STRONG COUPLING.
    Physical QCD is at WEAK coupling (β ≈ 6).

    WHAT IS GENUINELY NEW:
    - SU(3) character expansion EXACT over Q
    - Dimensions, Casimirs, partition function all machine-checked
    - Gap > 0 PROVED (not just computed) for β < 6
    - First SU(3) lattice gauge theory in Rocq *)

Lemma observables_gap : gap_su3 1 == 5#6 /\ 0 < gap_su3 1.
Proof.
  split; [exact gap_su3_at_1 | exact gap_su3_positive_1].
Qed.

Lemma observables_sigma :
  sigma_su3_strong 6 == 2#3 /\ 0 < sigma_su3_strong 6.
Proof.
  split; [exact sigma_su3_at_6 | exact sigma_positive_6].
Qed.

Lemma observables_glueball :
  glueball_mass_su3 1 == 5#6 /\ 1 < mass_ratio_su3 1.
Proof.
  split; [exact glueball_at_1 | exact mass_ratio_gt_1].
Qed.

Theorem su3_observables_complete :
  su3_dim 1 0 = 3%nat /\
  su3_dim 1 1 = 8%nat /\
  gap_su3 1 == 5#6 /\
  sigma_su3_strong 6 == 2#3 /\
  0 < Z_su3_approx 1.
Proof.
  split; [|split; [|split; [|split]]].
  - exact dim_fund.
  - exact dim_adjoint.
  - exact gap_su3_at_1.
  - exact sigma_su3_at_6.
  - exact Z_su3_positive_1.
Qed.

Theorem su3_mass_hierarchy :
  glueball_mass_su3 1 < glueball_mass_su3 0 /\
  glueball_mass_su3 3 < glueball_mass_su3 1.
Proof.
  split; [exact glueball_decreases_01 | exact glueball_decreases].
Qed.

Theorem phase3_complete :
  gap_su3 1 == 5#6 /\
  sigma_su3_strong 6 == 2#3 /\
  mass_ratio_su3 1 == 71#60.
Proof.
  split; [|split].
  - exact gap_su3_at_1.
  - exact sigma_su3_at_6.
  - exact mass_ratio_at_1_value.
Qed.
