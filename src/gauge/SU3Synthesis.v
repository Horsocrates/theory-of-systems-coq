(** * SU3Synthesis.v -- SU(3) representation theory complete
    Elements: su3_rep_complete
    Roles:    Unify dimensions, Casimirs, gap, partition function
    Rules:    dim(3)=3, dim(8)=8, C₂(3)=4/3, gap(1)=5/6, Z(1)>0
    Status:   Gauge
    STATUS: 5 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import gauge.SU3Representations.
From ToS Require Import gauge.SU3Characters.
From ToS Require Import gauge.SU3Transfer.

Open Scope Q_scope.

(** Phase 1 complete: SU(3) representations, characters, transfer *)

Lemma su3_dimensions_correct :
  su3_dim 1 0 = 3%nat /\ su3_dim 1 1 = 8%nat /\ su3_dim 3 0 = 10%nat.
Proof.
  split; [|split]; reflexivity.
Qed.

Lemma su3_casimirs_correct :
  su3_casimir 1 0 == 4#3 /\ su3_casimir 1 1 == 3.
Proof.
  split; [exact casimir_fund | exact casimir_adjoint].
Qed.

Lemma su3_gap_and_Z :
  gap_su3 1 == 5#6 /\ 0 < Z_su3_approx 1.
Proof.
  split; [exact gap_su3_at_1 | exact Z_su3_positive_1].
Qed.

Theorem su3_rep_complete :
  su3_dim 1 0 = 3%nat /\
  su3_dim 1 1 = 8%nat /\
  su3_casimir 1 0 == 4#3 /\
  gap_su3 1 == 5#6 /\
  0 < Z_su3_approx 1.
Proof.
  split; [|split; [|split; [|split]]].
  - exact dim_fund.
  - exact dim_adjoint.
  - exact casimir_fund.
  - exact gap_su3_at_1.
  - exact Z_su3_positive_1.
Qed.

Theorem su3_phase1_stats :
  su3_dim 0 0 = 1%nat /\
  su3_dim 2 2 = 27%nat /\
  t_fund_su3 1 == 1#6 /\
  t_adj_su3 1 == 1#72.
Proof.
  split; [|split; [|split]].
  - exact dim_trivial.
  - exact dim_27.
  - exact t_fund_at_1.
  - exact t_adj_at_1.
Qed.
