(** * DimensionFromSpin.v — d=3 as the INTERSECTION of two POSITED bounds — honest rollback
       of the old header "d=3 is the UNIQUE dimension": the bounds are inputs, not theorems
    Elements: spin1_dim, spatial_dim, spacetime_dim, force_exponent, n_metric, sin2
    Roles:    L5 (stability ordering) → the bounds; d=3 — the intersection point
    Rules:    stable_orbits (force exponent < 3) genuinely yields d ≤ 3 (stable_iff_le3);
              the spin-1 lower bound min_d_for_spin1 = 3 is a BARE POSIT (no model here);
              "uniqueness" = 3 ≤ d ≤ 3 (unique_given_bounds) — real but conditional
    STATUS:   18 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026  (uniqueness-honesty rollback: June 2026)

    +-- HONEST STATUS (rolled back from "d=3 is the UNIQUE dimension...") ------------------+
    | The file pins d = 3 as the intersection of TWO bounds:                                 |
    |   (1) spin-1 needs d ≥ 3 — encoded as the bare constant min_d_for_spin1 := 3.          |
    |       NO model derives it here (the SO(d)-representation argument is cited prose,      |
    |       not Coq) — a POSIT.                                                               |
    |   (2) stable orbits need d ≤ 3 — the model stable_orbits (F ∝ 1/r^{d−1}, exponent < 3) |
    |       genuinely yields the bound for ALL d (stable_iff_le3) — derived GIVEN the model. |
    | GIVEN both bounds, uniqueness is real but trivial: 3 ≤ d ≤ 3 (unique_given_bounds).    |
    | It LIVES IN the posits: weakening the lower bound by ONE already admits d = 2          |
    | (uniqueness_lives_in_the_posits).  The sin²θ_W column below inherits the 3/13 chain's  |
    | own counted posits (see WeinbergAngleDerivation / MetricDOFJustification).             |
    +-----------------------------------------------------------------------------------------+

    ============ E/R/R разбор ============
      Elements : кандидаты-размерности d; границы — min=3 (голый постулат) и max=3 (из
                 модели орбит F ∝ 1/r^{d−1}).
      Roles    : d=3 — роль «точка пересечения границ»; sin²(d) — наследует роль 3/13-цепи.
      Rules    : stable_orbits ⟹ d ≤ 3 — выведено ПРИ модели (stable_iff_le3); нижняя
                 граница — постулат без модели; единственность = 3 ≤ d ≤ 3 (условная).
      ДИАГНОСТИКА (P4): «UNIQUE» снято: единственность реальна только при двух названных
      входах и тривиальна как пересечение; ослабь нижний постулат на 1 — интервал держит
      d=2 (могло-быть-иначе показано теоремой uniqueness_lives_in_the_posits). Узел:
      forced(пересечение) ⟂ posit(нижняя граница) ⟂ model(верхняя). Уровень: `новое-обрамление`.

    sin²θ_W at candidate dimensions (the 3/13 chain's own posits apply):
    — d=2: n_metric=6, sin²=1/3 — d=4: n_metric=15, sin²=1/6 — d=3: n_metric=10, sin²=3/13
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.

(** ** Core definitions *)

Definition spin1_dim : nat := 3%nat.
Definition min_d_for_spin1 : nat := 3%nat.
Definition max_d_for_stability : nat := 3%nat.
Definition spatial_dim : nat := 3%nat.
Definition spacetime_dim : nat := 4%nat.
Definition n_metric_derived : nat := (spacetime_dim * (spacetime_dim + 1) / 2)%nat.

(* Force exponent in d spatial dims: F ∝ 1/r^{d-1} *)
Definition force_exponent (d : nat) : nat := (d - 1)%nat.

(* Stability: exponent < 3 needed *)
Definition stable_orbits (d : nat) : bool := (force_exponent d <? 3)%nat.

(* Metric DOF at spatial dimension d: D(D+1)/2 where D = d+1 *)
Definition n_metric_at_d (d : nat) : nat :=
  let D := (d + 1)%nat in (D * (D + 1) / 2)%nat.

Open Scope Q_scope.

(* sin²θ_W prediction at spatial dimension d *)
Definition sin2_at_d (d : nat) : Q :=
  inject_Z (Z.of_nat 3%nat) / inject_Z (Z.of_nat (3 + n_metric_at_d d)%nat).

(** ** Dimension constraints *)

Lemma spin1_needs_3 : min_d_for_spin1 = 3%nat.
Proof. reflexivity. Qed.

Lemma stability_needs_le3 : max_d_for_stability = 3%nat.
Proof. reflexivity. Qed.

Lemma d_is_3 : spatial_dim = 3%nat.
Proof. reflexivity. Qed.

Lemma D_is_4 : spacetime_dim = 4%nat.
Proof. reflexivity. Qed.

Lemma n_metric_is_10 : n_metric_derived = 10%nat.
Proof. reflexivity. Qed.

(** ** Force law and orbital stability *)

Lemma force_exp_d3 : force_exponent 3%nat = 2%nat.
Proof. reflexivity. Qed.

Lemma force_exp_d4 : force_exponent 4%nat = 3%nat.
Proof. reflexivity. Qed.

Lemma stable_d3 : stable_orbits 3%nat = true.
Proof. reflexivity. Qed.

Lemma stable_d4 : stable_orbits 4%nat = false.
Proof. reflexivity. Qed.

(** ** Wrong dimensions *)

Lemma wrong_d2 : n_metric_at_d 2%nat = 6%nat /\ sin2_at_d 2%nat == 1#3.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma wrong_d4 : n_metric_at_d 4%nat = 15%nat /\ sin2_at_d 4%nat == 1#6.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

(** ** Correct dimension *)

Lemma correct_d3 : n_metric_at_d 3%nat = 10%nat /\ sin2_at_d 3%nat == 3#13.
Proof.
  split.
  - reflexivity.
  - vm_compute. reflexivity.
Qed.

(** ** Synthesis: the consistency record at d=3
    (renamed June 2026 from dimension_uniquely_determined — the statement was and is a
     conjunction of consistency facts at d=3, NOT a uniqueness proof; see the honest
     core below for where uniqueness actually lives) *)

Lemma dimension_consistency_record :
  spatial_dim = 3%nat /\
  min_d_for_spin1 = 3%nat /\
  max_d_for_stability = 3%nat /\
  n_metric_at_d 3%nat = 10%nat /\
  sin2_at_d 3%nat == 3#13.
Proof.
  repeat split; try reflexivity; vm_compute; reflexivity.
Qed.

(** ** Stability excludes d>=4 *)

Lemma stability_excludes_d4_and_above :
  stable_orbits 4%nat = false /\ stable_orbits 5%nat = false.
Proof. split; reflexivity. Qed.

(** ** Both constraints agree on d=3 *)

Lemma constraints_agree :
  (min_d_for_spin1 <= spatial_dim)%nat /\
  (spatial_dim <= max_d_for_stability)%nat /\
  stable_orbits spatial_dim = true.
Proof. repeat split; try lia; reflexivity. Qed.

(** ** Honest core (June 2026 rollback): where the uniqueness actually lives *)

(** The stability MODEL genuinely yields the upper bound for ALL d:
    stable ⟺ d ≤ 3 — this half is derived (given the F ∝ 1/r^{d−1} model). *)
Lemma stable_iff_le3 : forall d, stable_orbits d = true <-> (d <= 3)%nat.
Proof.
  intro d. unfold stable_orbits, force_exponent.
  rewrite Nat.ltb_lt. split; intro; lia.
Qed.

(** ★ GIVEN the two posited bounds, d=3 is the unique value in the interval —
    real uniqueness, but CONDITIONAL on the posits (the interval is 3 ≤ d ≤ 3). *)
Lemma unique_given_bounds : forall d,
  (min_d_for_spin1 <= d)%nat /\ (d <= max_d_for_stability)%nat <-> d = 3%nat.
Proof.
  intro d. unfold min_d_for_spin1, max_d_for_stability. split; intro H; lia.
Qed.

(** ★ The uniqueness LIVES IN the posits, not in the framework: weaken the lower
    bound by ONE (min = 2 instead of 3) and the interval already holds a second
    value — the "could it be otherwise" witness. *)
Lemma uniqueness_lives_in_the_posits :
  exists d, (2 <= d)%nat /\ (d <= max_d_for_stability)%nat /\ d <> 3%nat.
Proof.
  exists 2%nat. unfold max_d_for_stability. repeat split; lia.
Qed.
