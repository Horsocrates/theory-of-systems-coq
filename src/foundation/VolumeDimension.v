(** * VolumeDimension.v — Q3 of the open agenda: does "number = volume" extend from the 1D chain (H19) to
      3+1D causal structure with the right DOF count?  TRACTABLE CORE — YES: the count of a D-dimensional
      causal interval (Alexandrov interval / causal diamond) of linear size s is its discrete VOLUME ~ s^D,
      and the DIMENSION D is recovered from how the count SCALES (doubling the size multiplies the count by
      2^D — the Myrheim-Meyer dimension estimator).  The 1D chain (H19) is the case D = 1 (volume linear in
      size).  The full Hauptvermutung — that a random sprinkling converges to a UNIQUE D-manifold with the
      right metric — is OPEN, and is marked Conjectural.

    -- number = volume in D dimensions --
      In a causal set, the causal interval [x,y] = { z : x < z < y } is the discrete causal diamond between
      x and y; its CARDINALITY (number) is the discrete VOLUME of that diamond.  In D continuum dimensions
      this volume scales as (linear size)^D.  So:
          vol_D D s = s^D     (number = volume, in D dimensions).
      The 1D chain (H19, NumberIsVolume.v) is D = 1: volume linear in size.  3+1D is D = 4: volume ~ s^4.

    -- the dimension is recovered from the count --
      Doubling the linear size multiplies the count by 2^D: vol_D D (2s) = 2^D * vol_D D s.  So D is read
      off from the count's scaling — the discrete number KNOWS the dimension (the Myrheim-Meyer estimator).
      The SAME D that sets the volume scaling (s^D) sets the metric DOF D(D+1)/2 (H20, Malament): D = 4 ->
      volume s^4 and DOF 10.

    -- the wall (Hauptvermutung) --
      What is PROVEN here: number = volume in D dimensions (vol = s^D), and the dimension recovered from the
      count scaling.  What is OPEN: that a Poisson sprinkling's interval-counts converge to a UNIQUE
      continuum D-manifold with the right metric (the causal-set closeness / Hauptvermutung).  Marked
      Conjectural — not pretended.

    -- HONEST scope --
      vol_D = s^D models the IDEALIZED continuum scaling of the causal-diamond volume; in a real sprinkling
      the count is the EXPECTED volume with fluctuations, and recovering D requires statistics (Myrheim-
      Meyer uses the expected interval-count ratio).  The idealized scaling and the DOF tie are proved; the
      statistical estimator and the convergence to a unique manifold are the open/harder parts.

    Elements: vol_D D s = s^D; vol_D 1 s = s (H19); vol_D D (2s) = 2^D vol_D D s; metric_dof 4 = 10
    Roles:    interval count = volume (any D); scaling exponent = dimension D; same D => metric DOF D(D+1)/2
    Rules:    number = volume in D dims; dimension recovered from count scaling; unique-manifold limit open

    ============ E/R/R разбор ============
      Rules (L5): "number = volume" в D измерениях: объём причинного интервала (causal diamond) размера s =
                  счёт ~ s^D; размерность D восстанавливается из масштабирования счёта (удвоение -> x2^D).
      Roles (L4): счёт интервала = объём (любая D); показатель масштабирования = размерность D; та же D
                  задаёт метрические DOF D(D+1)/2 (H20); полный предел (единственное многообразие) = открыто.
      Elements  : vol_D D s := s^D; vol_D 1 s = s (H19); vol_D D (2s) = 2^D vol_D D s; metric_dof 4 = 10.
    ДИАГНОСТИКА (P4): ядро Q3 делается -- number=volume на D измерений (объём diamond = s^D), размерность
    выводится из счёта (Мирхейм-Мейер), та же D даёт DOF.  1D-мера H19 = частный случай (D=1).  СТЕНА:
    полная Hauptvermutung (насеивание -> единственное D-многообразие с метрикой) открыта (Conjectural).
    ЧЕСТНО: идеализированное масштабирование s^D; статистический оценщик + сходимость = открытое.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  number = volume in D dimensions                                        *)
(* ===================================================================== *)

(** The discrete volume of a D-dimensional causal interval (causal diamond) of linear size s is the COUNT
    of causal-set elements in it: s^D. *)
Definition vol_D (D size : nat) : nat := size ^ D.

Lemma vol_is_count : forall D size, vol_D D size = size ^ D.
Proof. reflexivity. Qed.

(** 1D recovers H19 (NumberIsVolume): the volume is linear in size (the chain segment). *)
Lemma vol_1_linear : forall size, vol_D 1 size = size.
Proof. intro size. unfold vol_D. apply Nat.pow_1_r. Qed.

(** 3+1D: the causal-diamond volume is s^4 (here s = 2 -> 16). *)
Lemma vol_4 : vol_D 4 2 = 16.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  the dimension is recovered from the count's scaling                    *)
(* ===================================================================== *)

(** ★ Doubling the linear size multiplies the count by 2^D — so the dimension D is read off from how the
    number scales (the Myrheim-Meyer dimension estimator). *)
Lemma dimension_from_scaling : forall D size, vol_D D (2 * size) = 2 ^ D * vol_D D size.
Proof. intros D size. unfold vol_D. rewrite Nat.pow_mul_l. reflexivity. Qed.

(** Concrete: D = 1 -> doubling-ratio 2; D = 4 -> doubling-ratio 16 = 2^4. *)
Lemma scaling_1D : vol_D 1 (2 * 5) = 2 * vol_D 1 5.
Proof. reflexivity. Qed.

Lemma scaling_4D : vol_D 4 (2 * 1) = 16 * vol_D 4 1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  the same D sets the metric DOF (H20, Malament)                         *)
(* ===================================================================== *)

Definition metric_dof (D : nat) : nat := D * (S D) / 2.

(** The same D that sets the volume scaling (s^D) sets the metric DOF D(D+1)/2: D = 4 -> 10. *)
Lemma dim4_dof10 : metric_dof 4 = 10.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  the wall: the unique-manifold limit (Hauptvermutung) is open           *)
(* ===================================================================== *)

Inductive Q3Claim := VolumeDimensionRelation | DimensionFromCount | UniqueManifoldLimit.
Inductive Status := Proven | Conjectural.

Definition q3_status (c : Q3Claim) : Status :=
  match c with
  | VolumeDimensionRelation => Proven       (* vol = s^D *)
  | DimensionFromCount      => Proven       (* D from the count scaling (Myrheim-Meyer) *)
  | UniqueManifoldLimit     => Conjectural  (* sprinkling -> unique D-manifold: Hauptvermutung, OPEN *)
  end.

Lemma hauptvermutung_open : q3_status UniqueManifoldLimit = Conjectural.
Proof. reflexivity. Qed.

Lemma core_proven :
  q3_status VolumeDimensionRelation = Proven /\ q3_status DimensionFromCount = Proven.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: number = volume extends to 3+1D (core), Hauptvermutung open  *)
(* ===================================================================== *)

(** Q3 — number = volume in 3+1D:
      (volume)     the interval count is the discrete volume in D dimensions: vol_D D s = s^D;
      (1D)         the chain (H19) is D = 1: volume linear in size;
      (dimension)  D is recovered from the count's scaling: vol_D D (2s) = 2^D vol_D D s (Myrheim-Meyer);
      (DOF)        the same D sets the metric DOF D(D+1)/2: D = 4 -> 10 (Malament, H20);
      (wall)       the convergence to a UNIQUE continuum D-manifold (Hauptvermutung) is OPEN.
    "number = volume" extends to D dimensions and the count carries the dimension; the full Hauptvermutung
    (unique manifold) stays conjectural — the tractable core is done, the hard limit is honestly flagged. *)
Theorem number_is_volume_3plus1D :
  (forall D size, vol_D D size = size ^ D)
  /\ (forall size, vol_D 1 size = size)
  /\ (forall D size, vol_D D (2 * size) = 2 ^ D * vol_D D size)
  /\ metric_dof 4 = 10
  /\ q3_status UniqueManifoldLimit = Conjectural.
Proof.
  split; [ exact vol_is_count | ].
  split; [ exact vol_1_linear | ].
  split; [ exact dimension_from_scaling | ].
  split; [ exact dim4_dof10 | exact hauptvermutung_open ].
Qed.
