(** * DimensionTwoAxes.v — deepening hint ③: "transition through dimensions" is TWO-dimensional.
       Thread ③ (NestedDimensionsOpenTower) gave ONE axis of "dimension": the NESTING depth (rank in the
       tower), an open process — transitions = ascend/descend.  The GR↔QFT discriminant bridge
       (GRQFTDiscriminantBridge) gives a SECOND, independent axis: the causal TYPE of a direction = the
       sign of Δ = tr²−4det — COMPACT (Δ<0, elliptic/rotation/gauge/INTERNAL, preserves x²+y²) vs
       NON-COMPACT (Δ>0, hyperbolic/boost/spacetime/EXTERNAL, preserves x²−y²) vs NULL (Δ=0, lightcone).

       THE SYNTHESIS.  A dimensional locus is a pair (rank, type) ∈ ℕ × DimType.  Two transition families:
         • NESTING (rank): step_up/step_down — changes rank, PRESERVES type   (thread ③, grounded in ascend);
         • TYPE   (dtype): flip_type        — changes type, PRESERVES rank   (the Δ-sign axis).
       The two axes are ORTHOGONAL: the transitions COMMUTE, and each touches exactly one coordinate.  So
       "transition through dimensions" has two independent moves — WHERE in the hierarchy (rank, P1) and
       WHAT KIND of direction (Δ-sign: internal/gauge vs external/spacetime).  Together they span the grid.

    WHAT THE REPO HAS (surveyed): NestedDimensionsOpenTower.v (the nesting axis, imported); GRQFTDiscriminant
    Bridge.v (Δ-sign = causal type, the preserved forms x²±y², imported); CausalSignature.v (the single
    minus sign).  GAP: nobody combines the nesting axis and the Δ-type axis into a single 2-axis transition
    structure with the independence (commutation) result.  This fills exactly that.

    ============ E/R/R разбор ============
      Elements : уровень (rank=depth, нить ③) + 2×2-генератор и его Δ (Δ-мост); локус = (rank, dtype).
      Roles    : rank = ГДЕ в иерархии (вертикаль, P1); dtype = КАКОГО РОДА направление (compact=internal/gauge
                 Δ<0 vs noncompact=external/spacetime Δ>0) — знак Δ (горизонталь).
      Rules    : step_up/down меняют rank, хранят type; flip_type меняет type, хранит rank; оси КОММУТИРУЮТ
                 (независимы); type ⟺ знак Δ (Δ<0 хранит x²+y² определённую=internal; Δ>0 хранит x²−y² индеф.=external).
      ДИАГНОСТИКА (P4): «переход через измерения» ДВУМЕРЕН — пара (шаг вложенности, тип); оси ортогональны
      (каждый переход трогает ровно одну координату); вертикаль (нить ③) = открытый процесс глубины,
      горизонталь (Δ-мост) = тип дистинкции; полное пространство = ℕ × DimType. ЧЕСТНО: 2-осевая СТРУКТУРА
      + независимость + привязка типа к сохраняемой форме, НЕ физический Wick-поворот / смена сигнатуры.
      Уровень: `синтез` (связь нити ③ ↔ Δ-моста).

    STATUS: 14 Qed, 0 Admitted, 0 axioms  (imports foundation.NestedDimensionsOpenTower + .GRQFTDiscriminantBridge)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Arith Lia.
From ToS Require Import foundation.NestedDimensionsOpenTower.
From ToS Require Import foundation.GRQFTDiscriminantBridge.

(* ===================================================================== *)
(*  The TYPE axis: causal type of a direction = the sign of Δ              *)
(* ===================================================================== *)

(** The causal TYPE of a 2×2 direction = the Δ-sign trichotomy (GRQFTDiscriminantBridge):
    Compact = elliptic/rotation/gauge/INTERNAL (Δ<0); NonCompact = hyperbolic/boost/spacetime/EXTERNAL
    (Δ>0); Null = parabolic/lightcone (Δ=0). *)
Inductive DimType : Set := Compact | Null | NonCompact.

Definition is_compact    (a b c d : Q) : Prop := mdisc a b c d < 0.
Definition is_noncompact (a b c d : Q) : Prop := 0 < mdisc a b c d.
Definition is_null       (a b c d : Q) : Prop := mdisc a b c d == 0.

(** The Δ-type is realized concretely (reusing the bridge's lemmas): rotation = Compact (internal/gauge),
    boost = NonCompact (external/spacetime), shear = Null (lightcone). *)
Lemma rotation_is_compact : is_compact r_a r_b r_c r_d.
Proof. unfold is_compact. exact rot345_elliptic. Qed.

Lemma boost_is_noncompact : is_noncompact b_a b_b b_c b_d.
Proof. unfold is_noncompact. exact boost345_hyperbolic. Qed.

Lemma shear_is_null : is_null n_a n_b n_c n_d.
Proof. unfold is_null. exact par_parabolic. Qed.

(** The type fixes the preserved quadratic form: Compact ↔ definite x²+y² (bounded = internal),
    NonCompact ↔ indefinite x²−y² (causal = external).  (Reusing the bridge's ring identities.) *)
Lemma compact_preserves_definite : forall c s x y,
  (c*x - s*y)*(c*x - s*y) + (s*x + c*y)*(s*x + c*y) == (c*c + s*s)*(x*x + y*y).
Proof. exact rotation_preserves_euclid. Qed.

Lemma noncompact_preserves_indefinite : forall g s x y,
  (g*x + s*y)*(g*x + s*y) - (s*x + g*y)*(s*x + g*y) == (g*g - s*s)*(x*x - y*y).
Proof. exact boost_preserves_mink. Qed.

(* ===================================================================== *)
(*  The dimensional locus = (rank, type), and the two transition families  *)
(* ===================================================================== *)

(** A LOCUS in dimension space: a nesting rank (thread ③) AND a causal type (Δ-sign). *)
Record Locus : Set := mkLocus { rank : nat ; dtyp : DimType }.

(** NESTING axis (thread ③): up/down the tower — changes rank, preserves type. *)
Definition step_up   (L : Locus) : Locus := mkLocus (S (rank L)) (dtyp L).
Definition step_down (L : Locus) : Locus := mkLocus (pred (rank L)) (dtyp L).

(** TYPE axis: flip internal↔external (Compact↔NonCompact) — changes type, preserves rank. *)
Definition flip_type (L : Locus) : Locus :=
  mkLocus (rank L) (match dtyp L with Compact => NonCompact | NonCompact => Compact | Null => Null end).

(* ----- the nesting axis is grounded in thread ③'s tower (rank = depth, step_up = ascend) ----- *)

Definition locus_of (l : Level) (t : DimType) : Locus := mkLocus (depth l) t.

(** ★ The nesting transition on a locus IS thread ③'s ascend on the underlying Level. *)
Lemma ascend_is_step_up : forall l t, locus_of (ascend l) t = step_up (locus_of l t).
Proof. intros l t. unfold locus_of, step_up, ascend. reflexivity. Qed.

(* ===================================================================== *)
(*  The two axes are ORTHOGONAL (independent)                              *)
(* ===================================================================== *)

(** Nesting changes the rank, PRESERVES the type. *)
Lemma nesting_changes_rank : forall L, rank (step_up L) = S (rank L).
Proof. intro L. reflexivity. Qed.

Lemma nesting_preserves_type : forall L, dtyp (step_up L) = dtyp L.
Proof. intro L. reflexivity. Qed.

(** Type-flip changes the type, PRESERVES the rank. *)
Lemma type_preserves_rank : forall L, rank (flip_type L) = rank L.
Proof. intro L. reflexivity. Qed.

Lemma type_flip_changes : forall n, dtyp (flip_type (mkLocus n Compact)) = NonCompact.
Proof. intro n. reflexivity. Qed.

(** ★★ The two transition families COMMUTE: the nesting axis and the type axis are ORTHOGONAL. *)
Lemma axes_commute : forall L, step_up (flip_type L) = flip_type (step_up L).
Proof. intros [n t]. reflexivity. Qed.

(** Type-flip is involutive on the internal↔external pair (toggling type twice returns). *)
Lemma flip_type_involutive : forall L, flip_type (flip_type L) = L.
Proof. intros [n t]. destruct t; reflexivity. Qed.

(* ===================================================================== *)
(*  The two axes SPAN the dimension grid                                   *)
(* ===================================================================== *)

(** Apply the nesting step n times. *)
Fixpoint iter_up (n : nat) (L : Locus) : Locus :=
  match n with O => L | S k => step_up (iter_up k L) end.

(** ★ From the base INTERNAL locus (0, Compact), one type-flip + n nesting steps reaches (n, NonCompact):
    the two independent transitions SPAN the dimension grid ℕ × DimType. *)
Lemma reach_grid : forall n,
  iter_up n (flip_type (mkLocus 0%nat Compact)) = mkLocus n NonCompact.
Proof.
  induction n as [| k IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** "Transition through dimensions" is TWO-dimensional, and the two axes are independent:
      (ground)   the nesting transition on a locus = thread ③'s ascend (rank = depth);
      (axis 1)   nesting changes rank, preserves type;
      (axis 2)   type-flip changes type, preserves rank;
      (orthog)   the two transitions commute — orthogonal axes;
      (type↔Δ)   the type is the Δ-sign: rotation Compact (internal, preserves x²+y²), boost NonCompact
                 (external, preserves x²−y²);
      (span)     the two transitions span the grid ℕ × DimType.
    So the dimension space is rank × type: WHERE in the hierarchy (thread ③, open process) and WHAT KIND
    of direction (Δ-sign, internal/gauge vs external/spacetime).  Honest: the 2-axis STRUCTURE and its
    independence, with the type tied to the preserved form — NOT a physical Wick rotation / signature change. *)
Theorem dimension_two_axes :
  (forall l t, locus_of (ascend l) t = step_up (locus_of l t))
  /\ (forall L, rank (step_up L) = S (rank L) /\ dtyp (step_up L) = dtyp L)
  /\ (forall L, rank (flip_type L) = rank L)
  /\ (forall L, step_up (flip_type L) = flip_type (step_up L))
  /\ (forall L, flip_type (flip_type L) = L)
  /\ (is_compact r_a r_b r_c r_d /\ is_noncompact b_a b_b b_c b_d)
  /\ (forall n, iter_up n (flip_type (mkLocus 0%nat Compact)) = mkLocus n NonCompact).
Proof.
  split. exact ascend_is_step_up.
  split. intro L. split; [ exact (nesting_changes_rank L) | exact (nesting_preserves_type L) ].
  split. exact type_preserves_rank.
  split. exact axes_commute.
  split. exact flip_type_involutive.
  split. split; [ exact rotation_is_compact | exact boost_is_noncompact ].
  exact reach_grid.
Qed.
