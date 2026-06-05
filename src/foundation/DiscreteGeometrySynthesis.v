(** * DiscreteGeometrySynthesis.v — the CAPSTONE of the causal-set path: order (CausalOrderGeometry.v) +
      number (NumberIsVolume.v) = geometry, with the slogan given its exact QUANTITATIVE form (Malament's
      10 = 9 + 1) and an HONEST map of what is proven vs the conjectural continuum limit (Hauptvermutung).

    -- "order + number = geometry", quantitatively (Malament) --
      A Lorentzian metric in D dimensions has D(D+1)/2 independent components.  The CAUSAL structure (the
      order) determines all but ONE of them — the conformal class (the metric up to a local scale).  The
      VOLUME (the number / counting measure) supplies the missing one — the conformal factor / local
      scale.  Together: conformal (D(D+1)/2 - 1) + volume (1) = metric (D(D+1)/2).  In D = 4: 9 + 1 = 10.
      This is the precise content of Sorkin's slogan and Malament's theorem.

    -- The synthesis bundles the two proven halves --
      This file IMPORTS the two source files (their .vo are current) and bundles their capstones:
        order half  (CausalOrderGeometry): causally_before is a frame-free strict partial order;
        number half (NumberIsVolume):      vol is a finitely-additive measure.
      The record DiscreteGeometry packages both; chain_geometry instantiates it from the proven lemmas.

    -- HONEST map: proven vs conjectural --
      PROVEN here / in the sources: (1) the order is a strict partial order; (2) the number is a
      finitely-additive measure; (3) the DOF decomposition 9 + 1 = 10.  CONJECTURAL (open): that a Poisson
      sprinkling's (order, number) converges to a UNIQUE continuum geometry — the causal-set closeness /
      Hauptvermutung.  We mark it Conjectural and do not pretend otherwise.  10 = 9 + 1 is a DOF count
      (arithmetic + Malament's theorem cited), NOT a derivation of the metric.

    Elements: metric_dof 4 = 10, conformal_dof 4 = 9, volume_dof = 1; the DiscreteGeometry record
    Roles:    order = conformal class (shape); number = scale (volume); together = metric; 3 proven, 1 open
    Rules:    discrete geometry = (order, measure); order + number = geometry as 9 + 1 = 10

    ============ E/R/R разбор ============
      Rules (L5): дискретная геометрия = (ПОРЯДОК, МЕРА); порядок фиксирует конформную структуру (всё, кроме
                  масштаба), число фиксирует масштаб; вместе = метрика.  Количественно: 9 + 1 = 10.
      Roles (L4): порядок (H18) = конформный класс (форма); число (H19) = масштаб (объём); вместе = метрика.
                  Честная карта: 3 доказано (порядок=ч.у., число=мера, 9+1=10), 1 гипотеза (близость, открыта).
      Elements  : metric_dof D := D(D+1)/2; metric_dof 4=10, conformal_dof 4=9, volume_dof=1; запись бандлит
                  chain_irrefl/chain_trans (порядок) + vol_additive (число).
    ДИАГНОСТИКА (P4): капстоун пути.  Слоган «order+number=geometry» получает точную форму 10=9+1 (Маламент:
    каузальная структура = 9 из 10 компонент метрики, объём = 10-я).  Машинно сведены обе половины + честная
    карта (3 доказано vs 1 гипотеза близости, открыта).  P4 держит обе половины конечными/Element.  ЧЕСТНО:
    10=9+1 — разложение DOF (арифметика + цитата Маламента), НЕ вывод метрики; континуумный предел открыт.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia List.
Import ListNotations.
From ToS Require Import foundation.CausalOrderGeometry.
From ToS Require Import foundation.NumberIsVolume.

(* ===================================================================== *)
(*  order + number = geometry, as a DOF count (Malament: 10 = 9 + 1)        *)
(* ===================================================================== *)

(** A symmetric Lorentzian metric in D dimensions has D(D+1)/2 independent components. *)
Definition metric_dof (D : nat) : nat := D * (S D) / 2.

(** The causal (conformal) structure determines all but one — the metric up to a local scale. *)
Definition conformal_dof (D : nat) : nat := metric_dof D - 1.

(** The counting volume supplies the missing one — the conformal factor / local scale. *)
Definition volume_dof : nat := 1.

Lemma metric_dof_4 : metric_dof 4 = 10.
Proof. reflexivity. Qed.

Lemma conformal_dof_4 : conformal_dof 4 = 9.
Proof. reflexivity. Qed.

(** ★ order + number = geometry, as a DOF count: the causal structure fixes 9 of the 10 metric
    components (the conformal class), the counting volume fixes the 10th. *)
Lemma order_plus_number_dof_4 : conformal_dof 4 + volume_dof = metric_dof 4.
Proof. reflexivity. Qed.

(** General D (whenever the metric has at least one component): conformal + volume = metric. *)
Lemma order_plus_number_dof :
  forall D, 1 <= metric_dof D -> conformal_dof D + volume_dof = metric_dof D.
Proof. intros D H. unfold conformal_dof, volume_dof. lia. Qed.

(* ===================================================================== *)
(*  The synthesis: a discrete geometry = (order, measure)                  *)
(* ===================================================================== *)

(** A discrete geometry bundles the two frame-free, Element-side halves:
      the ORDER (a strict partial order = the conformal / causal structure) and
      the NUMBER (a finitely-additive measure = the volume). *)
Record DiscreteGeometry := mkDG {
  dg_order_irrefl : forall x, ~ causally_before x x;
  dg_order_trans  : forall x y z, causally_before x y -> causally_before y z -> causally_before x z;
  dg_vol_additive : forall A B, vol (A ++ B) = vol A + vol B
}.

(** The chain causal set IS a discrete geometry — instantiated directly from the proven lemmas of the
    two source files (CausalOrderGeometry + NumberIsVolume). *)
Definition chain_geometry : DiscreteGeometry :=
  mkDG chain_irrefl chain_trans vol_additive.

(* ===================================================================== *)
(*  Honest map: what is proven vs the conjectural continuum limit          *)
(* ===================================================================== *)

Inductive ClaimStatus := Proven | Conjectural.

Inductive Claim :=
  | OrderIsPartialOrder    (* H18: causal order is a frame-free strict partial order *)
  | NumberIsMeasure        (* H19: the count is a finitely-additive measure *)
  | DofDecomposition       (* 9 + 1 = 10 *)
  | ContinuumLimitUnique.  (* sprinkling -> unique continuum geometry: the Hauptvermutung *)

Definition status (c : Claim) : ClaimStatus :=
  match c with
  | OrderIsPartialOrder  => Proven
  | NumberIsMeasure      => Proven
  | DofDecomposition     => Proven
  | ContinuumLimitUnique => Conjectural
  end.

(** The causal-set closeness / Hauptvermutung is OPEN — marked honestly, not pretended. *)
Lemma hauptvermutung_is_open : status ContinuumLimitUnique = Conjectural.
Proof. reflexivity. Qed.

(** The other three pieces ARE proven (in the two sources and here). *)
Lemma three_pieces_proven :
  status OrderIsPartialOrder = Proven
  /\ status NumberIsMeasure = Proven
  /\ status DofDecomposition = Proven.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the discrete-geometry synthesis                              *)
(* ===================================================================== *)

(** The capstone of the causal-set path:
      (order)   the causal relation is a strict partial order (irreflexive) — the conformal structure;
      (number)  the count is a finitely-additive measure — the volume;
      (= geom)  together they make geometry: 9 (conformal) + 1 (volume) = 10 (metric) in D = 4;
      (honest)  but the continuum limit (the Hauptvermutung) remains conjectural.
    order + number = geometry, made precise and bounded by an honest map of what is and is not proven. *)
Theorem discrete_geometry_synthesis :
  (forall x, ~ causally_before x x)
  /\ (forall A B, vol (A ++ B) = vol A + vol B)
  /\ conformal_dof 4 + volume_dof = metric_dof 4
  /\ status ContinuumLimitUnique = Conjectural.
Proof.
  split; [ exact chain_irrefl | ].
  split; [ exact vol_additive | ].
  split; [ exact order_plus_number_dof_4 | exact hauptvermutung_is_open ].
Qed.
