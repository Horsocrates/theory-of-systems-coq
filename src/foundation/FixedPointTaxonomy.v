(** * FixedPointTaxonomy.v — the Lipschitz ratio CLASSIFIES three structurally opposite "fixed-point"
       phenomena the repo treats in separate threads: contraction (r<1 → convergence), isometry (r=1 →
       symmetry/oscillation, RH's reflection), and the negb-diagonal (no fixed point → paradox/
       undecidability). One classifier ties vein C (convergence), the zeta reflection, and vein E (Lawvere).

    THE OBSERVATION (a candidate 10th thread / cross-vein taxonomy).
    The single word "fixed point" covers THREE structurally OPPOSITE phenomena in the repo, each in a
    different thread, distinguished by the Lipschitz ratio r of the map (and the negb anti-flip):

      (1) CONTRACTION  r < 1  (`half_map x = x/2`, ratio 1/2): a UNIQUE ATTRACTING fixed point; iteration
          converges geometrically. This is the convergence ENGINE — `FixedPoint.v` (Banach), `PicardLindelof`
          (ODEs), `GradientDescent`, `ReasoningConvergence`, and the RG flow to a fixed point
          (process/gauge RG → continuum limit / universality). Vein C.

      (2) ISOMETRY  r = 1  (`reflect x = 1−x`, the zeta functional-equation reflection): a fixed point
          (1/2 = the critical line) that is NOT attracting — iteration OSCILLATES (period 2), and no r<1
          bounds it. This is RH's reflection (`zeta/ContractionZeros.v` `reflect_not_contraction`).

      (3) DIAGONAL  the negb anti-flip (`negb b ≠ b`): NO fixed point — the Lawvere/Cantor diagonal seed
          that produces uncountability / halting / paradox / undecidability (`cs/LawvereFixedPoint.v`,
          `Roles.v`, `settheory/CantorTheoremGeneral.v`). Vein E.

    So the Lipschitz ratio r is a CLASSIFIER: r<1 → convergence (a point you reach), r=1 → symmetry (a
    point you orbit), and the negb-flip → undecidability (a point that cannot exist). The repo's
    convergence engine, RH's reflection, and the Lawvere diagonal are the three faces of one taxonomy.

    WHAT IS NEW / HONEST SCALE.
    Each type is classical: Banach's contraction (r<1 → unique fixed point), isometries (r=1), and
    Lawvere/Cantor's diagonal (no fixed point). NEW (synthesis+observation, machine-checked): the
    unification under ONE classifier (the Lipschitz ratio / negb anti-flip) tying three of the repo's
    own threads (vein C convergence, the zeta reflection, vein E diagonal). This is a META-observation
    spanning veins C/E + zeta — more a cross-vein taxonomy than a fully independent vein. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : три отображения — half_map x=x/2 (сжатие r=1/2), reflect x=1−x (изометрия r=1), negb
                 (диагональ); липшицевы отношения r; неподвижные точки (0, 1/2, нет).
      Roles    : r<1 = сжатие → притягивающая неподвижная точка (движок сходимости Пикар/GD/RG/reasoning, вена C);
                 r=1 = изометрия → неподвижная точка не притягивает / осцилляция (отражение RH σ→1−σ, zeta);
                 negb-флип = диагональ → НЕТ неподвижной точки (корень Ловера, парадокс/неразрешимость, вена E).
      Rules    : half_lipschitz (r=1/2); reflect_isometry (r=1) + reflect_not_contraction + reflect_period2;
                 negb_no_fixpoint.
      ДИАГНОСТИКА (P4): липшицево отношение r КЛАССИФИЦИРУЕТ три структурно различных типа неподвижной точки —
      сходимость (r<1, точка, которую достигаешь), симметрия/осцилляция (r=1, точка, вокруг которой кружишь),
      неразрешимость (negb-диагональ, точка, которой не может быть). Сшивает вену C (сходимость), zeta (RH-отражение)
      и вену E (Ловер-диагональ). ЧЕСТНО: три типа классичны (Банах/изометрия/Ловер); ново — унификация под
      классификатором r + связь трёх нитей репо. Уровень: `синтез+наблюдение`.

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (self-contained, Stdlib only; cites FixedPoint/ContractionZeros/LawvereFixedPoint)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  (1) CONTRACTION (r = 1/2 < 1): unique attracting fixed point          *)
(* ===================================================================== *)

Definition half_map (x : Q) : Q := x * (1 # 2).

(** ★ Contraction with ratio 1/2: |half a − half b| = (1/2)·|a − b| < |a − b|. The convergence engine
    (FixedPoint/Picard/GradientDescent/RG): r<1 ⟹ a unique attracting fixed point, reached by iteration. *)
Lemma half_lipschitz : forall a b, Qabs (half_map a - half_map b) == (1 # 2) * Qabs (a - b).
Proof.
  intros a b. unfold half_map.
  assert (H : a * (1 # 2) - b * (1 # 2) == (1 # 2) * (a - b)) by ring.
  rewrite H, Qabs_Qmult.
  assert (H2 : Qabs (1 # 2) == (1 # 2)) by (vm_compute; reflexivity).
  rewrite H2. reflexivity.
Qed.

(** The fixed point is 0 (and it is the attractor of the iteration). *)
Lemma half_fixed_zero : half_map 0 == 0.
Proof. unfold half_map. ring. Qed.

(* ===================================================================== *)
(*  (2) ISOMETRY (r = 1): a fixed point that does NOT attract — RH        *)
(* ===================================================================== *)

Definition reflect (x : Q) : Q := 1 - x.   (* the zeta functional-equation reflection σ ↦ 1 − σ *)

(** ★ Reflection is an ISOMETRY (ratio 1): |reflect a − reflect b| = |a − b| — distance is preserved. *)
Lemma reflect_isometry : forall a b, Qabs (reflect a - reflect b) == Qabs (a - b).
Proof.
  intros a b. unfold reflect.
  assert (H : (1 - a) - (1 - b) == -(a - b)) by ring.
  rewrite H, Qabs_opp. reflexivity.
Qed.

(** Its fixed point is 1/2 — the critical line. *)
Lemma reflect_fixed_half : reflect (1 # 2) == 1 # 2.
Proof. unfold reflect. vm_compute. reflexivity. Qed.

(** It is period-2: iterating returns to the start — the orbit OSCILLATES, it does NOT converge. *)
Lemma reflect_period2 : forall x, reflect (reflect x) == x.
Proof. intro x. unfold reflect. ring. Qed.

(** ★ It is NOT a contraction: no r<1 bounds an isometry (the anti-Banach case, RH's reflection). *)
Lemma reflect_not_contraction :
  ~ (exists r, 0 <= r /\ r < 1 /\ forall a b, Qabs (reflect a - reflect b) <= r * Qabs (a - b)).
Proof.
  intros [r [Hr0 [Hr1 Hc]]]. specialize (Hc 0 1).
  rewrite reflect_isometry in Hc.
  assert (Hd : Qabs (0 - 1) == 1) by (vm_compute; reflexivity).
  rewrite Hd in Hc. lra.
Qed.

(* ===================================================================== *)
(*  (3) DIAGONAL (negb anti-flip): NO fixed point — Lawvere/Cantor        *)
(* ===================================================================== *)

(** ★ The negb anti-flip has NO fixed point: negb b ≠ b. This is the diagonal seed of every
    uncountability / halting / paradox / undecidability result (Lawvere/Cantor; veins E). *)
Lemma negb_no_fixpoint : forall b : bool, negb b <> b.
Proof. intros [|]; discriminate. Qed.

(* ===================================================================== *)
(*  CAPSTONE: the Lipschitz ratio classifies the three fixed-point types  *)
(* ===================================================================== *)

(** ONE classifier (the Lipschitz ratio r, and the negb anti-flip) sorts "fixed point" into three
    structurally opposite phenomena:
      (r<1)  contraction — unique ATTRACTING fixed point, iteration CONVERGES (the engine: Picard/GD/RG/reasoning, vein C);
      (r=1)  isometry — fixed point 1/2 that does NOT attract, iteration OSCILLATES (RH's reflection σ↦1−σ, zeta);
      (negb) diagonal — NO fixed point (the Lawvere/Cantor seed of paradox/undecidability, vein E).
    A point you reach, a point you orbit, a point that cannot exist — three faces of one taxonomy,
    tying the repo's convergence engine, RH's reflection, and the Lawvere diagonal. *)
Theorem fixed_point_taxonomy :
  (forall a b, Qabs (half_map a - half_map b) == (1 # 2) * Qabs (a - b))   (* (1) contraction r=1/2 *)
  /\ half_map 0 == 0                                                       (*     fixed point 0 *)
  /\ (forall a b, Qabs (reflect a - reflect b) == Qabs (a - b))            (* (2) isometry r=1 *)
  /\ reflect (1 # 2) == 1 # 2                                              (*     fixed point 1/2 *)
  /\ (forall x, reflect (reflect x) == x)                                  (*     period-2 oscillation *)
  /\ (~ exists r, 0 <= r /\ r < 1 /\ forall a b, Qabs (reflect a - reflect b) <= r * Qabs (a - b))
  /\ (forall b : bool, negb b <> b).                                       (* (3) diagonal: no fixed point *)
Proof.
  split. exact half_lipschitz.
  split. exact half_fixed_zero.
  split. exact reflect_isometry.
  split. exact reflect_fixed_half.
  split. exact reflect_period2.
  split. exact reflect_not_contraction.
  exact negb_no_fixpoint.
Qed.
