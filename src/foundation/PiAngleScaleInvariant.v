(** * PiAngleScaleInvariant.v — completing the π-incommensurability picture to ALL Pythagorean triples (not
       just coprime): π-commensurability is SCALE-INVARIANT, so every triple reduces to its primitive core.
       PiAngleAllTriples.v proved infinite order for triples where some p | c is coprime to a — but that FAILS
       for non-primitive triples like 15-20-25 (5 | a = 15, and 5 is c's only prime).  The fix is structural:
       the rotation by g·(a,b) over scale g·c is exactly gⁿ times the rotation by (a,b) over c, so finite order
       is invariant under scaling.  Hence 15-20-25, 6-8-10, … reduce to 3-4-5 — covering EVERY triple.

    -- The scaling law (machine-checked) --
      Rot (g·a) (g·b) n = (gⁿ·Xₙ, gⁿ·Yₙ) and cⁿ scales to (g·c)ⁿ = gⁿ·cⁿ.  So the rotation g·(a,b)/g·c returns
      to the identity at stage n  ⟺  gⁿ·Xₙ = gⁿ·cⁿ and gⁿ·Yₙ = 0  ⟺ (g ≠ 0)  Xₙ = cⁿ and Yₙ = 0  ⟺  the
      rotation (a,b)/c returns.  π-commensurability is therefore scale-invariant.

    -- The completed picture --
      Every Pythagorean triple is g times a primitive one; the angle (cos = a/c in lowest terms) is unchanged.
      So infinite order for ALL primitive triples (PiAngleAllTriples, via the eigenvector mod c) + scale
      invariance ⟹ infinite order for EVERY non-degenerate triple — 6-8-10 and 15-20-25 (which the coprime
      criterion could not reach) now follow from 3-4-5.  The role-limit (angle ∉ πℚ) is exactly the
      non-degenerate case; the degenerate axis cases (b = 0: cos = 1) are π-commensurable (finite order),
      the other side of the boundary.

    WHAT THE REPO HAS (surveyed): PiAngleRoleLimit.v (Rot/Xr/Yr/cpow, role_limit_345); PiAngleAllTriples.v
    (the eigenvector theorem for coprime moduli).  GAP: scale invariance, closing the non-primitive triples.

    ============ E/R/R разбор ============
      Elements : масштаб g; поворот g·(a,b) над g·c; примитивное ядро (a,b,c).
      Roles    : π-соизмеримость = конечный порядок (Element); масштаб не меняет угол ⟹ инвариант.
      Rules    : Rot (g·a)(g·b) n = gⁿ·Rot a b n; cpow (g·c) n = gⁿ·cpow c n ⟹ соизмеримость(g·abc) ⟺ соизмеримость(abc).
      ДИАГНОСТИКА (P4): любая тройка = g·(примитивная); угол тот же ⟹ беск. порядок ВСЕХ непримитивных сводится к примитивному
      ядру (15-20-25 → 3-4-5, чего модуль-аргумент не достаёт). Граница: вырожденные (ось, cos=1) = соизмеримы; невырожденные = role-limit.
      Уровень: `новая теорема` (масштаб-инвариантность ⟹ ВСЕ тройки) + `синтез` (полная картина границы).

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (builds on foundation.PiAngleRoleLimit + algebra.RationalRootTest)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import algebra.RationalRootTest.
From ToS Require Import foundation.PiAngleRoleLimit.
Open Scope Z_scope.

(* ===================================================================== *)
(*  Scaling laws                                                           *)
(* ===================================================================== *)

Lemma zpow_nonzero : forall g n, g <> 0 -> zpow g n <> 0.
Proof.
  intros g n Hg. induction n; cbn [zpow].
  - lia.
  - intro Hc. apply Z.mul_eq_0 in Hc. destruct Hc as [H | H]; [ apply Hg; exact H | apply IHn; exact H ].
Qed.

Lemma cpow_scale : forall g c n, cpow (g * c) n = zpow g n * cpow c n.
Proof.
  intros g c. induction n as [| n IH]; cbn [cpow zpow]; [ ring | rewrite IH; ring ].
Qed.

(** ★ The rotation by g·(a,b) over scale g·c is gⁿ times the rotation by (a,b) over c. *)
Lemma rot_scale : forall g a b n,
  Xr (g * a) (g * b) n = zpow g n * Xr a b n /\ Yr (g * a) (g * b) n = zpow g n * Yr a b n.
Proof.
  intros g a b. induction n as [| n IH].
  - unfold Xr, Yr; simpl; cbn [zpow]; split; ring.
  - destruct IH as [IHx IHy].
    rewrite (Xr_S (g * a) (g * b) n), (Yr_S (g * a) (g * b) n),
            (Xr_S a b n), (Yr_S a b n), IHx, IHy.
    change (zpow g (S n)) with (g * zpow g n).
    split; ring.
Qed.

(* ===================================================================== *)
(*  ★★ Scale invariance of π-commensurability                             *)
(* ===================================================================== *)

(** ★★ π-commensurability (finite order) is invariant under scaling the triple by g ≠ 0 — so every triple has
    the same status as its primitive core. *)
Theorem pi_commensurable_scale : forall g a b c : Z,
  g <> 0 -> (pi_commensurable (g * a) (g * b) (g * c) <-> pi_commensurable a b c).
Proof.
  intros g a b c Hg. split.
  - intros [n [Hn [HX HY]]]. exists n. split; [ exact Hn | ].
    destruct (rot_scale g a b n) as [Hsx Hsy].
    assert (Hnz : zpow g n <> 0) by (apply zpow_nonzero; exact Hg).
    split.
    + assert (Heq : zpow g n * Xr a b n = zpow g n * cpow c n)
        by (rewrite <- Hsx, <- cpow_scale; exact HX).
      rewrite Z.mul_cancel_l in Heq by exact Hnz. exact Heq.
    + assert (Heq : zpow g n * Yr a b n = zpow g n * 0)
        by (rewrite Z.mul_0_r, <- Hsy; exact HY).
      rewrite Z.mul_cancel_l in Heq by exact Hnz. exact Heq.
  - intros [n [Hn [HX HY]]]. exists n. split; [ exact Hn | ].
    destruct (rot_scale g a b n) as [Hsx Hsy].
    split.
    + rewrite Hsx, HX, cpow_scale. reflexivity.
    + rewrite Hsy, HY, Z.mul_0_r. reflexivity.
Qed.

(* ===================================================================== *)
(*  Non-primitive triples — reduced to the primitive core 3-4-5            *)
(* ===================================================================== *)

(** ★ 6-8-10 = 2·(3,4,5): a role-limit by scale invariance (the angle equals arccos(3/5)). *)
Corollary role_limit_6_8_10 : ~ pi_commensurable 6 8 10.
Proof. intro H. apply (pi_commensurable_scale 2 3 4 5 ltac:(lia)) in H. exact (role_limit_345 H). Qed.

(** ★ 15-20-25 = 5·(3,4,5): the case the coprime criterion MISSED (5 | a = 15) — now a role-limit via scaling. *)
Corollary role_limit_15_20_25 : ~ pi_commensurable 15 20 25.
Proof. intro H. apply (pi_commensurable_scale 5 3 4 5 ltac:(lia)) in H. exact (role_limit_345 H). Qed.

(* ===================================================================== *)
(*  The other side of the boundary: degenerate axis angles are commensurable *)
(* ===================================================================== *)

(** ★ The degenerate rotation (c,0)/c (cos = 1, the identity) IS π-commensurable — finite order 1.  So the
    role-limit is exactly the NON-degenerate angles. *)
Corollary degenerate_commensurable : forall c : Z, pi_commensurable c 0 c.
Proof.
  intro c. exists 1%nat. split; [ lia | split ].
  - rewrite Xr_1. cbn [cpow]. ring.
  - rewrite Yr_1. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The π-incommensurability picture completed to ALL Pythagorean triples:
      (scaling)     Rot (g·a)(g·b) n = gⁿ·Rot a b n, cpow (g·c) n = gⁿ·cpow c n;
      (invariance)  π-commensurability is scale-invariant — every triple has its primitive core's status;
      (all triples) 6-8-10 and 15-20-25 (which the coprime criterion could not reach) are role-limits via 3-4-5;
      (boundary)    the degenerate axis case (c,0) is π-commensurable (finite order) — the role-limit is
                    exactly the non-degenerate angles.
    So with PiAngleAllTriples (every primitive triple) + this, the constructive shadow of Niven's theorem is
    complete: arccos(a/c)/π is a role-limit for EVERY non-degenerate Pythagorean angle.  Honest: still the
    ANGLE, not π itself (Niven's integral — the wall).  Level: scale invariance closing the non-primitive
    triples plus the full Element/role-limit boundary. *)
Theorem pi_angle_scale_invariant :
  (forall g a b c, g <> 0 -> (pi_commensurable (g * a) (g * b) (g * c) <-> pi_commensurable a b c))
  /\ ~ pi_commensurable 6 8 10
  /\ ~ pi_commensurable 15 20 25
  /\ (forall c, pi_commensurable c 0 c).
Proof.
  split; [ exact pi_commensurable_scale | ].
  split; [ exact role_limit_6_8_10 | ].
  split; [ exact role_limit_15_20_25 | exact degenerate_commensurable ].
Qed.
