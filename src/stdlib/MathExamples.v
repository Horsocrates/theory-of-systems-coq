(** * MathExamples.v — Cross-Module Mathematical Examples

    Theory of Systems — Verified Standard Library (Tier 2b)

    Demonstrates integration across GroupTheory, RingField, and Topology.
    Each example connects multiple mathematical structures.

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Close Scope Z_scope.
Open Scope Q_scope.

From ToS Require Import GroupTheory RingField Topology.

(* ================================================================= *)
(*  PART I: GROUP COMPUTATION EXAMPLES (3 Qed)                        *)
(* ================================================================= *)

(** 1. Integer addition via group structure: 3 + 5 = 8 *)
Lemma Z_group_add_3_5 :
  g_op Z_add_group 3%Z 5%Z = 8%Z.
Proof. reflexivity. Qed.

(** 2. Rational addition via group structure: 1/2 + 1/2 = 1 *)
Lemma Q_group_add_half :
  g_eq Q_add_group (g_op Q_add_group (1#2) (1#2)) 1.
Proof.
  unfold g_eq, g_op, Q_add_group. ring.
Qed.

(** 3. Group inverse in Z: -(3) = -3 *)
Lemma Z_group_inv_3 :
  g_inv Z_add_group 3%Z = (-3)%Z.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  PART II: RING/FIELD COMPUTATION EXAMPLES (4 Qed)                  *)
(* ================================================================= *)

(** 4. Integer multiplication via ring structure: 2 * 3 = 6 *)
Lemma Z_ring_mul_2_3 :
  r_mul Z_ring 2%Z 3%Z = 6%Z.
Proof. reflexivity. Qed.

(** 5. Rational multiplication via ring structure: (1/2) * (1/3) = 1/6 *)
Lemma Q_ring_mul_half_third :
  g_eq (r_add_group Q_ring) (r_mul Q_ring (1#2) (1#3)) (1#6).
Proof.
  unfold g_eq, r_add_group, r_mul, Q_ring, Q_add_group. ring.
Qed.

(** 6. Field inverse: (1/2) * /(1/2) = 1 *)
Lemma Q_field_inv_half :
  g_eq (r_add_group (f_ring Q_field))
       (r_mul (f_ring Q_field) (1#2) (f_inv Q_field (1#2)))
       (r_one (f_ring Q_field)).
Proof.
  apply f_inv_r.
  unfold g_eq, g_id, r_add_group, f_ring, Q_field, Q_ring, Q_add_group.
  intro H. discriminate H.
Qed.

(** 7. Ring zero annihilation on concrete value: 0 * 42 = 0 *)
Lemma Q_ring_zero_annihilates :
  g_eq (r_add_group Q_ring)
       (r_mul Q_ring 0 42)
       (g_id (r_add_group Q_ring)).
Proof.
  apply r_mul_zero_l.
Qed.

(* ================================================================= *)
(*  PART III: TOPOLOGY EXAMPLES (4 Qed)                               *)
(* ================================================================= *)

(** 8. 1/2 is in the open ball B(0, 1) *)
Lemma half_in_unit_ball : open_ball 0 1 (1#2).
Proof.
  unfold open_ball.
  assert (Heq : (1#2) - 0 == (1#2)) by ring.
  rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(** 9. B(0, 1) is an open set *)
Lemma unit_ball_is_open : is_open (open_ball 0 1).
Proof.
  apply open_ball_is_open. lra.
Qed.

(** 10. The open interval (0, 1) is open *)
Lemma unit_interval_open : is_open (open_interval 0 1).
Proof.
  apply interval_open. lra.
Qed.

(** 11. Intersection of B(0,1) and B(1,1) is bounded *)
Lemma bounded_ball_intersection :
  is_bounded (fun x => open_ball 0 1 x /\ open_ball 1 1 x).
Proof.
  apply intersection_bounded_l.
  apply open_ball_bounded. lra.
Qed.

(* ================================================================= *)
(*  PART IV: CROSS-MODULE CONNECTIONS (4 Qed)                         *)
(* ================================================================= *)

(** 12. Translation by any constant is continuous (topology + algebra) *)
Lemma translation_continuous : forall c, continuous (fun x => x + c).
Proof.
  exact add_const_continuous.
Qed.

(** 13. Doubling is a group homomorphism Z -> Z *)
Lemma Z_double_is_hom :
  is_homomorphism Z_add_group Z_add_group (fun x => g_op Z_add_group x x).
Proof.
  split.
  - intros x y.
    unfold g_op, g_eq, Z_add_group. lia.
  - intros x x' H.
    unfold g_op, g_eq, Z_add_group in *. lia.
Qed.

(** 14. The derived identity law applied to Q_ring:
        for any q, q + 0 = q (ring zero is additive identity) *)
Lemma Q_ring_id_r_example :
  forall q : Q,
    g_eq (r_add_group Q_ring)
         (g_op (r_add_group Q_ring) q (g_id (r_add_group Q_ring)))
         q.
Proof.
  intro q. apply g_id_r.
Qed.

(** 15. Negation (f(x) = -x) is continuous — connects topology and group inverse *)
Lemma negation_continuous : continuous (fun x => - x).
Proof.
  unfold continuous, continuous_at.
  intros x eps Heps.
  exists eps. split; [exact Heps|].
  intros y Hy.
  assert (Heq : - y - - x == -(y - x)) by ring.
  assert (Habs_eq : Qabs (- y - - x) == Qabs (y - x)).
  { apply Qle_antisym.
    - assert (H1 : Qabs (-y - -x) == Qabs (-(y - x))).
      { apply Qabs_wd. ring. }
      assert (H2 : Qabs (-(y - x)) == Qabs (y - x)) by apply Qabs_opp.
      lra.
    - assert (H1 : Qabs (y - x) == Qabs (-(-y - -x))).
      { apply Qabs_wd. ring. }
      assert (H2 : Qabs (-(-y - -x)) == Qabs (-y - -x)) by apply Qabs_opp.
      lra. }
  lra.
Qed.

(* ================================================================= *)
(*  Summary: 15 Qed, 0 Admitted, 0 axioms                             *)
(*    3 group examples: Z_group_add_3_5, Q_group_add_half,            *)
(*      Z_group_inv_3                                                  *)
(*    4 ring/field examples: Z_ring_mul_2_3, Q_ring_mul_half_third,    *)
(*      Q_field_inv_half, Q_ring_zero_annihilates                      *)
(*    4 topology examples: half_in_unit_ball, unit_ball_is_open,       *)
(*      unit_interval_open, bounded_ball_intersection                  *)
(*    4 cross-module: translation_continuous, Z_double_is_hom,         *)
(*      Q_ring_id_r_example, negation_continuous                       *)
(* ================================================================= *)
