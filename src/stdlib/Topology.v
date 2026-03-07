(** * Topology.v — Topological Concepts over Q

    Theory of Systems — Verified Standard Library (Tier 2b)

    Elements: points in Q, subsets (Q -> Prop), open balls, functions Q -> Q
    Roles:    point -> Position, ball -> Neighborhood, set -> Region
    Rules:    open = every point has a ball inside (constitution),
              continuous = preimage of open is open (constitution)
    Status:   open | closed | bounded | compact

    STATUS: 19 Qed, 0 Admitted, 0 axioms
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

(* ========================================================================= *)
(* SECTION 1: BASIC DEFINITIONS                                             *)
(* ========================================================================= *)

(** Open ball: { y : Q | Qabs(y - center) < radius } *)
Definition open_ball (center radius : Q) (x : Q) : Prop :=
  Qabs (x - center) < radius.

(** A set S is open if every point has an open ball inside S *)
Definition is_open (S : Q -> Prop) : Prop :=
  forall x, S x -> exists eps, 0 < eps /\ forall y, open_ball x eps y -> S y.

(** A set S is closed if its complement is open *)
Definition is_closed (S : Q -> Prop) : Prop :=
  is_open (fun x => ~ S x).

(** A set S is bounded if contained in some ball around 0 *)
Definition is_bounded (S : Q -> Prop) : Prop :=
  exists M, 0 < M /\ forall x, S x -> Qabs x < M.

(** Continuity at a point *)
Definition continuous_at (f : Q -> Q) (x : Q) : Prop :=
  forall eps, 0 < eps -> exists delta, 0 < delta /\
  forall y, Qabs (y - x) < delta -> Qabs (f y - f x) < eps.

(** Continuity on all of Q *)
Definition continuous (f : Q -> Q) : Prop :=
  forall x, continuous_at f x.

(** Open interval (a, b) *)
Definition open_interval (a b : Q) (x : Q) : Prop :=
  a < x /\ x < b.

(** Closed interval [a, b] *)
Definition closed_interval (a b : Q) (x : Q) : Prop :=
  a <= x /\ x <= b.

(* ========================================================================= *)
(* SECTION 2: BALL PROPERTIES                                               *)
(* ========================================================================= *)

(** 1. Center is in its own ball *)
Lemma open_ball_center : forall c r, 0 < r -> open_ball c r c.
Proof.
  intros c r Hr.
  unfold open_ball.
  assert (Heq : c - c == 0) by ring.
  rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(** 2. Open balls are open sets *)
Lemma open_ball_is_open : forall c r, 0 < r -> is_open (open_ball c r).
Proof.
  intros c r Hr x Hx.
  unfold open_ball in Hx.
  exists (r - Qabs (x - c)).
  assert (Heps : 0 < r - Qabs (x - c)) by lra.
  split; [exact Heps|].
  intros y Hy.
  unfold open_ball in *.
  assert (Htri : Qabs (y - c) <= Qabs (y - x) + Qabs (x - c)).
  { assert (Heq : y - c == (y - x) + (x - c)) by ring.
    rewrite Heq.
    apply Qabs_triangle. }
  apply Qle_lt_trans with (Qabs (y - x) + Qabs (x - c)); [exact Htri|].
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: OPEN AND CLOSED SETS                                          *)
(* ========================================================================= *)

(** 3. The empty set is open *)
Lemma empty_is_open : is_open (fun _ => False).
Proof.
  unfold is_open.
  intros x Hx. contradiction.
Qed.

(** 4. The full set (all of Q) is open *)
Lemma full_is_open : is_open (fun _ => True).
Proof.
  unfold is_open.
  intros x _.
  exists 1. split; [lra|].
  intros y _. exact I.
Qed.

(** 5. Union of two open sets is open *)
Lemma union_two_open : forall S1 S2,
  is_open S1 -> is_open S2 ->
  is_open (fun x => S1 x \/ S2 x).
Proof.
  intros S1 S2 H1 H2 x [Hx|Hx].
  - destruct (H1 x Hx) as [eps [Heps Hball]].
    exists eps. split; [exact Heps|].
    intros y Hy. left. apply Hball. exact Hy.
  - destruct (H2 x Hx) as [eps [Heps Hball]].
    exists eps. split; [exact Heps|].
    intros y Hy. right. apply Hball. exact Hy.
Qed.

(** 6. Intersection of two open sets is open *)
Lemma intersection_two_open : forall S1 S2,
  is_open S1 -> is_open S2 ->
  is_open (fun x => S1 x /\ S2 x).
Proof.
  intros S1 S2 H1 H2 x [Hx1 Hx2].
  destruct (H1 x Hx1) as [eps1 [Heps1 Hball1]].
  destruct (H2 x Hx2) as [eps2 [Heps2 Hball2]].
  exists (Qmin eps1 eps2).
  split.
  - apply Q.min_glb_lt; assumption.
  - intros y Hy.
    split.
    + apply Hball1.
      unfold open_ball in *.
      apply Qlt_le_trans with (Qmin eps1 eps2); [exact Hy|].
      apply Q.le_min_l.
    + apply Hball2.
      unfold open_ball in *.
      apply Qlt_le_trans with (Qmin eps1 eps2); [exact Hy|].
      apply Q.le_min_r.
Qed.

(* ========================================================================= *)
(* SECTION 4: BOUNDED SETS                                                  *)
(* ========================================================================= *)

(** 7. Open balls are bounded *)
Lemma open_ball_bounded : forall c r, 0 < r -> is_bounded (open_ball c r).
Proof.
  intros c r Hr.
  unfold is_bounded.
  exists (Qabs c + r).
  split.
  - assert (Habs : 0 <= Qabs c) by apply Qabs_nonneg.
    lra.
  - intros x Hx.
    unfold open_ball in Hx.
    assert (Htri : Qabs x <= Qabs (x - c) + Qabs c).
    { assert (Heq : x == (x - c) + c) by ring.
      assert (Habs_eq : Qabs x == Qabs ((x - c) + c)).
      { apply Qabs_wd. exact Heq. }
      assert (Htri0 := Qabs_triangle (x - c) c).
      lra. }
    lra.
Qed.

(** 8. Intersection with a bounded set is bounded *)
Lemma intersection_bounded_l : forall S1 S2,
  is_bounded S1 ->
  is_bounded (fun x => S1 x /\ S2 x).
Proof.
  intros S1 S2 [M [HM Hbd]].
  exists M. split; [exact HM|].
  intros x [Hx1 _].
  apply Hbd. exact Hx1.
Qed.

(* ========================================================================= *)
(* SECTION 5: CONTINUITY                                                    *)
(* ========================================================================= *)

(** 9. The identity function is continuous *)
Lemma identity_continuous : continuous (fun x => x).
Proof.
  unfold continuous, continuous_at.
  intros x eps Heps.
  exists eps. split; [exact Heps|].
  intros y Hy. exact Hy.
Qed.

(** 10. Constant functions are continuous *)
Lemma constant_continuous : forall c, continuous (fun _ => c).
Proof.
  unfold continuous, continuous_at.
  intros c x eps Heps.
  exists 1. split; [lra|].
  intros y _.
  assert (Heq : c - c == 0) by ring.
  rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** 11. Composition preserves continuity at a point *)
Lemma continuous_at_comp : forall f g x,
  continuous_at g x ->
  continuous_at f (g x) ->
  continuous_at (fun y => f (g y)) x.
Proof.
  intros f g x Hg Hf eps Heps.
  destruct (Hf eps Heps) as [delta_f [Hdf Hbf]].
  destruct (Hg delta_f Hdf) as [delta_g [Hdg Hbg]].
  exists delta_g. split; [exact Hdg|].
  intros y Hy.
  apply Hbf. apply Hbg. exact Hy.
Qed.

(** 12. Translation f(x) = x + c is continuous *)
Lemma add_const_continuous : forall c, continuous (fun x => x + c).
Proof.
  unfold continuous, continuous_at.
  intros c x eps Heps.
  exists eps. split; [exact Heps|].
  intros y Hy.
  assert (Heq : y + c - (x + c) == y - x) by ring.
  rewrite Heq. exact Hy.
Qed.

(** 13. Preimage of open set under continuous function is open *)
Lemma continuous_preserves_open_preimage : forall f,
  continuous f ->
  forall S, is_open S ->
  is_open (fun x => S (f x)).
Proof.
  intros f Hcont S Hopen x Hfx.
  destruct (Hopen (f x) Hfx) as [eps [Heps Hball]].
  destruct (Hcont x eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta|].
  intros y Hy.
  apply Hball.
  unfold open_ball.
  apply Hbd. exact Hy.
Qed.

(* ========================================================================= *)
(* SECTION 6: INTERVALS                                                     *)
(* ========================================================================= *)

(** Helper: Qabs bound for open interval membership *)
Lemma qabs_lt_of_bounds : forall a b x y eps,
  a < x -> x < b ->
  eps == Qmin (x - a) (b - x) ->
  Qabs (y - x) < eps ->
  a < y /\ y < b.
Proof.
  intros a b x y eps Hax Hxb Heps_eq Hy.
  assert (Hm1 : 0 < x - a) by lra.
  assert (Hm2 : 0 < b - x) by lra.
  assert (Hmin_pos : 0 < Qmin (x - a) (b - x)).
  { apply Q.min_glb_lt; lra. }
  assert (Habs_bound : Qabs (y - x) < Qmin (x - a) (b - x)).
  { rewrite Heps_eq in Hy. exact Hy. }
  assert (Hle1 : Qmin (x - a) (b - x) <= x - a) by apply Q.le_min_l.
  assert (Hle2 : Qmin (x - a) (b - x) <= b - x) by apply Q.le_min_r.
  assert (Habs_yx : Qabs (y - x) < x - a) by lra.
  assert (Habs_yx2 : Qabs (y - x) < b - x) by lra.
  split.
  - assert (Hneg : -(y - x) <= Qabs (y - x)).
    { apply Qle_trans with (Qabs (-(y - x))).
      - apply Qle_Qabs.
      - assert (Heq : Qabs (-(y - x)) == Qabs (y - x)) by apply Qabs_opp.
        lra. }
    lra.
  - assert (Hpos : y - x <= Qabs (y - x)) by apply Qle_Qabs.
    lra.
Qed.

(** 14. Open intervals are open sets *)
Lemma interval_open : forall a b, a < b -> is_open (open_interval a b).
Proof.
  intros a b Hab x [Hax Hxb].
  exists (Qmin (x - a) (b - x)).
  split.
  - apply Q.min_glb_lt; lra.
  - intros y Hy.
    unfold open_interval.
    unfold open_ball in Hy.
    apply (qabs_lt_of_bounds a b x y (Qmin (x - a) (b - x))); auto.
    reflexivity.
Qed.

(** 15. Closed intervals are closed *)
Lemma closed_interval_closed : forall a b, a <= b -> is_closed (closed_interval a b).
Proof.
  intros a b Hab.
  unfold is_closed, is_open.
  intros x Hx.
  unfold closed_interval in Hx.
  (* x is NOT in [a,b], so either x < a or x > b *)
  assert (Hcase : x < a \/ b < x).
  { destruct (Qlt_le_dec x a) as [Hlt|Hle].
    - left. exact Hlt.
    - right.
      destruct (Qlt_le_dec b x) as [Hlt2|Hle2].
      + exact Hlt2.
      + exfalso. apply Hx. split; assumption. }
  destruct Hcase as [Hxa|Hxb].
  - (* x < a: take eps = a - x *)
    exists (a - x).
    split; [lra|].
    intros y Hy.
    unfold open_ball in Hy.
    unfold closed_interval.
    intros [Hay _].
    assert (Hpos : y - x <= Qabs (y - x)) by apply Qle_Qabs.
    assert (Hlt : y - x < a - x).
    { apply Qle_lt_trans with (Qabs (y - x)); [exact Hpos|exact Hy]. }
    lra.
  - (* x > b: take eps = x - b *)
    exists (x - b).
    split; [lra|].
    intros y Hy.
    unfold open_ball in Hy.
    unfold closed_interval.
    intros [_ Hyb].
    assert (Hneg : -(y - x) <= Qabs (y - x)).
    { apply Qle_trans with (Qabs (-(y - x))).
      - apply Qle_Qabs.
      - assert (Hopp : Qabs (-(y - x)) == Qabs (y - x)) by apply Qabs_opp.
        lra. }
    assert (Hlt : -(y - x) < x - b).
    { apply Qle_lt_trans with (Qabs (y - x)); [exact Hneg|exact Hy]. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 7: MORE CONTINUITY RESULTS                                       *)
(* ========================================================================= *)

(** 16. Sum of continuous-at functions is continuous at a point *)
Lemma continuous_at_sum : forall f g x,
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun y => f y + g y) x.
Proof.
  intros f g x Hf Hg eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hf (eps * (1#2)) Heps2) as [d1 [Hd1 Hb1]].
  destruct (Hg (eps * (1#2)) Heps2) as [d2 [Hd2 Hb2]].
  exists (Qmin d1 d2).
  split.
  - apply Q.min_glb_lt; assumption.
  - intros y Hy.
    assert (Hy1 : Qabs (y - x) < d1).
    { apply Qlt_le_trans with (Qmin d1 d2); [exact Hy|apply Q.le_min_l]. }
    assert (Hy2 : Qabs (y - x) < d2).
    { apply Qlt_le_trans with (Qmin d1 d2); [exact Hy|apply Q.le_min_r]. }
    specialize (Hb1 y Hy1).
    specialize (Hb2 y Hy2).
    assert (Heq : f y + g y - (f x + g x) == (f y - f x) + (g y - g x)) by ring.
    rewrite Heq.
    assert (Htri : Qabs ((f y - f x) + (g y - g x)) <=
                   Qabs (f y - f x) + Qabs (g y - g x))
      by apply Qabs_triangle.
    lra.
Qed.

(** 17. Negation of continuous-at function is continuous at a point *)
Lemma continuous_at_neg : forall f x,
  continuous_at f x ->
  continuous_at (fun y => - f y) x.
Proof.
  intros f x Hf eps Heps.
  destruct (Hf eps Heps) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta|].
  intros y Hy.
  specialize (Hbd y Hy).
  assert (Heq : - f y - - f x == -(f y - f x)) by ring.
  assert (Habs_eq : Qabs (- f y - - f x) == Qabs (f y - f x)).
  { apply Qle_antisym.
    - assert (H1 : Qabs (- f y - - f x) == Qabs (-(f y - f x))).
      { apply Qabs_wd. ring. }
      assert (H2 : Qabs (-(f y - f x)) == Qabs (f y - f x)) by apply Qabs_opp.
      lra.
    - assert (H1 : Qabs (f y - f x) == Qabs (-(- f y - - f x))).
      { apply Qabs_wd. ring. }
      assert (H2 : Qabs (-(- f y - - f x)) == Qabs (- f y - - f x)) by apply Qabs_opp.
      lra. }
  lra.
Qed.

(** 18. Continuous at x implies bounded near x *)
Lemma continuous_at_bounded_near : forall f x,
  continuous_at f x ->
  exists delta, 0 < delta /\
  exists M, 0 < M /\ forall y, Qabs (y - x) < delta -> Qabs (f y) < M.
Proof.
  intros f x Hf.
  destruct (Hf 1 ltac:(lra)) as [delta [Hdelta Hbd]].
  exists delta. split; [exact Hdelta|].
  exists (Qabs (f x) + 1).
  split.
  - assert (Hnn : 0 <= Qabs (f x)) by apply Qabs_nonneg. lra.
  - intros y Hy.
    specialize (Hbd y Hy).
    assert (Htri : Qabs (f y) <= Qabs (f y - f x) + Qabs (f x)).
    { assert (Heq : f y == (f y - f x) + f x) by ring.
      assert (Habs_eq : Qabs (f y) == Qabs ((f y - f x) + f x)).
      { apply Qabs_wd. exact Heq. }
      assert (Htri0 := Qabs_triangle (f y - f x) (f x)).
      lra. }
    lra.
Qed.
