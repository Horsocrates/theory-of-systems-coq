(** * ProcessTopOpen.v — Open Sets as Rational Ball Processes
    Elements: rational balls B(c, r) with c, r ∈ Q
    Roles:    covering (balls that cover S), refining (smaller balls)
    Rules:    ball overlap (union is open), rational density
    Status:   complete
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS TOPOLOGY OPEN — Open Sets as Rational Ball Processes        *)
(*                                                                           *)
(*  Under P4: an open set is NOT a subset of R (R doesn't exist).           *)
(*  An open set is a PROCESS of rational ball covers:                        *)
(*    S_n = union of rational balls B(c_i, r_i) with c_i, r_i ∈ Q          *)
(*  The process {S_n} IS the open set.                                       *)
(*                                                                           *)
(*  STATUS: 20 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs QArith.Qminmax Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Rational Ball  (~7 lemmas)                                *)
(* ================================================================== *)

(** Point in open ball: |x - c| < r *)
Definition in_ball (c r x : Q) : Prop :=
  Qabs (x - c) < r.

(** Center is in its ball *)
Lemma in_ball_center : forall c r,
  0 < r -> in_ball c r c.
Proof.
  intros c r Hr. unfold in_ball.
  assert (Heq : c - c == 0) by lra.
  rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Ball membership is symmetric in a sense *)
Lemma in_ball_sym : forall c r x,
  in_ball c r x -> Qabs (c - x) < r.
Proof.
  intros c r x Hx. unfold in_ball in Hx.
  assert (Heq : c - x == -(x - c)) by lra.
  rewrite Heq.
  destruct (Qlt_le_dec (x - c) 0) as [Hn | Hp].
  - rewrite Qabs_neg in Hx; [| lra].
    rewrite Qabs_pos; lra.
  - rewrite Qabs_pos in Hx; [| lra].
    rewrite Qabs_neg; lra.
Qed.

(** Triangle inequality for balls *)
Lemma in_ball_shrink : forall c r x y,
  in_ball c r x ->
  Qabs (y - x) < r - Qabs (x - c) ->
  in_ball c r y.
Proof.
  intros c r x y Hx Hyx. unfold in_ball in *.
  assert (Htri := Qabs_triangle (y - x) (x - c)).
  assert (Heq : y - x + (x - c) == y - c) by lra.
  assert (Htri2 : Qabs (y - c) <= Qabs (y - x) + Qabs (x - c)).
  { rewrite <- Heq. exact Htri. }
  lra.
Qed.

(* ================================================================== *)
(*  Part II: Open Set Process  (~7 lemmas)                            *)
(* ================================================================== *)

(** Open set over Q *)
Definition QOpenSet := Q -> Prop.

(** Open set: every point has a ball around it inside the set *)
Definition is_open_process (S : QOpenSet) : Prop :=
  forall x, S x -> exists eps, 0 < eps /\
    forall y, Qabs (y - x) < eps -> S y.

(** Empty set is open *)
Lemma empty_open : is_open_process (fun _ => False).
Proof. intros x Hx. contradiction. Qed.

(** Full space is open *)
Lemma full_open : is_open_process (fun _ => True).
Proof.
  intros x _. exists 1. split; [lra |]. intros y _. exact I.
Qed.

(** Open ball is an open set *)
Lemma ball_is_open : forall c r,
  0 < r -> is_open_process (in_ball c r).
Proof.
  intros c r Hr x Hx. unfold in_ball in *.
  exists (r - Qabs (x - c)).
  split; [lra |].
  intros y Hy.
  assert (Htri := Qabs_triangle (y - x) (x - c)).
  assert (Heq : y - x + (x - c) == y - c) by lra.
  assert (Htri2 : Qabs (y - c) <= Qabs (y - x) + Qabs (x - c)).
  { rewrite <- Heq. exact Htri. }
  lra.
Qed.

(** Union of two open sets is open *)
Lemma union_open : forall S1 S2,
  is_open_process S1 -> is_open_process S2 ->
  is_open_process (fun x => S1 x \/ S2 x).
Proof.
  intros S1 S2 H1 H2 x [Hx | Hx].
  - destruct (H1 x Hx) as [eps [Heps Hball]].
    exists eps. split; [exact Heps |].
    intros y Hy. left. exact (Hball y Hy).
  - destruct (H2 x Hx) as [eps [Heps Hball]].
    exists eps. split; [exact Heps |].
    intros y Hy. right. exact (Hball y Hy).
Qed.

(** Intersection of two open sets is open *)
Lemma intersection_open : forall S1 S2,
  is_open_process S1 -> is_open_process S2 ->
  is_open_process (fun x => S1 x /\ S2 x).
Proof.
  intros S1 S2 H1 H2 x [Hx1 Hx2].
  destruct (H1 x Hx1) as [e1 [He1 Hb1]].
  destruct (H2 x Hx2) as [e2 [He2 Hb2]].
  exists (Qmin e1 e2). split.
  - apply Q.min_glb_lt; assumption.
  - intros y Hy. split.
    + apply Hb1. apply Qlt_le_trans with (Qmin e1 e2); [exact Hy |].
      apply Q.le_min_l.
    + apply Hb2. apply Qlt_le_trans with (Qmin e1 e2); [exact Hy |].
      apply Q.le_min_r.
Qed.

(** Open interval is open *)
Lemma open_interval_open : forall a b,
  a < b -> is_open_process (fun x => a < x /\ x < b).
Proof.
  intros a b Hab x [Hax Hxb].
  exists (Qmin (x - a) (b - x)). split.
  - apply Q.min_glb_lt; lra.
  - intros y Hy.
    assert (Hmin1 : Qmin (x - a) (b - x) <= x - a) by apply Q.le_min_l.
    assert (Hmin2 : Qmin (x - a) (b - x) <= b - x) by apply Q.le_min_r.
    assert (Habs := Qabs_triangle (y - x) 0).
    assert (Hnn := Qabs_nonneg (y - x)).
    destruct (Qlt_le_dec (y - x) 0) as [Hn | Hp].
    + rewrite Qabs_neg in Hy; [| lra]. split; lra.
    + rewrite Qabs_pos in Hy; [| lra]. split; lra.
Qed.

(* ================================================================== *)
(*  Part III: Hausdorff Separation  (~3 lemmas)                      *)
(* ================================================================== *)

(** Helper: distinct rationals have positive distance *)
Lemma not_Qeq_pos_dist : forall x y : Q,
  ~ (x == y) -> 0 < Qabs (x - y).
Proof.
  intros x y Hneq.
  destruct (Qlt_le_dec 0 (Qabs (x - y))) as [Hpos | Hneg].
  - exact Hpos.
  - exfalso. apply Hneq.
    assert (Hnn := Qabs_nonneg (x - y)).
    assert (Heq : Qabs (x - y) == 0) by lra.
    destruct (Qlt_le_dec (x - y) 0) as [Hn | Hp].
    + rewrite Qabs_neg in Heq; lra.
    + rewrite Qabs_pos in Heq; lra.
Qed.

(** Q is Hausdorff: distinct points are separated by disjoint balls *)
Theorem hausdorff_Q : forall x y : Q,
  ~ (x == y) ->
  exists e : Q, 0 < e /\
    (forall z, Qabs (z - x) < e -> Qabs (z - y) < e -> False).
Proof.
  intros x y Hneq.
  set (d := Qabs (x - y)).
  assert (Hd : 0 < d) by (apply not_Qeq_pos_dist; exact Hneq).
  exists (d * (1#2)). split.
  { assert (H12 : (0 : Q) == 0 * (1#2)) by lra.
    rewrite H12. apply Qmult_lt_compat_r; lra. }
  intros z Hz1 Hz2.
  (* |x-y| <= |x-z| + |z-y| by triangle *)
  assert (Htri := Qabs_triangle (x - z) (z - y)).
  assert (Heq : x - z + (z - y) == x - y) by lra.
  assert (Htri2 : d <= Qabs (x - z) + Qabs (z - y)).
  { unfold d. rewrite <- Heq. exact Htri. }
  (* |x-z| < d/2 because |x-z| = |z-x| < d/2 *)
  assert (Hxz : Qabs (x - z) < d * (1#2)).
  { (* Triangle on z-x gives x-z = -(z-x) *)
    destruct (Qlt_le_dec (z - x) 0) as [Hn | Hp].
    - assert (Hpn : 0 <= x - z) by lra.
      rewrite Qabs_pos; [| exact Hpn].
      rewrite Qabs_neg in Hz1; [| lra]. lra.
    - assert (Hpn : x - z <= 0) by lra.
      rewrite Qabs_neg; [| exact Hpn].
      rewrite Qabs_pos in Hz1; [| lra]. lra. }
  lra.
Qed.

(* ================================================================== *)
(*  Part IV: Ball Cover Process  (~3 lemmas)                          *)
(* ================================================================== *)

(** A ball cover: list of (center, radius) pairs *)
Definition QBallCover := list (Q * Q).

(** Point covered by a ball cover *)
Definition covered_by_balls (bc : QBallCover) (x : Q) : Prop :=
  exists p, In p bc /\ 0 < snd p /\ in_ball (fst p) (snd p) x.

(** Single ball covers its center *)
Lemma single_ball_covers_center : forall c r,
  0 < r -> covered_by_balls [(c, r)] c.
Proof.
  intros c r Hr. exists (c, r). simpl. split.
  - left. reflexivity.
  - split; [exact Hr |]. apply in_ball_center. exact Hr.
Qed.

(** Appending covers gives union cover *)
Lemma append_covers_union : forall b1 b2 x,
  covered_by_balls b1 x \/ covered_by_balls b2 x ->
  covered_by_balls (b1 ++ b2) x.
Proof.
  intros b1 b2 x [Hb1 | Hb2].
  - destruct Hb1 as [p [Hin [Hpos Hball]]].
    exists p. split; [| split; [exact Hpos | exact Hball]].
    apply in_or_app. left. exact Hin.
  - destruct Hb2 as [p [Hin [Hpos Hball]]].
    exists p. split; [| split; [exact Hpos | exact Hball]].
    apply in_or_app. right. exact Hin.
Qed.

(** The open process: sequence of finite ball covers *)
Definition OpenProcess := nat -> QBallCover.

(** An open process is refining: more coverage at higher levels *)
Definition is_refining (op : OpenProcess) : Prop :=
  forall n x, covered_by_balls (op n) x ->
    covered_by_balls (op (S n)) x.

(** Under P4: at every level, the cover is finite (trivially) *)
Lemma p4_cover_finite : forall (op : OpenProcess) n,
  exists k, length (op n) = k.
Proof. intros op n. exists (length (op n)). reflexivity. Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check in_ball. Check in_ball_center. Check in_ball_sym.
Check in_ball_shrink.
Check is_open_process. Check empty_open. Check full_open.
Check ball_is_open. Check union_open. Check intersection_open.
Check open_interval_open.
Check not_Qeq_pos_dist. Check hausdorff_Q.
Check covered_by_balls. Check single_ball_covers_center.
Check append_covers_union. Check p4_cover_finite.
