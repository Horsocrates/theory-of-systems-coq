(** * ProcessMeasureIntervals.v -- The measure of an interval as a process; distinguishable sets, as a ToS System

    Elements: rational segments [c, d]; the stage sums of the indicator
              ([measure_process a b c d n]); finite chains of segments
              ([list (Q * Q)]); point-processes [x : RealProcess].
    Roles:    [measure_process a b c d] -- the process naming the number d - c;
              [chain lo l]              -- an ordered, non-overlapping family;
              [in_union l x]            -- the point x lies in a segment of l;
              [distinguishable A]       -- A coincides with a finite chain up to
                                           a set covered with arbitrarily small
                                           total length (the indicator of A is
                                           approximated by step functions);
              [finitely_distinguishable A] -- the finite level (Jordan): A is
                                           squeezed between an inner and an
                                           outer finite chain with an arbitrarily
                                           small gap of total lengths;
              [has_content A v]         -- the same, with the number v between.
    Rules:    grid rule: stage n differs from d - c by at most one grid step;
              scaling and shift of an interval; additivity along a chain of
              adjacent intervals; additivity of the process up to the shared
              point (which costs at most one grid step);
              sweep rule: a chain covering the rationals of (c, d) has total
              length >= d - c;
              trisection diagonal: against any sequence of rationals a point of
              a given segment is built that differs from each of them.

    Proved (no axioms):
      - [measure_process_rate], [measure_process_converges],
        [measure_process_Cauchy]: the measure process tends to d - c;
        [measure_process_not_sup]: it is not monotone and overshoots d - c;
      - [measure_scaling], [measure_shift_general],
        [measure_finite_additive_chain];
      - [measure_process_additive_upto_point], [measure_process_additive_equiv];
      - [interval_has_content], [interval_finitely_distinguishable],
        [segment_distinguishable];
      - [diagonal_point_avoids], [segment_has_irrational_point];
      - [chain_cover_lower_bound],
        [segment_rationals_not_finitely_distinguishable];
      - [null_set_distinguishable], [segment_rationals_distinguishable],
        [cantor_distinguishable];
      - [rationals_distinguishable_not_finitely]: the rational points of a
        segment are null and distinguishable, but not finitely distinguishable.

    P4 diagnostic: the measure of an interval is read off a process of finite
      stage sums; distinguishability speaks of finite chains and of covers
      given stage by stage. The number d - c is forced (rate bound); the
      reading "least upper bound of the stages" is not available: the stages
      are not monotone.

    NOT claimed:
      - that finite distinguishability implies distinguishability in general
        (proved here for a segment only);
      - uniqueness of the content of a finitely distinguishable set;
      - a measure for every distinguishable set;
      - a set that is not distinguishable (classically such a set needs the
        Axiom of Choice; none is exhibited here);
      - anything about functions (integrability is treated elsewhere).

    STATUS: 48 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa List.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessSimple.
From ToS Require Import process.ProcessMCT.
From ToS Require Import RiemannIntegration.
From ToS Require Import MeanValueTheorem.
From ToS Require Import Countability_Q.
From ToS Require analysis.LebesgueMeasure.
From ToS Require process.ProcessMeasureTheory.
From ToS Require Import process.ProcessNullCovers.

Open Scope Q_scope.

Module LM := ToS.analysis.LebesgueMeasure.
Module PMT := ToS.process.ProcessMeasureTheory.

(* ===================================================================== *)
(*  1. The measure process of an interval tends to d - c                  *)
(* ===================================================================== *)

Lemma ind_cases : forall c d y,
  (c <= y /\ y <= d /\ indicator c d y == 1) \/
  (y < c /\ indicator c d y == 0) \/
  (d < y /\ indicator c d y == 0).
Proof.
  intros c d y.
  destruct (Qlt_le_dec y c) as [Hyc | Hcy].
  - right. left. split; [ exact Hyc | apply indicator_outside_left; exact Hyc ].
  - destruct (Qlt_le_dec d y) as [Hdy | Hyd].
    + right. right. split; [ exact Hdy | apply indicator_outside_right; exact Hdy ].
    + left. split; [ exact Hcy | split; [ exact Hyd | apply indicator_inside; assumption ] ].
Qed.

Lemma ind_sum_nonneg : forall c d a h k,
  0 <= h -> 0 <= riemann_sum (indicator c d) a h k.
Proof.
  intros c d a h k Hh. induction k as [|k IH]; cbn [riemann_sum].
  - apply Qle_refl.
  - assert (H0 := proj1 (indicator_bounded c d (walk_point a h k))).
    assert (Hm : 0 <= indicator c d (walk_point a h k) * h)
      by (apply Qmult_le_0_compat; assumption).
    lra.
Qed.

(** Upper invariant: S(k) <= max(0, min(x_k, d + h) - c). *)
Lemma ind_sum_upper : forall c d a h k,
  c <= d -> 0 < h ->
  riemann_sum (indicator c d) a h k <= 0 \/
  (riemann_sum (indicator c d) a h k <= walk_point a h k - c /\
   riemann_sum (indicator c d) a h k <= d + h - c).
Proof.
  intros c d a h k Hcd Hh. induction k as [|k IH].
  - left. cbn [riemann_sum]. apply Qle_refl.
  - cbn [riemann_sum walk_point].
    set (y := walk_point a h k) in *.
    set (s := riemann_sum (indicator c d) a h k) in *.
    destruct (ind_cases c d y) as [[H1 [H2 E]] | [[H1 E] | [H1 E]]].
    + assert (Et : indicator c d y * h == h) by (rewrite E; ring).
      right. destruct IH as [IH | [IH1 IH2]]; split; lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      left. destruct IH as [IH | [IH1 IH2]]; lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      destruct IH as [IH | [IH1 IH2]]; [ left; lra | right; split; lra ].
Qed.

(** Lower invariant: S(k) >= min(x_k, d) - c - h. *)
Lemma ind_sum_lower : forall c d a h k,
  a <= c -> c <= d -> 0 < h ->
  walk_point a h k - c - h <= riemann_sum (indicator c d) a h k \/
  d - c - h <= riemann_sum (indicator c d) a h k.
Proof.
  intros c d a h k Hac Hcd Hh. induction k as [|k IH].
  - left. cbn [riemann_sum walk_point]. lra.
  - assert (Hnn : 0 <= riemann_sum (indicator c d) a h k)
      by (apply ind_sum_nonneg; lra).
    cbn [riemann_sum walk_point].
    set (y := walk_point a h k) in *.
    set (s := riemann_sum (indicator c d) a h k) in *.
    destruct (ind_cases c d y) as [[H1 [H2 E]] | [[H1 E] | [H1 E]]].
    + assert (Et : indicator c d y * h == h) by (rewrite E; ring).
      destruct IH as [IH | IH]; [ left; lra | right; lra ].
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      left. lra.
    + assert (Et : indicator c d y * h == 0) by (rewrite E; ring).
      right. destruct IH as [IH | IH]; lra.
Qed.

(** Rate: at stage n the measure process is within one grid step of d - c. *)
Theorem measure_process_rate : forall a b c d n,
  a < b -> a <= c -> c <= d -> d <= b ->
  Qabs (PMT.measure_process a b c d n - (d - c)) <= integral_step a b n.
Proof.
  intros a b c d n Hab Hac Hcd Hdb.
  unfold PMT.measure_process, indicator_process, riemann_process, integral_process.
  set (h := integral_step a b n).
  assert (Hh : 0 < h) by (unfold h; apply integral_step_pos; exact Hab).
  assert (Hend : walk_point a h (S n) == b).
  { rewrite walk_point_qeq. unfold h.
    assert (G := grid_width_eq a b n). lra. }
  destruct (ind_sum_upper c d a h (S n) Hcd Hh) as [U | [U1 U2]];
  destruct (ind_sum_lower c d a h (S n) Hac Hcd Hh) as [L | L];
  apply Qabs_Qle_condition; split; lra.
Qed.

(** The measure process names the number d - c. *)
Theorem measure_process_converges : forall a b c d,
  a < b -> a <= c -> c <= d -> d <= b ->
  PMT.measure_process a b c d ~~ const_process (d - c).
Proof.
  intros a b c d Hab Hac Hcd Hdb eps Heps.
  destruct (integral_step_eventually_small a b eps Hab Heps) as [N HN].
  exists N. intros n Hn. unfold const_process.
  eapply Qle_lt_trans; [ apply measure_process_rate; assumption | apply HN; exact Hn ].
Qed.

Corollary measure_process_Cauchy : forall a b c d,
  a < b -> a <= c -> c <= d -> d <= b ->
  is_Cauchy (PMT.measure_process a b c d).
Proof.
  intros a b c d Hab Hac Hcd Hdb.
  apply (equiv_cauchy_l (const_process (d - c))).
  - apply process_equiv_sym. apply measure_process_converges; assumption.
  - apply const_is_Cauchy.
Qed.

(** The process is not monotone in n and overshoots d - c: for [1/3, 2/3]
    in [0, 1] the stages 1, 2, 3 give 1/2, 2/3, 1/4, while d - c = 1/3.
    The measure is the limit of the stages, not their least upper bound. *)
Example measure_process_not_sup :
  PMT.measure_process 0 1 (1#3) (2#3) 1%nat == 1#2 /\
  PMT.measure_process 0 1 (1#3) (2#3) 2%nat == 2#3 /\
  PMT.measure_process 0 1 (1#3) (2#3) 3%nat == 1#4.
Proof. split; [| split]; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  2. Scaling, shift, additivity along a chain                           *)
(* ===================================================================== *)

(** Scaling: mu([k a, k b]) = k * mu([a, b]). *)
Lemma measure_scaling : forall k a b (Hab : a <= b) (Hk : k * a <= k * b),
  LM.measure_interval (k * a) (k * b) Hk == k * LM.measure_interval a b Hab.
Proof.
  intros k a b Hab Hk. rewrite !LM.measure_interval_eq. ring.
Qed.

Lemma scale_le : forall k a b, 0 <= k -> a <= b -> k * a <= k * b.
Proof.
  intros k a b Hk Hab.
  rewrite (Qmult_comm k a), (Qmult_comm k b).
  apply Qmult_le_compat_r; assumption.
Qed.

(** The same with the premise 0 <= k in place of a ready inequality. *)
Lemma measure_scaling_nonneg : forall k a b (Hk : 0 <= k) (Hab : a <= b),
  LM.measure_interval (k * a) (k * b) (scale_le k a b Hk Hab) ==
  k * LM.measure_interval a b Hab.
Proof.
  intros. apply measure_scaling.
Qed.

(** Shift: mu([a + t, b + t]) = mu([a, b]). *)
Lemma measure_shift_general : forall a b t (Hab : a <= b) (Ht : a + t <= b + t),
  LM.measure_interval (a + t) (b + t) Ht == LM.measure_interval a b Hab.
Proof.
  intros. rewrite !LM.measure_interval_eq. ring.
Qed.

Lemma measure_chain_sum : forall (p : nat -> Q) (Hm : forall k, p k <= p (S k)) n,
  q_sum (fun k => LM.measure_interval (p k) (p (S k)) (Hm k)) n == p n - p 0%nat.
Proof.
  intros p Hm n. induction n as [|n IH]; cbn [q_sum].
  - ring.
  - rewrite IH, LM.measure_interval_eq. ring.
Qed.

(** Finite additivity along a chain of adjacent intervals
    p 0 <= p 1 <= ... <= p n. *)
Theorem measure_finite_additive_chain :
  forall (p : nat -> Q) (Hm : forall k, p k <= p (S k)) n (H0n : p 0%nat <= p n),
  q_sum (fun k => LM.measure_interval (p k) (p (S k)) (Hm k)) n ==
  LM.measure_interval (p 0%nat) (p n) H0n.
Proof.
  intros. rewrite measure_chain_sum, LM.measure_interval_eq. reflexivity.
Qed.

(* ===================================================================== *)
(*  3. Additivity of the measure process                                  *)
(* ===================================================================== *)

Lemma indicator_split : forall c d e x, c <= d -> d <= e ->
  indicator c d x + indicator d e x == indicator c e x + indicator d d x.
Proof.
  intros c d e x Hcd Hde.
  destruct (Qlt_le_dec x c) as [Hxc | Hcx].
  { assert (E1 : indicator c d x == 0) by (apply indicator_outside_left; lra).
    assert (E2 : indicator d e x == 0) by (apply indicator_outside_left; lra).
    assert (E3 : indicator c e x == 0) by (apply indicator_outside_left; lra).
    assert (E4 : indicator d d x == 0) by (apply indicator_outside_left; lra).
    rewrite E1, E2, E3, E4. lra. }
  destruct (Qlt_le_dec x d) as [Hxd | Hdx].
  { assert (E1 : indicator c d x == 1) by (apply indicator_inside; lra).
    assert (E2 : indicator d e x == 0) by (apply indicator_outside_left; lra).
    assert (E3 : indicator c e x == 1) by (apply indicator_inside; lra).
    assert (E4 : indicator d d x == 0) by (apply indicator_outside_left; lra).
    rewrite E1, E2, E3, E4. lra. }
  destruct (Qlt_le_dec d x) as [Hdx' | Hxd'].
  { assert (E1 : indicator c d x == 0) by (apply indicator_outside_right; lra).
    assert (E4 : indicator d d x == 0) by (apply indicator_outside_right; lra).
    destruct (Qlt_le_dec e x) as [Hex | Hxe].
    - assert (E2 : indicator d e x == 0) by (apply indicator_outside_right; lra).
      assert (E3 : indicator c e x == 0) by (apply indicator_outside_right; lra).
      rewrite E1, E2, E3, E4. lra.
    - assert (E2 : indicator d e x == 1) by (apply indicator_inside; lra).
      assert (E3 : indicator c e x == 1) by (apply indicator_inside; lra).
      rewrite E1, E2, E3, E4. lra. }
  assert (E1 : indicator c d x == 1) by (apply indicator_inside; lra).
  assert (E2 : indicator d e x == 1) by (apply indicator_inside; lra).
  assert (E3 : indicator c e x == 1) by (apply indicator_inside; lra).
  assert (E4 : indicator d d x == 1) by (apply indicator_inside; lra).
  rewrite E1, E2, E3, E4. lra.
Qed.

(** At every stage: mu_n[c,d] + mu_n[d,e] = mu_n[c,e] + mu_n[d,d]
    (the shared point d is counted twice). *)
Theorem measure_process_additive_upto_point : forall a b c d e n,
  a < b -> c <= d -> d <= e ->
  PMT.measure_process a b c d n + PMT.measure_process a b d e n ==
  PMT.measure_process a b c e n + PMT.measure_process a b d d n.
Proof.
  intros a b c d e n Hab Hcd Hde.
  unfold PMT.measure_process, indicator_process.
  rewrite <- (riemann_process_add (indicator c d) (indicator d e) a b n).
  rewrite <- (riemann_process_add (indicator c e) (indicator d d) a b n).
  apply Qle_antisym; apply riemann_process_monotone; auto; intro x.
  - rewrite (indicator_split c d e x Hcd Hde). apply Qle_refl.
  - rewrite (indicator_split c d e x Hcd Hde). apply Qle_refl.
Qed.

Lemma walk_point_lt : forall a step k m, 0 < step -> (k < m)%nat ->
  walk_point a step k < walk_point a step m.
Proof.
  intros a step k m Hs. induction m as [|m IH]; intro H; [lia|].
  cbn [walk_point].
  destruct (Nat.eq_dec k m) as [->|Hne]; [lra|].
  assert (H1 : walk_point a step k < walk_point a step m) by (apply IH; lia).
  lra.
Qed.

Lemma rs_point_zero_below : forall d a step m, 0 < step ->
  (forall k, (k < m)%nat -> walk_point a step k < d) ->
  riemann_sum (indicator d d) a step m == 0.
Proof.
  intros d a step m Hs. induction m as [|m IH]; intro H; cbn [riemann_sum].
  - reflexivity.
  - assert (E : indicator d d (walk_point a step m) == 0).
    { apply indicator_outside_left. apply H. lia. }
    rewrite E, IH; [ring | intros k Hk; apply H; lia].
Qed.

Lemma rs_point_le_step : forall d a step m, 0 < step ->
  riemann_sum (indicator d d) a step m <= step.
Proof.
  intros d a step m Hs. induction m as [|m IH]; cbn [riemann_sum].
  - lra.
  - destruct (Qlt_le_dec d (walk_point a step m)) as [Hlt | Hle].
    + assert (E : indicator d d (walk_point a step m) == 0)
        by (apply indicator_outside_right; exact Hlt).
      rewrite E. lra.
    + assert (Z : riemann_sum (indicator d d) a step m == 0).
      { apply rs_point_zero_below; [exact Hs|]. intros k Hk.
        apply Qlt_le_trans with (walk_point a step m);
          [apply walk_point_lt; assumption | exact Hle]. }
      rewrite Z.
      destruct (indicator_bounded d d (walk_point a step m)) as [_ H1].
      assert (H2 : indicator d d (walk_point a step m) * step <= 1 * step)
        by (apply Qmult_le_compat_r; lra).
      lra.
Qed.

(** The point term is at most one grid step. *)
Lemma measure_process_point_le_step : forall a b d n, a < b ->
  PMT.measure_process a b d d n <= integral_step a b n.
Proof.
  intros a b d n Hab.
  unfold PMT.measure_process, indicator_process, riemann_process, integral_process.
  apply rs_point_le_step. apply integral_step_pos. exact Hab.
Qed.

(** Additivity of the process: the sum of the measure processes of [c,d]
    and [d,e] names the same point as the measure process of [c,e]. *)
Theorem measure_process_additive_equiv : forall a b c d e,
  a < b -> c <= d -> d <= e ->
  (fun n => PMT.measure_process a b c d n + PMT.measure_process a b d e n)
    ~~ PMT.measure_process a b c e.
Proof.
  intros a b c d e Hab Hcd Hde eps Heps.
  destruct (integral_step_eventually_small a b eps Hab Heps) as [N HN].
  exists N. intros n Hn.
  assert (E := measure_process_additive_upto_point a b c d e n Hab Hcd Hde).
  assert (H0 : 0 <= PMT.measure_process a b d d n)
    by (apply PMT.measure_process_nonneg; exact Hab).
  assert (H1 := measure_process_point_le_step a b d n Hab).
  assert (H2 := HN n Hn).
  assert (E' : PMT.measure_process a b c d n + PMT.measure_process a b d e n
               - PMT.measure_process a b c e n == PMT.measure_process a b d d n).
  { rewrite E. ring. }
  rewrite E'. rewrite Qabs_pos; [lra | exact H0].
Qed.

(* ===================================================================== *)
(*  4. Finite distinguishability: chains inside and outside               *)
(* ===================================================================== *)

Definition total_len (l : list (Q * Q)) : Q :=
  fold_right (fun p acc => (snd p - fst p) + acc) 0 l.

(** The point named by x lies in one of the segments of l. *)
Definition in_union (l : list (Q * Q)) (x : RealProcess) : Prop :=
  exists p, In p l /\ proc_in_closed x (fst p) (snd p).

(** An ordered, non-overlapping family of segments to the right of lo. *)
Fixpoint chain (lo : Q) (l : list (Q * Q)) : Prop :=
  match l with
  | [] => True
  | p :: r => lo <= fst p /\ fst p <= snd p /\ chain (snd p) r
  end.

(** A is squeezed between an inner and an outer chain whose total lengths
    differ by at most eps. The inner chain is tested on points (Cauchy
    processes) only. *)
Definition finitely_distinguishable_within (A : RealProcess -> Prop) (eps : Q) : Prop :=
  exists inner outer : list (Q * Q),
    (exists lo, chain lo inner) /\ (exists lo, chain lo outer) /\
    (forall x, is_Cauchy x -> in_union inner x -> A x) /\
    (forall x, A x -> in_union outer x) /\
    total_len outer - total_len inner <= eps.

Definition finitely_distinguishable (A : RealProcess -> Prop) : Prop :=
  forall eps, 0 < eps -> finitely_distinguishable_within A eps.

(** The same with the number v between the inner and the outer length. *)
Definition has_content (A : RealProcess -> Prop) (v : Q) : Prop :=
  forall eps, 0 < eps ->
  exists inner outer : list (Q * Q),
    (exists lo, chain lo inner) /\ (exists lo, chain lo outer) /\
    (forall x, is_Cauchy x -> in_union inner x -> A x) /\
    (forall x, A x -> in_union outer x) /\
    total_len inner <= v /\ v <= total_len outer /\
    total_len outer - total_len inner <= eps.

Lemma has_content_finitely_distinguishable : forall A v,
  has_content A v -> finitely_distinguishable A.
Proof.
  intros A v H eps Heps.
  destruct (H eps Heps) as [inner [outer [H1 [H2 [H3 [H4 [_ [_ H7]]]]]]]].
  exists inner, outer. split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | exact H7]]]].
Qed.

(** A segment has content d - c, the measure of the interval. *)
Theorem interval_has_content : forall c d, c <= d ->
  has_content (fun x => proc_in_closed x c d) (d - c).
Proof.
  intros c d Hcd eps Heps.
  exists [(c, d)], [(c, d)].
  split; [ exists c; cbn [chain fst snd]; split; [lra | split; [exact Hcd | exact I]] |].
  split; [ exists c; cbn [chain fst snd]; split; [lra | split; [exact Hcd | exact I]] |].
  split; [| split].
  - intros x _ [p [[Hp | []] Hx]]. subst p. exact Hx.
  - intros x Hx. exists (c, d). split; [left; reflexivity | exact Hx].
  - cbn [total_len fold_right fst snd]. split; [lra | split; lra].
Qed.

Theorem interval_finitely_distinguishable : forall c d, c <= d ->
  finitely_distinguishable (fun x => proc_in_closed x c d).
Proof.
  intros c d Hcd. apply has_content_finitely_distinguishable with (v := d - c).
  apply interval_has_content. exact Hcd.
Qed.

(** The content of a segment is the measure of the interval. *)
Corollary interval_content_is_measure : forall c d (Hcd : c <= d),
  has_content (fun x => proc_in_closed x c d) (LM.measure_interval c d Hcd).
Proof.
  intros c d Hcd eps Heps.
  destruct (interval_has_content c d Hcd eps Heps)
    as [inner [outer [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]].
  exists inner, outer.
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 |]]]].
  rewrite LM.measure_interval_eq. split; [exact H5 | split; [exact H6 | exact H7]].
Qed.

(* ===================================================================== *)
(*  5. A constant point in a segment; chains as covers                    *)
(* ===================================================================== *)

Lemma const_in_closed_inv : forall q lo hi,
  proc_in_closed (const_process q) lo hi -> lo <= q /\ q <= hi.
Proof.
  intros q lo hi H. split.
  - destruct (Qlt_le_dec q lo) as [Hlt | Hle]; [| exact Hle].
    exfalso. assert (He : 0 < lo - q) by lra.
    destruct (H (lo - q) He) as [M HM].
    destruct (HM M (Nat.le_refl M)) as [H1 _]. unfold const_process in H1. lra.
  - destruct (Qlt_le_dec hi q) as [Hlt | Hle]; [| exact Hle].
    exfalso. assert (He : 0 < q - hi) by lra.
    destruct (H (q - hi) He) as [M HM].
    destruct (HM M (Nat.le_refl M)) as [_ H2]. unfold const_process in H2. lra.
Qed.

Lemma chain_total_nonneg : forall l lo, chain lo l -> 0 <= total_len l.
Proof.
  induction l as [|p r IH]; intros lo H.
  - cbn [total_len fold_right]. lra.
  - cbn [chain] in H. destruct H as [_ [H2 H3]].
    assert (Hr := IH (snd p) H3).
    cbn [total_len fold_right]. fold (total_len r). lra.
Qed.

(** Every rational point of a chain lies to the right of its bound. *)
Lemma chain_union_lower : forall l lo q,
  chain lo l -> in_union l (const_process q) -> lo <= q.
Proof.
  induction l as [|p r IH]; intros lo q Hc [p' [Hin Hx]].
  - destruct Hin.
  - cbn [chain] in Hc. destruct Hc as [H1 [H2 H3]].
    destruct Hin as [E | Hin].
    + subst p'. destruct (const_in_closed_inv q (fst p) (snd p) Hx) as [Ha _]. lra.
    + assert (Hq : snd p <= q) by (apply (IH (snd p) q H3); exists p'; split; assumption).
      lra.
Qed.

(** Sweep rule: a chain covering every rational of (c, d) has total
    length at least d - c. *)
Theorem chain_cover_lower_bound : forall l lo c d,
  chain lo l ->
  (forall q : Q, c < q -> q < d -> in_union l (const_process q)) ->
  d - c <= total_len l.
Proof.
  induction l as [|p r IH]; intros lo c d Hc Hcov.
  - cbn [total_len fold_right].
    destruct (Qlt_le_dec c d) as [Hlt | Hle]; [| lra].
    exfalso.
    destruct (Hcov ((c + d) * (1 # 2))) as [p [Hin _]]; [lra | lra | destruct Hin].
  - cbn [chain] in Hc. destruct Hc as [H1 [H2 H3]].
    assert (Hr := chain_total_nonneg r (snd p) H3).
    cbn [total_len fold_right]. fold (total_len r).
    destruct (Qlt_le_dec c d) as [Hcd | Hdc]; [| lra].
    (* the family starts no later than c *)
    assert (Hu : fst p <= c).
    { destruct (Qlt_le_dec c (fst p)) as [Hlt | Hle]; [| exact Hle].
      exfalso.
      destruct (Qlt_le_dec (fst p) d) as [Hud | Hdu].
      - (* a rational between c and fst p *)
        assert (Hq : lo <= (c + fst p) * (1 # 2)).
        { apply (chain_union_lower (p :: r) lo).
          - cbn [chain]. split; [exact H1 | split; [exact H2 | exact H3]].
          - apply Hcov; lra. }
        destruct (Hcov ((c + fst p) * (1 # 2))) as [p' [Hin Hx]]; [lra | lra |].
        destruct Hin as [E | Hin].
        + subst p'. destruct (const_in_closed_inv _ _ _ Hx) as [Ha _]. lra.
        + assert (Hq' : snd p <= (c + fst p) * (1 # 2))
            by (apply (chain_union_lower r (snd p)); [exact H3 | exists p'; split; assumption]).
          lra.
      - (* a rational between c and d, left of the whole family *)
        destruct (Hcov ((c + d) * (1 # 2))) as [p' [Hin Hx]]; [lra | lra |].
        destruct Hin as [E | Hin].
        + subst p'. destruct (const_in_closed_inv _ _ _ Hx) as [Ha _]. lra.
        + assert (Hq' : snd p <= (c + d) * (1 # 2))
            by (apply (chain_union_lower r (snd p)); [exact H3 | exists p'; split; assumption]).
          lra. }
    destruct (Qlt_le_dec c (snd p)) as [Hcv | Hvc].
    + (* the rest covers the rationals of (snd p, d) *)
      assert (Hrest : d - snd p <= total_len r).
      { apply (IH (snd p) (snd p) d H3). intros q Hq1 Hq2.
        destruct (Hcov q) as [p' [Hin Hx]]; [lra | exact Hq2 |].
        destruct Hin as [E | Hin].
        - subst p'. destruct (const_in_closed_inv _ _ _ Hx) as [_ Hb]. lra.
        - exists p'. split; assumption. }
      lra.
    + (* the first segment lies left of c: the rest covers (c, d) *)
      assert (Hrest : d - c <= total_len r).
      { apply (IH (snd p) c d H3). intros q Hq1 Hq2.
        destruct (Hcov q Hq1 Hq2) as [p' [Hin Hx]].
        destruct Hin as [E | Hin].
        - subst p'. destruct (const_in_closed_inv _ _ _ Hx) as [_ Hb]. lra.
        - exists p'. split; assumption. }
      lra.
Qed.

(* ===================================================================== *)
(*  6. The trisection diagonal: a point of a segment avoiding a sequence  *)
(* ===================================================================== *)

(** Width of the stage-k segment inside a segment of width w. *)
Definition stage_w (w : Q) (k : nat) : Q := w * third_pow k.

Lemma stage_w_S : forall w k, stage_w w (S k) == (1 # 3) * stage_w w k.
Proof. intros w k. unfold stage_w. cbn [third_pow]. ring. Qed.

Lemma stage_w_0 : forall w, stage_w w 0 == w.
Proof. intro w. unfold stage_w. cbn [third_pow]. ring. Qed.

Lemma stage_w_pos : forall w k, 0 < w -> 0 < stage_w w k.
Proof.
  intros w k Hw. unfold stage_w. apply Qmult_lt_0_compat; [exact Hw | apply third_pow_pos].
Qed.

(** Left end of the stage-m segment: at step k the third that does not
    contain e k is kept (the left one if e k lies right of the middle,
    the right one otherwise). *)
Fixpoint diag_left (p w : Q) (e : nat -> Q) (m : nat) : Q :=
  match m with
  | O => p
  | S k =>
      if Qlt_le_dec (diag_left p w e k + (1 # 2) * stage_w w k) (e k)
      then diag_left p w e k
      else diag_left p w e k + (2 # 3) * stage_w w k
  end.

Lemma diag_step_cases : forall p w e k,
  (diag_left p w e k + (1 # 2) * stage_w w k < e k /\
   diag_left p w e (S k) = diag_left p w e k) \/
  (e k <= diag_left p w e k + (1 # 2) * stage_w w k /\
   diag_left p w e (S k) = diag_left p w e k + (2 # 3) * stage_w w k).
Proof.
  intros p w e k. cbn [diag_left].
  destruct (Qlt_le_dec (diag_left p w e k + (1 # 2) * stage_w w k) (e k)) as [H | H].
  - left. split; [exact H | reflexivity].
  - right. split; [exact H | reflexivity].
Qed.

Lemma diag_tail : forall p w e n d, 0 < w ->
  diag_left p w e n <= diag_left p w e (n + d) /\
  diag_left p w e (n + d) + stage_w w (n + d) <= diag_left p w e n + stage_w w n.
Proof.
  intros p w e n d Hw. induction d as [|d [IH1 IH2]].
  - rewrite Nat.add_0_r. split; lra.
  - rewrite Nat.add_succ_r.
    assert (Hp := stage_w_pos w (n + d) Hw).
    assert (ES := stage_w_S w (n + d)).
    destruct (diag_step_cases p w e (n + d)) as [[_ E] | [_ E]]; rewrite E; split; lra.
Qed.

(** From step n on, the left ends stay in one segment of stage n. *)
Lemma diag_window : forall p w e n m, 0 < w -> (n <= m)%nat ->
  diag_left p w e n <= diag_left p w e m /\
  diag_left p w e m <= diag_left p w e n + stage_w w n.
Proof.
  intros p w e n m Hw Hnm.
  replace m with (n + (m - n))%nat by lia.
  destruct (diag_tail p w e n (m - n) Hw) as [H1 H2].
  assert (Hp := stage_w_pos w (n + (m - n)) Hw). split; lra.
Qed.

(** After step k the left ends keep the distance w * 3^-k / 6 from e k. *)
Lemma diag_gap : forall p w e k m, 0 < w -> (k < m)%nat ->
  (1 # 6) * stage_w w k <= Qabs (diag_left p w e m - e k).
Proof.
  intros p w e k m Hw Hkm.
  destruct (diag_window p w e (S k) m Hw Hkm) as [H1 H2].
  assert (Hp := stage_w_pos w k Hw).
  assert (ES := stage_w_S w k).
  destruct (diag_step_cases p w e k) as [[Hc E] | [Hc E]]; rewrite E in H1, H2.
  - apply Qle_trans with (- (diag_left p w e m - e k)); [lra |].
    rewrite <- Qabs_opp. apply Qle_Qabs.
  - apply Qle_trans with (diag_left p w e m - e k); [lra | apply Qle_Qabs].
Qed.

Lemma stage_w_below : forall w eps, 0 < w -> 0 < eps ->
  exists n, stage_w w n < eps.
Proof.
  intros w eps Hw Heps.
  assert (He : 0 < eps / w) by (apply Qlt_shift_div_l; lra).
  destruct (third_pow_below (eps / w) He) as [n Hn]. exists n.
  unfold stage_w.
  assert (H : w * third_pow n < w * (eps / w)) by (apply Qmult_lt_l; assumption).
  assert (E : w * (eps / w) == eps) by (field; lra).
  lra.
Qed.

(** Against any sequence e of rationals: a point of [p, p + w] that
    differs from every e k. *)
Theorem diagonal_point_avoids : forall (p w : Q) (e : nat -> Q), 0 < w ->
  exists y : RealProcess,
    is_Cauchy y /\ proc_in_closed y p (p + w) /\
    forall k, ~ (y ~~ const_process (e k)).
Proof.
  intros p w e Hw. exists (diag_left p w e). split; [| split].
  - intros eps Heps. destruct (stage_w_below w eps Hw Heps) as [n Hn].
    exists n. intros m m' Hm Hm'.
    destruct (diag_window p w e n m Hw Hm) as [H1 H2].
    destruct (diag_window p w e n m' Hw Hm') as [H3 H4].
    apply Qabs_Qlt_condition. split; lra.
  - intros eps Heps. exists 0%nat. intros m Hm.
    destruct (diag_window p w e 0%nat m Hw Hm) as [H1 H2].
    cbn [diag_left] in H1, H2. assert (E0 := stage_w_0 w). split; lra.
  - intros k Heq.
    assert (Hp := stage_w_pos w k Hw).
    assert (He : 0 < (1 # 6) * stage_w w k) by lra.
    destruct (Heq _ He) as [N HN].
    specialize (HN (Nat.max N (S k)) (Nat.le_max_l N (S k))).
    unfold const_process in HN.
    assert (G := diag_gap p w e k (Nat.max N (S k)) Hw ltac:(lia)).
    lra.
Qed.

(** Every segment of positive length contains a point that is not rational. *)
Theorem segment_has_irrational_point : forall p q : Q, p < q ->
  exists y : RealProcess,
    is_Cauchy y /\ proc_in_closed y p q /\ ~ rational_point y.
Proof.
  intros p q Hpq.
  assert (Hw : 0 < q - p) by lra.
  destruct (diagonal_point_avoids p (q - p) enum_Q Hw) as [y [Hc [Hin Hav]]].
  exists y. split; [exact Hc | split].
  - apply proc_in_closed_mono with (lo := p) (hi := p + (q - p)); [lra | lra | exact Hin].
  - intro Hr. destruct (rational_point_enumerated y Hr) as [k Hk].
    exact (Hav k Hk).
Qed.

(* ===================================================================== *)
(*  7. The rational points of a segment: not finitely distinguishable     *)
(* ===================================================================== *)

(** A chain all of whose points are rational has total length 0. *)
Lemma rational_chain_degenerate : forall l lo,
  chain lo l ->
  (forall x, is_Cauchy x -> in_union l x -> rational_point x) ->
  total_len l <= 0.
Proof.
  induction l as [|p r IH]; intros lo Hc Hrat.
  - cbn [total_len fold_right]. lra.
  - cbn [chain] in Hc. destruct Hc as [H1 [H2 H3]].
    assert (Hr : total_len r <= 0).
    { apply (IH (snd p) H3). intros x Hx [p' [Hin Hp']].
      apply Hrat; [exact Hx | exists p'; split; [right; exact Hin | exact Hp']]. }
    cbn [total_len fold_right]. fold (total_len r).
    destruct (Qlt_le_dec (fst p) (snd p)) as [Hlt | Hle]; [| lra].
    exfalso.
    destruct (segment_has_irrational_point (fst p) (snd p) Hlt) as [y [Hy [Hin Hirr]]].
    apply Hirr. apply Hrat; [exact Hy | exists p; split; [left; reflexivity | exact Hin]].
Qed.

Lemma segment_rational_is_rational : forall c d x,
  segment_rational_point c d x -> rational_point x.
Proof. intros c d x [q [_ [_ Hq]]]. exists q. exact Hq. Qed.

(** The rational points of [c, d], c < d, are not finitely distinguishable: every
    inner chain has length 0, every outer chain has length >= d - c. *)
Theorem segment_rationals_not_finitely_distinguishable : forall c d : Q, c < d ->
  ~ finitely_distinguishable (segment_rational_point c d).
Proof.
  intros c d Hcd H.
  assert (He : 0 < (d - c) * (1 # 2)) by lra.
  destruct (H _ He) as [inner [outer [[lo1 Hc1] [[lo2 Hc2] [Hin [Hout Hgap]]]]]].
  assert (Hi : total_len inner <= 0).
  { apply (rational_chain_degenerate inner lo1 Hc1).
    intros x Hx Hu. apply (segment_rational_is_rational c d). apply Hin; assumption. }
  assert (Ho : d - c <= total_len outer).
  { apply (chain_cover_lower_bound outer lo2 c d Hc2).
    intros q Hq1 Hq2. apply Hout. exists q.
    split; [lra | split; [lra | apply process_equiv_refl]]. }
  lra.
Qed.

(* ===================================================================== *)
(*  8. Distinguishability: a finite chain up to a small cover             *)
(* ===================================================================== *)

(** The points where A and the union of the chain l differ. *)
Definition sym_diff (A : RealProcess -> Prop) (l : list (Q * Q))
    (x : RealProcess) : Prop :=
  (A x /\ ~ in_union l x) \/ (is_Cauchy x /\ in_union l x /\ ~ A x).

(** A is distinguishable: for every eps there is a finite chain that
    coincides with A outside a set covered by segments of total length
    below eps. In terms of functions: the indicator of A is approximated
    by the indicator of a finite chain, a step function. *)
Definition distinguishable (A : RealProcess -> Prop) : Prop :=
  forall eps, 0 < eps ->
  exists (l : list (Q * Q)) (lo hi : nat -> Q),
    (exists b, chain b l) /\
    (forall k, lo k <= hi k) /\
    (forall x, sym_diff A l x -> exists k, proc_in_closed x (lo k) (hi k)) /\
    (forall N, q_sum (fun k => hi k - lo k) N < eps).

(** A null set is distinguishable: the empty chain approximates it. *)
Theorem null_set_distinguishable : forall A, null_set A -> distinguishable A.
Proof.
  intros A HA eps Heps.
  destruct (null_set_eps A HA eps Heps) as [lo [hi [H1 [H2 H3]]]].
  exists [], lo, hi.
  split; [exists 0; exact I | split; [exact H1 | split; [| exact H3]]].
  intros x [[Hx _] | [_ [[p [[] _]] _]]]. apply H2. exact Hx.
Qed.

Lemma q_sum_zero : forall N, q_sum (fun _ : nat => 0 - 0) N == 0.
Proof.
  induction N as [|N IH]; cbn [q_sum]; [reflexivity | rewrite IH; ring].
Qed.

(** A segment is distinguishable: it is its own chain, nothing differs. *)
Theorem segment_distinguishable : forall c d, c <= d ->
  distinguishable (fun x => proc_in_closed x c d).
Proof.
  intros c d Hcd eps Heps.
  exists [(c, d)], (fun _ => 0), (fun _ => 0).
  split; [exists c; cbn [chain fst snd]; split; [lra | split; [exact Hcd | exact I]] |].
  split; [intro k; lra | split].
  - intros x [[Hx Hn] | [_ [[p [[Hp | []] Hin]] Hn]]].
    + exfalso. apply Hn. exists (c, d). split; [left; reflexivity | exact Hx].
    + exfalso. subst p. apply Hn. exact Hin.
  - intro N. rewrite q_sum_zero. exact Heps.
Qed.

Theorem segment_rationals_distinguishable : forall c d : Q,
  distinguishable (segment_rational_point c d).
Proof.
  intros c d. apply null_set_distinguishable. apply segment_rationals_null.
Qed.

Theorem cantor_distinguishable : distinguishable in_cantor.
Proof. apply null_set_distinguishable. exact cantor_null. Qed.

(** The rational points of a segment: null by covers and distinguishable,
    but not finitely distinguishable -- the step from finite chains to
    covers given as a process is exactly what tells them apart. *)
Theorem rationals_distinguishable_not_finitely : forall c d : Q, c < d ->
  null_set (segment_rational_point c d) /\
  distinguishable (segment_rational_point c d) /\
  ~ finitely_distinguishable (segment_rational_point c d).
Proof.
  intros c d Hcd. split; [| split].
  - apply segment_rationals_null.
  - apply segment_rationals_distinguishable.
  - apply segment_rationals_not_finitely_distinguishable. exact Hcd.
Qed.
