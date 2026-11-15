(** * ProcessNullCovers.v -- Measure zero by covering processes, as a ToS System

    Elements: point-processes [x : RealProcess]; closed rational segments
              [[lo k, hi k]]; the stage lists [cantor_stage n] (left ends of the
              2^n segments of length 3^-n); digit codes [dg : nat -> bool].
    Roles:    [proc_in_closed x lo hi]  -- the point named by x lies in [lo, hi]
                                           (a property of the point-class);
              [covering_process A lo hi mu] -- at every stage n the segments
                                           [lo n k, hi n k] cover A and every
                                           partial sum of their lengths is <= mu n;
              [null_set A]              -- A has a covering process tending to 0;
              [in_cantor x]             -- x lies in every trisection stage;
              [cantor_point dg]         -- the point named by a code of digits 0 / 2.
    Rules:    geometric budget: the k-th point of an enumeration receives the
              share (1/2)^(k+1) of the stage budget (1/2)^n;
              trisection: every segment of a stage leaves its two outer thirds;
              count 2^n, length 3^-n, total (2/3)^n; stages are nested;
              codes that differ first at place i name points 3^-(i+1) apart.

    Proved (no axioms):
      - [countable_null]: every set of points exhausted by a sequence of
        rational points is null; [rationals_null], [segment_rationals_null];
        [rationals_open_cover] (the textbook form with open intervals);
      - [cantor_stage_count], [cantor_stage_total]: 2^n segments, total (2/3)^n;
        [cantor_covering_process], [cantor_null]: the Cantor set is null;
      - [cantor_point_in_cantor], [cantor_point_Cauchy]: every code names a point
        of the set; [cantor_points_distinct], [cantor_points_not_enumerable]:
        no sequence of codes names all points of the set;
      - [covering_measure_is_null]: the length bound of a null set satisfies the
        earlier numeric predicate [ProcessMeasureTheory.is_null_set].
      The convergence facts are the earlier theorems [rationals_cover_to_zero]
      and [cantor_measure_zero]; here they receive the covers they speak about.

    P4 diagnostic: a cover is a process of stages, each stage an explicitly
      given family of segments; no infimum over all covers and no completed
      totality of points is used. The bound [mu] is not forced: any budget
      process tending to 0 qualifies.

    NOT claimed:
      - that a whole segment of point-processes is not null in the cover sense
        (no axiom-free proof is expected: recursive analysis has singular
        coverings of the computable continuum);
      - nullness of a countable family of arbitrary (non-rational) points
        (moduli of convergence would be needed to place the segments);
      - non-enumerability against sequences of arbitrary processes (only
        sequences of codes are treated: reading digits off a process needs a
        modulus);
      - countable unions of null sets.

    STATUS: 55 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa List Bool.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessRationalsNull.
From ToS Require Import process.ProcessCantorMeasure.
From ToS Require process.ProcessMeasureTheory.
From ToS Require Import Countability_Q.

Open Scope Q_scope.

Module PMT := ToS.process.ProcessMeasureTheory.

(* ===================================================================== *)
(*  1. A point-process in a closed segment                                *)
(* ===================================================================== *)

(** The point named by x lies in [lo, hi]: for every margin the process
    eventually stays inside the widened segment. *)
Definition proc_in_closed (x : RealProcess) (lo hi : Q) : Prop :=
  forall eps, 0 < eps ->
    exists M, forall m, (M <= m)%nat -> lo - eps < x m /\ x m < hi + eps.

(** Membership is a property of the point-class, not of its representative. *)
Lemma proc_in_closed_equiv : forall x y lo hi,
  x ~~ y -> proc_in_closed x lo hi -> proc_in_closed y lo hi.
Proof.
  intros x y lo hi Hxy H eps Heps.
  assert (Heps2 : 0 < eps * (1 # 2)) by lra.
  destruct (H _ Heps2) as [M1 H1]. destruct (Hxy _ Heps2) as [M2 H2].
  exists (Nat.max M1 M2). intros m Hm.
  assert (Hm1 : (M1 <= m)%nat) by lia.
  assert (Hm2 : (M2 <= m)%nat) by lia.
  destruct (H1 m Hm1) as [Ha Hb].
  specialize (H2 m Hm2). apply Qabs_Qlt_condition in H2. destruct H2 as [Hc Hd].
  split; lra.
Qed.

Lemma proc_in_closed_mono : forall x lo hi lo' hi',
  lo' <= lo -> hi <= hi' -> proc_in_closed x lo hi -> proc_in_closed x lo' hi'.
Proof.
  intros x lo hi lo' hi' Hl Hh H eps Heps.
  destruct (H eps Heps) as [M HM]. exists M. intros m Hm.
  destruct (HM m Hm) as [Ha Hb]. split; lra.
Qed.

Lemma proc_in_closed_const : forall q lo hi,
  lo <= q -> q <= hi -> proc_in_closed (const_process q) lo hi.
Proof.
  intros q lo hi Hl Hh eps Heps. exists 0%nat. intros m _.
  unfold const_process. split; lra.
Qed.

(* ===================================================================== *)
(*  2. Measure zero: a covering process tending to 0                      *)
(* ===================================================================== *)

(** One stage of a cover: the segments [lo k, hi k] cover A and every
    partial sum of their lengths is at most [bound]. *)
Definition covers_at (A : RealProcess -> Prop) (lo hi : nat -> Q) (bound : Q) : Prop :=
  (forall k, lo k <= hi k) /\
  (forall x, A x -> exists k, proc_in_closed x (lo k) (hi k)) /\
  (forall N, q_sum (fun k => hi k - lo k) N <= bound).

(** A covering process: a cover at every stage n, with length bound mu n. *)
Definition covering_process (A : RealProcess -> Prop)
    (lo hi : nat -> nat -> Q) (mu : RealProcess) : Prop :=
  forall n, covers_at A (lo n) (hi n) (mu n).

(** A set of points has measure zero: it has a covering process whose
    length bound tends to 0. *)
Definition null_set (A : RealProcess -> Prop) : Prop :=
  exists (lo hi : nat -> nat -> Q) (mu : RealProcess),
    covering_process A lo hi mu /\ mu ~~ const_process 0.

Lemma tends_to_zero_below : forall mu : RealProcess,
  mu ~~ const_process 0 -> forall eps, 0 < eps -> exists n, mu n < eps.
Proof.
  intros mu H eps Heps. destruct (H eps Heps) as [n Hn]. exists n.
  specialize (Hn n (Nat.le_refl n)). unfold const_process in Hn.
  apply Qle_lt_trans with (Qabs (mu n - 0)); [| exact Hn].
  assert (E : mu n - 0 == mu n) by ring. rewrite E. apply Qle_Qabs.
Qed.

(** The epsilon form: covers of arbitrarily small total length. *)
Theorem null_set_eps : forall A, null_set A ->
  forall eps, 0 < eps ->
  exists lo hi : nat -> Q,
    (forall k, lo k <= hi k) /\
    (forall x, A x -> exists k, proc_in_closed x (lo k) (hi k)) /\
    (forall N, q_sum (fun k => hi k - lo k) N < eps).
Proof.
  intros A [lo [hi [mu [Hc Hz]]]] eps Heps.
  destruct (tends_to_zero_below mu Hz eps Heps) as [n Hn].
  destruct (Hc n) as [H1 [H2 H3]].
  exists (lo n), (hi n). split; [exact H1 | split; [exact H2 |]].
  intro N. apply Qle_lt_trans with (mu n); [apply H3 | exact Hn].
Qed.

Lemma null_set_subset : forall A B : RealProcess -> Prop,
  (forall x, A x -> B x) -> null_set B -> null_set A.
Proof.
  intros A B Hsub [lo [hi [mu [Hc Hz]]]].
  exists lo, hi, mu. split; [| exact Hz].
  intro n. destruct (Hc n) as [H1 [H2 H3]].
  split; [exact H1 | split; [| exact H3]].
  intros x Hx. apply H2. apply Hsub. exact Hx.
Qed.

Lemma covering_measure_nonneg : forall A lo hi mu,
  covering_process A lo hi mu -> forall n, 0 <= mu n.
Proof.
  intros A lo hi mu Hc n. destruct (Hc n) as [_ [_ H3]].
  specialize (H3 0%nat). cbn [q_sum] in H3. exact H3.
Qed.

(** Bridge to the earlier numeric predicate: the length bound of a null
    set is a null process in the sense of ProcessMeasureTheory. *)
Theorem covering_measure_is_null : forall A lo hi mu,
  covering_process A lo hi mu -> mu ~~ const_process 0 -> PMT.is_null_set mu.
Proof.
  intros A lo hi mu _ Hz eps Heps.
  destruct (Hz eps Heps) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold const_process in HN.
  apply Qle_lt_trans with (Qabs (mu n - 0)); [| exact HN].
  assert (E : mu n - 0 == mu n) by ring. rewrite E. apply Qle_Qabs.
Qed.

(* ===================================================================== *)
(*  3. Countable => null: the geometric budget                            *)
(* ===================================================================== *)

Lemma half_pow_pos : forall n, 0 < half_pow n.
Proof. induction n as [|n IH]; cbn [half_pow]; lra. Qed.

(** Half-width of the segment around the k-th point at stage n:
    its length 2 * cov_radius n k = (1/2)^n * (1/2)^(k+1). *)
Definition cov_radius (n k : nat) : Q := half_pow n * half_pow (S (S k)).

Lemma cov_radius_pos : forall n k, 0 < cov_radius n k.
Proof.
  intros n k. unfold cov_radius. apply Qmult_lt_0_compat; apply half_pow_pos.
Qed.

Definition cov_lo (e : nat -> Q) (n k : nat) : Q := e k - cov_radius n k.
Definition cov_hi (e : nat -> Q) (n k : nat) : Q := e k + cov_radius n k.

(** The first N lengths of stage n add up to (1/2)^n * (1 - (1/2)^N). *)
Lemma cov_radius_sum : forall n N,
  q_sum (fun k => 2 * cov_radius n k) N == half_pow n * (1 - half_pow N).
Proof.
  intros n N. induction N as [|N IH].
  - cbn [q_sum half_pow]. ring.
  - cbn [q_sum]. rewrite IH. unfold cov_radius. cbn [half_pow]. ring.
Qed.

Lemma cov_sum : forall e n N,
  q_sum (fun k => cov_hi e n k - cov_lo e n k) N == half_pow n * (1 - half_pow N).
Proof.
  intros e n N. induction N as [|N IH].
  - cbn [q_sum half_pow]. ring.
  - cbn [q_sum]. rewrite IH. unfold cov_hi, cov_lo, cov_radius. cbn [half_pow]. ring.
Qed.

Lemma geometric_budget_lt : forall n N,
  half_pow n * (1 - half_pow N) < half_pow n.
Proof.
  intros n N.
  assert (Hp : 0 < half_pow n * half_pow N)
    by (apply Qmult_lt_0_compat; apply half_pow_pos).
  assert (E : half_pow n * (1 - half_pow N) == half_pow n - half_pow n * half_pow N)
    by ring.
  rewrite E. set (p := half_pow n * half_pow N) in *. lra.
Qed.

(** Every partial sum of the lengths of stage n stays below (1/2)^n. *)
Lemma cov_sum_lt : forall e n N,
  q_sum (fun k => cov_hi e n k - cov_lo e n k) N < half_pow n.
Proof.
  intros e n N. rewrite cov_sum. apply geometric_budget_lt.
Qed.

Lemma const_point_in_cov : forall e n k,
  proc_in_closed (const_process (e k)) (cov_lo e n k) (cov_hi e n k).
Proof.
  intros e n k. assert (H := cov_radius_pos n k).
  apply proc_in_closed_const; unfold cov_lo, cov_hi; lra.
Qed.

(** The covering process of a set exhausted by a sequence e of rational
    points: its length bound is the process (1/2)^n. *)
Theorem countable_covering_process : forall (A : RealProcess -> Prop) (e : nat -> Q),
  (forall x, A x -> exists k, x ~~ const_process (e k)) ->
  covering_process A (cov_lo e) (cov_hi e) half_pow.
Proof.
  intros A e He n. split; [| split].
  - intro k. assert (H := cov_radius_pos n k). unfold cov_lo, cov_hi. lra.
  - intros x Hx. destruct (He x Hx) as [k Hk]. exists k.
    apply proc_in_closed_equiv with (x := const_process (e k)).
    + apply process_equiv_sym. exact Hk.
    + apply const_point_in_cov.
  - intro N. apply Qlt_le_weak. apply cov_sum_lt.
Qed.

(** The rule "countable => null". *)
Theorem countable_null : forall (A : RealProcess -> Prop) (e : nat -> Q),
  (forall x, A x -> exists k, x ~~ const_process (e k)) -> null_set A.
Proof.
  intros A e He. exists (cov_lo e), (cov_hi e), half_pow.
  split; [apply countable_covering_process; exact He | exact rationals_cover_to_zero].
Qed.

(** A single point is null in the cover sense as well. *)
Corollary point_null : forall q : Q, null_set (fun x => x ~~ const_process q).
Proof.
  intro q. apply countable_null with (e := fun _ => q).
  intros x Hx. exists 0%nat. exact Hx.
Qed.

(** Rational points of the continuum and of a segment. *)
Definition rational_point (x : RealProcess) : Prop :=
  exists q : Q, x ~~ const_process q.

Definition segment_rational_point (c d : Q) (x : RealProcess) : Prop :=
  exists q : Q, c <= q /\ q <= d /\ x ~~ const_process q.

Lemma rational_point_enumerated : forall x, rational_point x ->
  exists k, x ~~ const_process (enum_Q k).
Proof.
  intros x [q Hq]. destruct (Q_countable q) as [k Hk]. exists k.
  intros eps Heps. destruct (Hq eps Heps) as [N HN]. exists N. intros n Hn.
  specialize (HN n Hn). unfold const_process in *. rewrite Hk. exact HN.
Qed.

Theorem rationals_covering_process :
  covering_process rational_point (cov_lo enum_Q) (cov_hi enum_Q) half_pow.
Proof.
  apply countable_covering_process. exact rational_point_enumerated.
Qed.

Theorem rationals_null : null_set rational_point.
Proof.
  apply countable_null with (e := enum_Q). exact rational_point_enumerated.
Qed.

Theorem segment_rationals_null : forall c d : Q,
  null_set (segment_rational_point c d).
Proof.
  intros c d. apply null_set_subset with (B := rational_point); [| exact rationals_null].
  intros x [q [_ [_ Hq]]]. exists q. exact Hq.
Qed.

(** The textbook form: for every eps there are open intervals around the
    enumerated rationals, each rational strictly inside one of them, with
    every partial sum of lengths below eps. *)
Theorem rationals_open_cover : forall eps, 0 < eps ->
  exists rad : nat -> Q,
    (forall k, 0 < rad k) /\
    (forall q : Q, exists k, Qabs (q - enum_Q k) < rad k) /\
    (forall N, q_sum (fun k => 2 * rad k) N < eps).
Proof.
  intros eps Heps.
  destruct (tends_to_zero_below half_pow rationals_cover_to_zero eps Heps) as [n Hn].
  exists (cov_radius n). split; [| split].
  - intro k. apply cov_radius_pos.
  - intro q. destruct (Q_countable q) as [k Hk]. exists k.
    assert (E : q - enum_Q k == 0) by (rewrite Hk; ring).
    rewrite E. change (0 < cov_radius n k). apply cov_radius_pos.
  - intro N. apply Qlt_trans with (half_pow n); [| exact Hn].
    rewrite cov_radius_sum. apply geometric_budget_lt.
Qed.

Corollary rationals_cover_measure_is_null : PMT.is_null_set half_pow.
Proof.
  apply (covering_measure_is_null rational_point (cov_lo enum_Q) (cov_hi enum_Q)).
  - exact rationals_covering_process.
  - exact rationals_cover_to_zero.
Qed.

(* ===================================================================== *)
(*  4. A finite list of equal segments as a stage of a cover              *)
(* ===================================================================== *)

Definition list_lo (l : list Q) (k : nat) : Q := nth k l 0.

Definition list_hi (l : list Q) (w : Q) (k : nat) : Q :=
  if (k <? length l)%nat then nth k l 0 + w else nth k l 0.

Lemma list_cover_le : forall l w k, 0 <= w -> list_lo l k <= list_hi l w k.
Proof.
  intros l w k Hw. unfold list_lo, list_hi.
  destruct (k <? length l)%nat; lra.
Qed.

Lemma list_cover_hit : forall l w a, In a l ->
  exists k, list_lo l k = a /\ list_hi l w k = a + w.
Proof.
  intros l w a Ha. destruct (In_nth l a 0 Ha) as [k [Hk Hn]].
  exists k. unfold list_lo, list_hi. split; [exact Hn|].
  apply Nat.ltb_lt in Hk. rewrite Hk, Hn. reflexivity.
Qed.

Lemma list_cover_sum_eq : forall l w N,
  q_sum (fun k => list_hi l w k - list_lo l k) N
  == inject_Z (Z.of_nat (Nat.min N (length l))) * w.
Proof.
  intros l w N. induction N as [|N IH].
  - cbn [q_sum Nat.min]. change (inject_Z (Z.of_nat 0)) with 0. ring.
  - cbn [q_sum]. rewrite IH. unfold list_hi, list_lo.
    destruct (Nat.ltb_spec N (length l)) as [Hlt | Hge].
    + rewrite (Nat.min_l N (length l)) by lia.
      rewrite (Nat.min_l (S N) (length l)) by lia.
      rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus.
      change (inject_Z 1) with 1. ring.
    + rewrite (Nat.min_r N (length l)) by lia.
      rewrite (Nat.min_r (S N) (length l)) by lia. ring.
Qed.

(** Partial sums of the lengths never exceed (number of segments) * w. *)
Lemma list_cover_sum : forall l w N, 0 <= w ->
  q_sum (fun k => list_hi l w k - list_lo l k) N
  <= inject_Z (Z.of_nat (length l)) * w.
Proof.
  intros l w N Hw. rewrite list_cover_sum_eq.
  apply Qmult_le_compat_r; [| exact Hw].
  rewrite <- Zle_Qle. apply Nat2Z.inj_le. apply Nat.le_min_r.
Qed.

(* ===================================================================== *)
(*  5. The Cantor construction: stages of trisection                      *)
(* ===================================================================== *)

Fixpoint third_pow (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (1 # 3) * third_pow k
  end.

Lemma third_pow_pos : forall n, 0 < third_pow n.
Proof. induction n as [|n IH]; cbn [third_pow]; lra. Qed.

Lemma third_pow_le_half_pow : forall n, third_pow n <= half_pow n.
Proof.
  induction n as [|n IH]; cbn [third_pow half_pow]; [lra|].
  assert (H := third_pow_pos n). lra.
Qed.

Lemma third_pow_below : forall eps, 0 < eps -> exists n, third_pow n < eps.
Proof.
  intros eps Heps.
  destruct (tends_to_zero_below half_pow rationals_cover_to_zero eps Heps) as [n Hn].
  exists n. apply Qle_lt_trans with (half_pow n); [apply third_pow_le_half_pow | exact Hn].
Qed.

(** From the segment [a, a + 3w] the outer thirds [a, a + w] and
    [a + 2w, a + 3w] remain: the list of their left ends. *)
Definition split_third (w a : Q) : list Q := [a; a + 2 * w].

(** Stage n: the left ends of the segments of length third_pow n. *)
Fixpoint cantor_stage (n : nat) : list Q :=
  match n with
  | O => [0]
  | S k => flat_map (split_third (third_pow (S k))) (cantor_stage k)
  end.

Lemma flat_split_length : forall w l,
  length (flat_map (split_third w) l) = (2 * length l)%nat.
Proof.
  intros w l. induction l as [|a l IH].
  - reflexivity.
  - cbn [flat_map split_third app length]. rewrite IH. lia.
Qed.

(** Stage n consists of exactly 2^n segments. *)
Theorem cantor_stage_count : forall n,
  length (cantor_stage n) = Nat.pow 2%nat n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [cantor_stage]. rewrite flat_split_length, IH. cbn [Nat.pow]. lia.
Qed.

(** Their total length (number of segments times 3^-n) is the process
    (2/3)^n of ProcessCantorMeasure. *)
Theorem cantor_stage_total : forall n,
  inject_Z (Z.of_nat (length (cantor_stage n))) * third_pow n
  == cantor_cover_measure n.
Proof.
  induction n as [|n IH].
  - cbn [cantor_stage length third_pow cantor_cover_measure]. reflexivity.
  - cbn [cantor_stage]. rewrite flat_split_length.
    cbn [third_pow cantor_cover_measure]. rewrite <- IH.
    rewrite Nat2Z.inj_mul, inject_Z_mult.
    change (inject_Z (Z.of_nat 2)) with 2. ring.
Qed.

(** The point named by x lies in stage n; the Cantor set is the
    intersection of the stages. *)
Definition in_stage (n : nat) (x : RealProcess) : Prop :=
  exists a, In a (cantor_stage n) /\ proc_in_closed x a (a + third_pow n).

Definition in_cantor (x : RealProcess) : Prop := forall n, in_stage n x.

(** Stages are nested. *)
Lemma stage_nested : forall n x, in_stage (S n) x -> in_stage n x.
Proof.
  intros n x [a' [Hin Hx]].
  cbn [cantor_stage] in Hin. apply in_flat_map in Hin.
  destruct Hin as [a [Ha Ha']].
  exists a. split; [exact Ha|].
  assert (Hp := third_pow_pos n).
  cbn [third_pow] in Hx, Ha'.
  unfold split_third in Ha'. cbn [In] in Ha'.
  destruct Ha' as [E | [E | []]]; subst a';
    (eapply proc_in_closed_mono; [| | exact Hx]; lra).
Qed.

(** Membership is a property of the point-class. *)
Lemma in_cantor_equiv : forall x y, x ~~ y -> in_cantor x -> in_cantor y.
Proof.
  intros x y Hxy H n. destruct (H n) as [a [Ha Hx]].
  exists a. split; [exact Ha|].
  apply proc_in_closed_equiv with (x := x); assumption.
Qed.

Lemma zero_in_stage_list : forall n, In 0 (cantor_stage n).
Proof.
  induction n as [|n IH]; [left; reflexivity|].
  cbn [cantor_stage]. apply in_flat_map. exists 0.
  split; [exact IH | left; reflexivity].
Qed.

(** The set is inhabited: 0 lies in every stage. *)
Lemma zero_in_cantor : in_cantor (const_process 0).
Proof.
  intro n. exists 0. split; [apply zero_in_stage_list|].
  assert (H := third_pow_pos n). apply proc_in_closed_const; lra.
Qed.

(** The middle third is removed: 1/2 is outside already at stage 1. *)
Lemma half_not_in_cantor : ~ in_cantor (const_process (1 # 2)).
Proof.
  intro H. destruct (H 1%nat) as [a [Hin Hx]].
  cbn [cantor_stage flat_map split_third app third_pow In] in Hin.
  assert (He : 0 < 1 # 12) by (rewrite Qlt_alt; reflexivity).
  destruct (Hx (1 # 12) He) as [M HM].
  destruct (HM M (Nat.le_refl M)) as [H1 H2]. unfold const_process in H1, H2.
  cbn [third_pow] in H2.
  destruct Hin as [E | [E | []]]; subst a.
  - rewrite Qlt_alt in H2. vm_compute in H2. discriminate H2.
  - rewrite Qlt_alt in H1. vm_compute in H1. discriminate H1.
Qed.

(** The stage as a cover: 2^n segments of length 3^-n, total (2/3)^n,
    containing every point of the set. *)
Theorem cantor_stage_cover : forall n,
  length (cantor_stage n) = Nat.pow 2%nat n /\
  inject_Z (Z.of_nat (Nat.pow 2%nat n)) * third_pow n == cantor_cover_measure n /\
  (forall x, in_cantor x -> in_stage n x).
Proof.
  intro n. split; [apply cantor_stage_count | split].
  - rewrite <- cantor_stage_count. apply cantor_stage_total.
  - intros x Hx. apply Hx.
Qed.

(** The covering process of the Cantor set: stage n, padded by empty
    segments; its length bound is the process (2/3)^n. *)
Theorem cantor_covering_process :
  covering_process in_cantor
    (fun n => list_lo (cantor_stage n))
    (fun n => list_hi (cantor_stage n) (third_pow n))
    cantor_cover_measure.
Proof.
  intro n. assert (Hp := third_pow_pos n). split; [| split].
  - intro k. apply list_cover_le. lra.
  - intros x Hx. destruct (Hx n) as [a [Ha Hin]].
    destruct (list_cover_hit (cantor_stage n) (third_pow n) a Ha) as [k [E1 E2]].
    exists k. rewrite E1, E2. exact Hin.
  - intro N. rewrite <- cantor_stage_total. apply list_cover_sum. lra.
Qed.

(** The Cantor set has measure zero. *)
Theorem cantor_null : null_set in_cantor.
Proof.
  exists (fun n => list_lo (cantor_stage n)),
         (fun n => list_hi (cantor_stage n) (third_pow n)),
         cantor_cover_measure.
  split; [exact cantor_covering_process | exact cantor_measure_zero].
Qed.

Corollary cantor_cover_measure_is_null : PMT.is_null_set cantor_cover_measure.
Proof.
  apply (covering_measure_is_null in_cantor
           (fun n => list_lo (cantor_stage n))
           (fun n => list_hi (cantor_stage n) (third_pow n))).
  - exact cantor_covering_process.
  - exact cantor_measure_zero.
Qed.

(* ===================================================================== *)
(*  6. The points of the Cantor set: codes of digits 0 / 2                *)
(* ===================================================================== *)

(** The m-th approximation of the point with code dg: the digit at place k
    (true = 2, false = 0) contributes 2 * 3^-(k+1). *)
Fixpoint cantor_approx (dg : nat -> bool) (m : nat) : Q :=
  match m with
  | O => 0
  | S k => if dg k then cantor_approx dg k + 2 * third_pow (S k)
           else cantor_approx dg k
  end.

Definition cantor_point (dg : nat -> bool) : RealProcess := cantor_approx dg.

(** The n-th approximation is the left end of a segment of stage n. *)
Lemma cantor_approx_in_stage : forall dg n,
  In (cantor_approx dg n) (cantor_stage n).
Proof.
  intros dg n. induction n as [|n IH].
  - left. reflexivity.
  - cbn [cantor_stage cantor_approx]. apply in_flat_map.
    exists (cantor_approx dg n). split; [exact IH|].
    unfold split_third. destruct (dg n); [right; left; reflexivity | left; reflexivity].
Qed.

Lemma cantor_approx_tail : forall dg n d,
  cantor_approx dg n <= cantor_approx dg (n + d) /\
  cantor_approx dg (n + d) + third_pow (n + d) <= cantor_approx dg n + third_pow n.
Proof.
  intros dg n d. induction d as [|d [IH1 IH2]].
  - rewrite Nat.add_0_r. split; lra.
  - rewrite Nat.add_succ_r. cbn [cantor_approx third_pow].
    assert (Hp := third_pow_pos (n + d)).
    destruct (dg (n + d)%nat); split; lra.
Qed.

(** From place n on, the approximations stay in one segment of stage n. *)
Lemma cantor_approx_window : forall dg n m, (n <= m)%nat ->
  cantor_approx dg n <= cantor_approx dg m /\
  cantor_approx dg m <= cantor_approx dg n + third_pow n.
Proof.
  intros dg n m Hnm.
  replace m with (n + (m - n))%nat by lia.
  destruct (cantor_approx_tail dg n (m - n)) as [H1 H2].
  assert (Hp := third_pow_pos (n + (m - n))). split; lra.
Qed.

Theorem cantor_point_in_stage : forall dg n, in_stage n (cantor_point dg).
Proof.
  intros dg n. exists (cantor_approx dg n). split; [apply cantor_approx_in_stage|].
  intros eps Heps. exists n. intros m Hm.
  destruct (cantor_approx_window dg n m Hm) as [H1 H2].
  unfold cantor_point. split; lra.
Qed.

(** Every code names a point of the Cantor set. *)
Theorem cantor_point_in_cantor : forall dg, in_cantor (cantor_point dg).
Proof. intros dg n. apply cantor_point_in_stage. Qed.

(** ... and the naming process is Cauchy. *)
Theorem cantor_point_Cauchy : forall dg, is_Cauchy (cantor_point dg).
Proof.
  intros dg eps Heps. destruct (third_pow_below eps Heps) as [n Hn].
  exists n. intros m m' Hm Hm'.
  destruct (cantor_approx_window dg n m Hm) as [H1 H2].
  destruct (cantor_approx_window dg n m' Hm') as [H3 H4].
  unfold cantor_point. apply Qabs_Qlt_condition. split; lra.
Qed.

Lemma cantor_approx_agree : forall dg dg' i,
  (forall j, (j < i)%nat -> dg j = dg' j) ->
  cantor_approx dg i = cantor_approx dg' i.
Proof.
  intros dg dg' i. induction i as [|i IH]; intro H; [reflexivity|].
  cbn [cantor_approx]. rewrite (H i) by lia. rewrite IH; [reflexivity|].
  intros j Hj. apply H. lia.
Qed.

(** Codes that agree before place i and split there (2 against 0) name
    approximations at least 3^-(i+1) apart from place i+1 on. *)
Lemma cantor_split_gap : forall dg dg' i,
  (forall j, (j < i)%nat -> dg j = dg' j) -> dg i = true -> dg' i = false ->
  forall m, (i < m)%nat ->
    third_pow (S i) <= cantor_approx dg m - cantor_approx dg' m.
Proof.
  intros dg dg' i Hag Ht Hf m Hm.
  assert (E := cantor_approx_agree dg dg' i Hag).
  destruct (cantor_approx_window dg (S i) m Hm) as [H1 _].
  destruct (cantor_approx_window dg' (S i) m Hm) as [_ H2].
  cbn [cantor_approx] in H1, H2. rewrite Ht in H1. rewrite Hf in H2.
  rewrite E in H1. lra.
Qed.

(** Two codes either agree below n or have a first place of difference. *)
Lemma first_difference : forall (f g : nat -> bool) (n : nat),
  (forall k, (k < n)%nat -> f k = g k) \/
  (exists j, (j < n)%nat /\ (forall k, (k < j)%nat -> f k = g k) /\ f j <> g j).
Proof.
  intros f g n. induction n as [|n [IH | IH]].
  - left. intros k Hk. lia.
  - destruct (bool_dec (f n) (g n)) as [E | NE].
    + left. intros k Hk.
      destruct (Nat.eq_dec k n) as [-> | Hne]; [exact E | apply IH; lia].
    + right. exists n. split; [lia | split; [exact IH | exact NE]].
  - right. destruct IH as [j [Hj [H1 H2]]]. exists j.
    split; [lia | split; assumption].
Qed.

(** Different codes name different points of the continuum. *)
Theorem cantor_points_distinct : forall dg dg' i, dg i <> dg' i ->
  ~ (cantor_point dg ~~ cantor_point dg').
Proof.
  intros dg dg' i Hi Heq.
  destruct (first_difference dg dg' (S i)) as [Hall | [j [_ [Hag Hj]]]].
  - apply Hi. apply Hall. lia.
  - assert (Hp := third_pow_pos (S j)).
    destruct (Heq (third_pow (S j)) Hp) as [N HN].
    specialize (HN (Nat.max N (S j)) (Nat.le_max_l N (S j))).
    unfold cantor_point in HN.
    apply Qabs_Qlt_condition in HN. destruct HN as [HN1 HN2].
    destruct (dg j) eqn:Ej; destruct (dg' j) eqn:Ej'; try (apply Hj; reflexivity).
    + assert (G := cantor_split_gap dg dg' j Hag Ej Ej'
                     (Nat.max N (S j)) ltac:(lia)).
      lra.
    + assert (Hag' : forall k, (k < j)%nat -> dg' k = dg k)
        by (intros k Hk; symmetry; apply Hag; exact Hk).
      assert (G := cantor_split_gap dg' dg j Hag' Ej' Ej
                     (Nat.max N (S j)) ltac:(lia)).
      lra.
Qed.

(** No sequence of codes names all points of the Cantor set: the diagonal
    code names a point of the set different from every listed one. *)
Theorem cantor_points_not_enumerable :
  ~ exists f : nat -> (nat -> bool),
      forall dg : nat -> bool, exists n, cantor_point (f n) ~~ cantor_point dg.
Proof.
  intros [f Hf].
  destruct (Hf (fun k => negb (f k k))) as [n Hn].
  apply (cantor_points_distinct (f n) (fun k => negb (f k k)) n); [| exact Hn].
  cbv beta. destruct (f n n); discriminate.
Qed.

(** Not enumerable -- and of measure zero. *)
Theorem cantor_not_enumerable_and_null :
  null_set in_cantor /\
  (forall dg, in_cantor (cantor_point dg) /\ is_Cauchy (cantor_point dg)) /\
  ~ (exists f : nat -> (nat -> bool),
       forall dg : nat -> bool, exists n, cantor_point (f n) ~~ cantor_point dg).
Proof.
  split; [exact cantor_null | split; [| exact cantor_points_not_enumerable]].
  intro dg. split; [apply cantor_point_in_cantor | apply cantor_point_Cauchy].
Qed.
