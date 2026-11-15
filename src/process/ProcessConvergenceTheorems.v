(** * ProcessConvergenceTheorems.v -- Fatou's inequality, bounds by a majorant, and the place of the residual premise in dominated convergence, as a ToS System

    Elements: the values fs k x of a sequence of functions at rational
              points; grid sums ([ProcessMCT.riemann_sum]) and stage values
              of the integral process ([ProcessLebesgue.lebesgue_process]);
              finite minima ([ProcessFatou.q_min_seq]); the residuals
              int |fs k - f|; a majorant g given as data.
    Roles:    lower envelope of functions / of integrals (the two sides of
              Fatou's inequality); majorant g -- the envelope that bounds
              integrals and residuals; residual -- the indicator of
              closeness; [integrals_converge I J] -- the integrals I k tend
              to J (first the limit along the grid, then along k);
              bad set -- the part of the segment where the convergence is
              not uniform, shown as data together with g.
    Rules:    Fatou: the integral of the lower envelope does not exceed the
              lower envelope of the integrals (on a grid and at every stage
              of the integral process); |int f| <= int g under |f| <= g;
              engine |int f1 - int f2| <= int |f1 - f2| and squeeze, at the
              level of the integral process; on a fixed grid the residual
              premise is equivalent to pointwise convergence at the nodes;
              almost uniform convergence under a majorant makes the
              residuals tend to zero.

    Proved (no axioms):
      - [grid_fatou], [process_fatou_inf], [process_fatou_tail];
      - [lebesgue_abs_le_majorant], [process_fatou_bounded_g],
        [dominated_integral_bound_g];
      - [grid_residual_from_pointwise], [grid_pointwise_from_residual],
        [grid_dct_pointwise]: on a fixed grid nothing infinitary is left;
      - [lebesgue_engine], [lebesgue_envelope], [process_dct_lebesgue]: the
        reduction at the level of the integral process, where the residual
        premise speaks of the limit along the grid;
      - [pointwise_dominated_not_enough], [dct_fails_on_rational_grid]: at
        that level the premise does not follow from pointwise convergence
        under a majorant (even monotone): the indicators of the first k
        rationals;
      - [almost_uniform_residual], [dominated_almost_uniform_convergence]:
        the premise is discharged when the convergence is uniform outside a
        set on which the integral of the majorant is small;
        [uniform_convergence_integral]: the uniform case.

    P4 diagnostic: every statement speaks of finite sums at a stage; the
      lower limit, the limit function and a completed measure are not
      elements. The infinitary step of dominated convergence is located:
      it is the passage from pointwise to almost uniform convergence
      (classically Egorov's theorem over a completed measure). Here the bad
      set is data, as the majorant is.

    NOT claimed:
      - Fatou's lemma for the lower limit (only finite minima, at a stage);
      - dominated convergence from pointwise convergence alone: it is false
        for the integral process over rational nodes
        ([pointwise_dominated_not_enough]);
      - Egorov's theorem (pointwise => almost uniform);
      - an example of almost uniform convergence that is not uniform;
      - anything about the type of integrable functions [L1On].

    STATUS: 37 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessIntegral.
From ToS Require Import process.ProcessSimple.
From ToS Require Import Countability_Q.
From ToS Require process.ProcessMCT.
From ToS Require process.ProcessDCT.
From ToS Require process.ProcessLebesgue.
From ToS Require process.ProcessFatou.
From ToS Require process.ProcessMeasureTheory.
From ToS Require process.ProcessMeasureIntervals.

Open Scope Q_scope.

Module MCT := ToS.process.ProcessMCT.
Module DCT := ToS.process.ProcessDCT.
Module PL := ToS.process.ProcessLebesgue.
Module PF := ToS.process.ProcessFatou.
Module MI := ToS.process.ProcessMeasureIntervals.

(* ===================================================================== *)
(*  1. Fatou's inequality for finite minima                               *)
(* ===================================================================== *)

(** The finite minimum is the greatest lower bound. *)
Lemma q_min_seq_glb : forall (F : nat -> Q) (n : nat) (c : Q),
  (forall k, (k <= n)%nat -> c <= F k) -> c <= PF.q_min_seq F n.
Proof.
  intros F n c H.
  destruct (PF.q_min_seq_exists F n) as [k [Hk Heq]].
  apply Qle_trans with (F k); [ apply H; exact Hk | ].
  rewrite Heq. apply Qle_refl.
Qed.

(** Fatou on a grid: the sum of the minima does not exceed the minimum of
    the sums. *)
Theorem grid_fatou : forall (fs : nat -> Q -> Q) (pts : nat -> Q) (w : Q) (N n : nat),
  0 <= w ->
  MCT.riemann_sum (fun x => PF.q_min_seq (fun k => fs k x) n) pts w N
  <= PF.q_min_seq (fun k => MCT.riemann_sum (fs k) pts w N) n.
Proof.
  intros fs pts w N n Hw. apply q_min_seq_glb. intros k Hk.
  apply MCT.riemann_sum_monotone; [ exact Hw | ].
  intro x. apply (PF.q_min_seq_le (fun j => fs j x) n k Hk).
Qed.

(** Fatou at every stage s of the integral process: the integral of the
    lower envelope of the functions does not exceed the lower envelope of
    the integrals. *)
Theorem process_fatou_inf : forall (fs : nat -> Q -> Q) (a b : Q) (n s : nat),
  a < b ->
  PL.lebesgue_process (fun x => PF.q_min_seq (fun k => fs k x) n) a b s
  <= PF.q_min_seq (fun k => PF.integral_sequence fs a b k s) n.
Proof.
  intros fs a b n s Hab. apply q_min_seq_glb. intros k Hk.
  unfold PF.integral_sequence.
  apply PL.lebesgue_monotone; [ exact Hab | ].
  intro x. apply (PF.q_min_seq_le (fun j => fs j x) n k Hk).
Qed.

(** The tail form (minimum over k in [m, m + n]) -- the one the lower limit
    is made of. *)
Corollary process_fatou_tail : forall (fs : nat -> Q -> Q) (a b : Q) (m n s : nat),
  a < b ->
  PL.lebesgue_process (fun x => PF.q_min_seq (fun k => fs (m + k)%nat x) n) a b s
  <= PF.q_min_seq (fun k => PF.integral_sequence fs a b (m + k)%nat s) n.
Proof.
  intros fs a b m n s Hab.
  exact (process_fatou_inf (fun k => fs (m + k)%nat) a b n s Hab).
Qed.

(* ===================================================================== *)
(*  2. Bounds by a majorant given as a function                           *)
(* ===================================================================== *)

(** |int f| <= int g at every stage, when |f| <= g. *)
Lemma lebesgue_abs_le_majorant : forall (f g : Q -> Q) (a b : Q) (s : nat),
  a < b -> (forall x, Qabs (f x) <= g x) ->
  Qabs (PL.lebesgue_process f a b s) <= PL.lebesgue_process g a b s.
Proof.
  intros f g a b s Hab Hdom.
  apply Qabs_Qle_condition. split.
  - assert (E : - PL.lebesgue_process g a b s
                == PL.lebesgue_process (fun x => (-1) * g x) a b s).
    { rewrite PL.lebesgue_scale. ring. }
    rewrite E. apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (Hdom x) as H. apply Qabs_Qle_condition in H. lra.
  - apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (Hdom x) as H. apply Qabs_Qle_condition in H. lra.
Qed.

(** Under domination the lower envelope of the integrals is bounded by the
    integral of the majorant. *)
Theorem process_fatou_bounded_g : forall (fs : nat -> Q -> Q) (g : Q -> Q) (a b : Q) (n : nat),
  a < b -> (forall k x, Qabs (fs k x) <= g x) ->
  Qabs (PF.q_min_seq (fun k => PF.integral_sequence fs a b k n) n)
  <= PL.lebesgue_process g a b n.
Proof.
  intros fs g a b n Hab Hdom.
  destruct (PF.q_min_seq_exists (fun k => PF.integral_sequence fs a b k n) n) as [k [Hk Heq]].
  rewrite Heq. unfold PF.integral_sequence.
  apply lebesgue_abs_le_majorant; [ exact Hab | intro x; apply Hdom ].
Qed.

(** The difference of two integrals is bounded by the integral of 2g. *)
Theorem dominated_integral_bound_g : forall (f1 f2 g : Q -> Q) (a b : Q) (s : nat),
  a < b -> (forall x, Qabs (f1 x) <= g x) -> (forall x, Qabs (f2 x) <= g x) ->
  Qabs (PL.lebesgue_process f1 a b s - PL.lebesgue_process f2 a b s)
  <= PL.lebesgue_process (fun x => 2 * g x) a b s.
Proof.
  intros f1 f2 g a b s Hab H1 H2.
  assert (A : PL.lebesgue_process f1 a b s
              <= PL.lebesgue_process f2 a b s
                 + PL.lebesgue_process (fun x => 2 * g x) a b s).
  { rewrite <- PL.lebesgue_add.
    apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (H1 x) as P1. pose proof (H2 x) as P2.
    apply Qabs_Qle_condition in P1. apply Qabs_Qle_condition in P2. lra. }
  assert (B : PL.lebesgue_process f2 a b s
              <= PL.lebesgue_process f1 a b s
                 + PL.lebesgue_process (fun x => 2 * g x) a b s).
  { rewrite <- PL.lebesgue_add.
    apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (H1 x) as P1. pose proof (H2 x) as P2.
    apply Qabs_Qle_condition in P1. apply Qabs_Qle_condition in P2. lra. }
  apply Qabs_Qle_condition. split; lra.
Qed.

(** The envelope |f1 - f2| <= 2g follows from |f1| <= g and |f2| <= g. *)
Lemma envelope_from_domination : forall (f1 f2 g : Q -> Q),
  (forall x, Qabs (f1 x) <= g x) -> (forall x, Qabs (f2 x) <= g x) ->
  forall x, Qabs (f1 x - f2 x) <= 2 * g x.
Proof.
  intros f1 f2 g H1 H2 x.
  pose proof (H1 x) as P1. pose proof (H2 x) as P2.
  apply Qabs_Qle_condition in P1. apply Qabs_Qle_condition in P2.
  apply Qabs_Qle_condition. split; lra.
Qed.

(* ===================================================================== *)
(*  3. A fixed grid: the residual premise is pointwise convergence        *)
(* ===================================================================== *)

(** A finite sum of processes that tend to zero tends to zero. *)
Lemma q_sum_null : forall (g : nat -> nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> (fun n => g n i) ~~ const_process 0) ->
  (fun n => MCT.q_sum (g n) N) ~~ const_process 0.
Proof.
  intros g N. induction N as [|k IH]; intros H eps Heps.
  - exists 0%nat. intros n _. unfold const_process. cbn [MCT.q_sum].
    assert (E : (0:Q) - 0 == 0) by ring. rewrite E. exact Heps.
  - assert (He2 : 0 < eps * (1 # 2)) by lra.
    assert (Hk : forall i, (i < k)%nat -> (fun n => g n i) ~~ const_process 0).
    { intros i Hi. apply H. lia. }
    destruct (IH Hk (eps * (1 # 2)) He2) as [N1 HN1].
    destruct (H k (Nat.lt_succ_diag_r k) (eps * (1 # 2)) He2) as [N2 HN2].
    exists (Nat.max N1 N2). intros n Hn.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    specialize (HN1 n Hn1). specialize (HN2 n Hn2).
    unfold const_process in *. cbn [MCT.q_sum].
    assert (E : MCT.q_sum (g n) k + g n k - 0
                == (MCT.q_sum (g n) k - 0) + (g n k - 0)) by ring.
    rewrite E.
    eapply Qle_lt_trans; [ apply Qabs_triangle | ].
    lra.
Qed.

(** Multiplying by a constant weight keeps the tendency to zero. *)
Lemma scale_null : forall (w : Q) (R : RealProcess),
  R ~~ const_process 0 -> (fun n => w * R n) ~~ const_process 0.
Proof.
  intros w R HR eps Heps.
  destruct (Qeq_dec w 0) as [Hw0 | Hw0].
  - exists 0%nat. intros n _. unfold const_process.
    assert (E : w * R n - 0 == 0) by (rewrite Hw0; ring).
    rewrite E. exact Heps.
  - assert (Hwpos : 0 < Qabs w).
    { destruct (Qlt_le_dec 0 (Qabs w)) as [Hp | Hn]; [ exact Hp | ].
      exfalso. apply Hw0.
      assert (Hz : Qabs w == 0) by (pose proof (Qabs_nonneg w); lra).
      pose proof (Qle_Qabs w) as H1. pose proof (Qle_Qabs (- w)) as H2.
      rewrite Qabs_opp in H2. lra. }
    assert (He : 0 < eps / Qabs w) by (apply Qlt_shift_div_l; lra).
    destruct (HR (eps / Qabs w) He) as [N0 HN0].
    exists N0. intros n Hn. specialize (HN0 n Hn). unfold const_process in *.
    assert (E : w * R n - 0 == w * (R n - 0)) by ring.
    rewrite E. rewrite Qabs_Qmult.
    apply Qlt_le_trans with (Qabs w * (eps / Qabs w)).
    + apply Qmult_lt_l; [ exact Hwpos | exact HN0 ].
    + assert (E2 : Qabs w * (eps / Qabs w) == eps) by (field; lra).
      rewrite E2. apply Qle_refl.
Qed.

(** On a fixed grid the residual premise of [ProcessDCT.process_dct]
    follows from pointwise convergence at the nodes -- no majorant. *)
Theorem grid_residual_from_pointwise :
  forall (fs : nat -> Q -> Q) (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  (forall i, (i < N)%nat -> (fun n => fs n (pts i)) ~~ const_process (f (pts i))) ->
  (fun n => MCT.riemann_sum (fun x => Qabs (fs n x - f x)) pts w N)
    ~~ const_process 0.
Proof.
  intros fs f pts w N Hpt.
  unfold MCT.riemann_sum.
  apply (scale_null w
           (fun n => MCT.q_sum (fun i => Qabs (fs n (pts i) - f (pts i))) N)).
  apply (q_sum_null (fun n i => Qabs (fs n (pts i) - f (pts i))) N).
  intros i Hi eps Heps.
  destruct (Hpt i Hi eps Heps) as [N0 HN0].
  exists N0. intros n Hn. specialize (HN0 n Hn). unfold const_process in *.
  assert (E : Qabs (fs n (pts i) - f (pts i)) - 0 == Qabs (fs n (pts i) - f (pts i))) by ring.
  rewrite E. rewrite Qabs_pos by apply Qabs_nonneg. exact HN0.
Qed.

(** Hence on a fixed grid the exchange holds for any pointwise convergent
    sequence, with no residual premise. *)
Theorem grid_dct_pointwise :
  forall (fs : nat -> Q -> Q) (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (forall i, (i < N)%nat -> (fun n => fs n (pts i)) ~~ const_process (f (pts i))) ->
  (fun n => MCT.riemann_sum (fs n) pts w N)
    ~~ const_process (MCT.riemann_sum f pts w N).
Proof.
  intros fs f pts w N Hw Hpt.
  apply DCT.process_dct; [ exact Hw | ].
  apply grid_residual_from_pointwise. exact Hpt.
Qed.

Lemma q_sum_term_le : forall (g : nat -> Q) (N i : nat),
  (forall j, 0 <= g j) -> (i < N)%nat -> g i <= MCT.q_sum g N.
Proof.
  intros g N i Hnn. induction N as [|k IH]; intro Hi; [ lia | ].
  cbn [MCT.q_sum].
  destruct (Nat.eq_dec i k) as [-> | Hne].
  - pose proof (MCT.q_sum_nonneg g k Hnn). lra.
  - assert (Hik : (i < k)%nat) by lia. specialize (IH Hik). pose proof (Hnn k). lra.
Qed.

(** Conversely, for w > 0 the residual premise gives pointwise convergence
    at the nodes: on a fixed grid the two are equivalent. *)
Theorem grid_pointwise_from_residual :
  forall (fs : nat -> Q -> Q) (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 < w ->
  (fun n => MCT.riemann_sum (fun x => Qabs (fs n x - f x)) pts w N)
    ~~ const_process 0 ->
  forall i, (i < N)%nat -> (fun n => fs n (pts i)) ~~ const_process (f (pts i)).
Proof.
  intros fs f pts w N Hw Hres i Hi eps Heps.
  assert (He : 0 < w * eps) by (apply Qmult_lt_0_compat; assumption).
  destruct (Hres (w * eps) He) as [N0 HN0].
  exists N0. intros n Hn. specialize (HN0 n Hn). unfold const_process in *.
  unfold MCT.riemann_sum in HN0.
  set (S := MCT.q_sum (fun j => Qabs (fs n (pts j) - f (pts j))) N) in *.
  assert (HS : Qabs (fs n (pts i) - f (pts i)) <= S).
  { unfold S. apply (q_sum_term_le (fun j => Qabs (fs n (pts j) - f (pts j))) N i);
      [ intro j; apply Qabs_nonneg | exact Hi ]. }
  assert (HS0 : 0 <= S) by (pose proof (Qabs_nonneg (fs n (pts i) - f (pts i))); lra).
  assert (E : w * S - 0 == w * S) by ring. rewrite E in HN0.
  assert (HwS : 0 <= w * S) by (apply Qmult_le_0_compat; lra).
  rewrite Qabs_pos in HN0 by exact HwS.
  assert (HSe : S < eps).
  { apply Qmult_lt_l with (z := w); [ exact Hw | exact HN0 ]. }
  lra.
Qed.

(* ===================================================================== *)
(*  4. The integral process: engine, envelope, squeeze                    *)
(* ===================================================================== *)

(** Engine at every stage: |int f1 - int f2| <= int |f1 - f2|. *)
Lemma lebesgue_engine : forall (f1 f2 : Q -> Q) (a b : Q) (s : nat),
  a < b ->
  Qabs (PL.lebesgue_process f1 a b s - PL.lebesgue_process f2 a b s)
  <= PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s.
Proof.
  intros f1 f2 a b s Hab.
  assert (A : PL.lebesgue_process f1 a b s
              <= PL.lebesgue_process f2 a b s
                 + PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s).
  { rewrite <- PL.lebesgue_add.
    apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (Qle_Qabs (f1 x - f2 x)). lra. }
  assert (B : PL.lebesgue_process f2 a b s
              <= PL.lebesgue_process f1 a b s
                 + PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s).
  { rewrite <- PL.lebesgue_add.
    apply PL.lebesgue_monotone; [ exact Hab | ].
    intro x. pose proof (Qle_Qabs (- (f1 x - f2 x))) as H. rewrite Qabs_opp in H. lra. }
  apply Qabs_Qle_condition. split; lra.
Qed.

(** Envelope at every stage: |f1 - f2| <= 2g gives int |f1 - f2| <= int 2g. *)
Lemma lebesgue_envelope : forall (f1 f2 g : Q -> Q) (a b : Q) (s : nat),
  a < b -> (forall x, Qabs (f1 x - f2 x) <= 2 * g x) ->
  PL.lebesgue_process (fun x => Qabs (f1 x - f2 x)) a b s
  <= PL.lebesgue_process (fun x => 2 * g x) a b s.
Proof.
  intros f1 f2 g a b s Hab Hdom.
  apply PL.lebesgue_monotone; [ exact Hab | exact Hdom ].
Qed.

(** The integrals I k tend to J: for every eps, for all large k, the stage
    values of I k and J differ by less than eps from some stage on. The
    limit along the grid comes first. *)
Definition integrals_converge (I : nat -> RealProcess) (J : RealProcess) : Prop :=
  forall eps, 0 < eps ->
    exists K, forall k, (K <= k)%nat ->
      exists S0, forall s, (S0 <= s)%nat -> Qabs (I k s - J s) < eps.

(** Squeeze at the level of the integral process: if the residuals tend to
    zero, the integrals converge. Here the premise speaks of the limit
    along the grid. *)
Theorem process_dct_lebesgue : forall (fs : nat -> Q -> Q) (f : Q -> Q) (a b : Q),
  a < b ->
  integrals_converge
    (fun k => PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b)
    (const_process 0) ->
  integrals_converge
    (fun k => PL.lebesgue_process (fs k) a b)
    (PL.lebesgue_process f a b).
Proof.
  intros fs f a b Hab Hres eps Heps.
  destruct (Hres eps Heps) as [K HK]. exists K. intros k Hk.
  destruct (HK k Hk) as [S0 HS0]. exists S0. intros s Hs.
  specialize (HS0 s Hs). unfold const_process in HS0.
  set (r := PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b s) in *.
  assert (Hr : Qabs (PL.lebesgue_process (fs k) a b s - PL.lebesgue_process f a b s) <= r).
  { unfold r. apply lebesgue_engine. exact Hab. }
  assert (Hr2 : r <= Qabs (r - 0)).
  { assert (E : r - 0 == r) by ring. rewrite E. apply Qle_Qabs. }
  lra.
Qed.

(* ===================================================================== *)
(*  5. Pointwise convergence under a majorant is not enough               *)
(* ===================================================================== *)

(** How many of the first k members of e equal x. *)
Fixpoint hit_sum (e : nat -> Q) (k : nat) (x : Q) : Q :=
  match k with
  | O => 0
  | S j => hit_sum e j x + indicator (e j) (e j) x
  end.

Lemma hit_sum_nonneg : forall e k x, 0 <= hit_sum e k x.
Proof.
  intros e k x. induction k as [| k IH]; cbn [hit_sum].
  - apply Qle_refl.
  - pose proof (indicator_bounded (e k) (e k) x) as [H0 _]. lra.
Qed.

Lemma hit_sum_mono : forall e k x, hit_sum e k x <= hit_sum e (S k) x.
Proof.
  intros e k x. cbn [hit_sum].
  pose proof (indicator_bounded (e k) (e k) x) as [H0 _]. lra.
Qed.

Lemma hit_sum_reaches : forall e j k x, (j < k)%nat -> e j == x -> 1 <= hit_sum e k x.
Proof.
  intros e j k x Hjk Hx. induction k as [| k IH]; [ lia | ].
  cbn [hit_sum].
  destruct (Nat.eq_dec j k) as [Heq | Hne].
  - subst k. pose proof (hit_sum_nonneg e j x) as Hn.
    assert (E : indicator (e j) (e j) x == 1).
    { apply indicator_inside; rewrite Hx; apply Qle_refl. }
    lra.
  - assert (Hlt : (j < k)%nat) by lia. specialize (IH Hlt).
    pose proof (indicator_bounded (e k) (e k) x) as [H0 _]. lra.
Qed.

(** The indicator of the first k members of e: 1 at x when x is one of
    e 0, ..., e (k - 1), and 0 otherwise. *)
Definition first_ind (e : nat -> Q) (k : nat) (x : Q) : Q :=
  if Qle_bool 1 (hit_sum e k x) then 1 else 0.

Lemma first_ind_cases : forall e k x,
  (1 <= hit_sum e k x /\ first_ind e k x = 1) \/
  (hit_sum e k x < 1 /\ first_ind e k x = 0).
Proof.
  intros e k x. unfold first_ind. destruct (Qle_bool 1 (hit_sum e k x)) eqn:E.
  - left. split; [ apply Qle_bool_iff; exact E | reflexivity ].
  - right. split; [ | reflexivity ].
    destruct (Qlt_le_dec (hit_sum e k x) 1) as [H | H]; [ exact H | ].
    apply Qle_bool_iff in H. rewrite H in E. discriminate.
Qed.

Lemma first_ind_nonneg : forall e k x, 0 <= first_ind e k x.
Proof.
  intros e k x. destruct (first_ind_cases e k x) as [[_ E] | [_ E]]; rewrite E; lra.
Qed.

Lemma first_ind_le_one : forall e k x, first_ind e k x <= 1.
Proof.
  intros e k x. destruct (first_ind_cases e k x) as [[_ E] | [_ E]]; rewrite E; lra.
Qed.

Lemma first_ind_le_hit : forall e k x, first_ind e k x <= hit_sum e k x.
Proof.
  intros e k x. pose proof (hit_sum_nonneg e k x) as Hn.
  destruct (first_ind_cases e k x) as [[H E] | [H E]]; rewrite E; lra.
Qed.

Lemma first_ind_mono : forall e k x, first_ind e k x <= first_ind e (S k) x.
Proof.
  intros e k x. pose proof (hit_sum_mono e k x) as Hm.
  destruct (first_ind_cases e k x) as [[H1 E1] | [H1 E1]];
  destruct (first_ind_cases e (S k) x) as [[H2 E2] | [H2 E2]];
    rewrite E1, E2; lra.
Qed.

(** At every point that e reaches, the indicators tend to 1. *)
Lemma first_ind_pointwise : forall e x, (exists j, e j == x) ->
  (fun k => first_ind e k x) ~~ const_process 1.
Proof.
  intros e x [j Hj] eps Heps. exists (S j). intros k Hk. unfold const_process.
  destruct (first_ind_cases e k x) as [[H E] | [H E]]; rewrite E.
  - assert (E0 : (1:Q) - 1 == 0) by ring. rewrite E0. exact Heps.
  - exfalso. assert (Hjk : (j < k)%nat) by lia.
    pose proof (hit_sum_reaches e j k x Hjk Hj). lra.
Qed.

Lemma riemann_process_zero : forall a b s, a < b ->
  riemann_process (fun _ : Q => 0) a b s == 0.
Proof.
  intros a b s Hab.
  pose proof (riemann_process_scale 0 (fun _ : Q => 1) a b s) as Hs. cbv beta in Hs.
  assert (H1 : riemann_process (fun _ : Q => 0) a b s
               <= riemann_process (fun _ : Q => 0 * 1) a b s)
    by (apply riemann_process_monotone; [ exact Hab | intro x; lra ]).
  assert (H2 : riemann_process (fun _ : Q => 0 * 1) a b s
               <= riemann_process (fun _ : Q => 0) a b s)
    by (apply riemann_process_monotone; [ exact Hab | intro x; lra ]).
  lra.
Qed.

Lemma nat_Q_nonneg : forall n : nat, 0 <= inject_Z (Z.of_nat n).
Proof. intro n. unfold Qle. simpl. lia. Qed.

(** Every point costs at most one grid step, so the stage sum of the first
    k points is at most k grid steps. *)
Lemma hit_sum_riemann : forall e k a b s, a < b ->
  riemann_process (hit_sum e k) a b s <= inject_Z (Z.of_nat k) * integral_step a b s.
Proof.
  intros e k a b s Hab. induction k as [| k IH].
  - change (hit_sum e 0) with (fun _ : Q => 0).
    rewrite (riemann_process_zero a b s Hab).
    assert (E : inject_Z (Z.of_nat 0) * integral_step a b s == 0) by (simpl; ring).
    rewrite E. apply Qle_refl.
  - pose proof (riemann_process_add (hit_sum e k) (indicator (e k) (e k)) a b s) as Hadd.
    change (fun x : Q => hit_sum e k x + indicator (e k) (e k) x)
      with (hit_sum e (S k)) in Hadd.
    pose proof (MI.measure_process_point_le_step a b (e k) s Hab) as Hpt.
    unfold ProcessMeasureTheory.measure_process, indicator_process in Hpt.
    assert (E : inject_Z (Z.of_nat (S k)) * integral_step a b s ==
                inject_Z (Z.of_nat k) * integral_step a b s + integral_step a b s).
    { rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. ring. }
    rewrite E, Hadd. lra.
Qed.

(** The integral of the indicator of the first k members is zero. *)
Lemma first_ind_integral_null : forall e k a b, a < b ->
  PL.lebesgue_process (first_ind e k) a b ~~ const_process 0.
Proof.
  intros e k a b Hab eps Heps.
  pose proof (nat_Q_nonneg k) as Hc.
  set (c := inject_Z (Z.of_nat k)) in *.
  assert (Hd : 0 < eps / (c + 1)) by (apply Qlt_shift_div_l; lra).
  destruct (integral_step_eventually_small a b (eps / (c + 1)) Hab Hd) as [N HN].
  exists N. intros s Hs. unfold const_process. specialize (HN s Hs).
  assert (H0 : 0 <= PL.lebesgue_process (first_ind e k) a b s).
  { apply PL.lebesgue_nonneg; [ exact Hab | intro x; apply first_ind_nonneg ]. }
  assert (H1 : PL.lebesgue_process (first_ind e k) a b s <= c * integral_step a b s).
  { apply Qle_trans with (PL.lebesgue_process (hit_sum e k) a b s).
    - apply PL.lebesgue_monotone; [ exact Hab | intro x; apply first_ind_le_hit ].
    - unfold c. exact (hit_sum_riemann e k a b s Hab). }
  pose proof (integral_step_pos a b s Hab) as Hp.
  assert (H2 : (c + 1) * integral_step a b s < (c + 1) * (eps / (c + 1))).
  { apply Qmult_lt_l; [ lra | exact HN ]. }
  assert (H3 : (c + 1) * (eps / (c + 1)) == eps) by (field; lra).
  assert (H4 : (c + 1) * integral_step a b s ==
               c * integral_step a b s + integral_step a b s) by ring.
  assert (E : PL.lebesgue_process (first_ind e k) a b s - 0 ==
              PL.lebesgue_process (first_ind e k) a b s) by ring.
  rewrite E. rewrite Qabs_pos by exact H0. lra.
Qed.

Lemma one_integral : PL.lebesgue_process (fun _ : Q => 1) 0 1 ~~ const_process 1.
Proof.
  assert (H01 : 0 < 1) by lra.
  intros eps Heps. destruct (PL.lebesgue_const 1 0 1 H01 eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn). unfold const_process in *.
  assert (E : (1:Q) * (1 - 0) == 1) by ring. rewrite E in HN. exact HN.
Qed.

(** Pointwise convergence under a majorant -- even monotone -- does not
    give the convergence of the integrals of the integral process: the
    indicators of the first k rationals grow to the constant 1 at every
    rational point, are bounded by the majorant 1, each has integral 0, and
    the limit has integral 1. *)
Theorem pointwise_dominated_not_enough :
  exists (fs : nat -> Q -> Q) (f g : Q -> Q),
    (forall k x, fs k x <= fs (S k) x) /\
    (forall k x, Qabs (fs k x) <= g x) /\
    (forall x, (fun k => fs k x) ~~ const_process (f x)) /\
    (forall k, PL.lebesgue_process (fs k) 0 1 ~~ const_process 0) /\
    PL.lebesgue_process g 0 1 ~~ const_process 1 /\
    PL.lebesgue_process f 0 1 ~~ const_process 1.
Proof.
  exists (first_ind enum_Q), (fun _ => 1), (fun _ => 1).
  split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - intros k x. apply first_ind_mono.
  - intros k x. rewrite Qabs_pos by apply first_ind_nonneg. apply first_ind_le_one.
  - intro x. apply first_ind_pointwise. apply Q_countable.
  - intro k. apply first_ind_integral_null. lra.
  - exact one_integral.
  - exact one_integral.
Qed.

(** In the terms of section 4: for this sequence the integrals do not
    converge to the integral of the limit. *)
Corollary dct_fails_on_rational_grid :
  ~ integrals_converge (fun k => PL.lebesgue_process (first_ind enum_Q k) 0 1)
                       (PL.lebesgue_process (fun _ : Q => 1) 0 1).
Proof.
  intro H.
  assert (H01 : (0:Q) < 1) by lra.
  assert (Hh : 0 < 1 # 2) by (rewrite Qlt_alt; reflexivity).
  assert (Hq : 0 < 1 # 4) by (rewrite Qlt_alt; reflexivity).
  destruct (H (1 # 2) Hh) as [K HK].
  destruct (HK K (Nat.le_refl K)) as [S0 HS0].
  destruct (first_ind_integral_null enum_Q K 0 1 H01 (1 # 4) Hq) as [N1 HN1].
  destruct (one_integral (1 # 4) Hq) as [N2 HN2].
  assert (Hs0 : (S0 <= Nat.max S0 (Nat.max N1 N2))%nat) by lia.
  assert (Hs1 : (N1 <= Nat.max S0 (Nat.max N1 N2))%nat) by lia.
  assert (Hs2 : (N2 <= Nat.max S0 (Nat.max N1 N2))%nat) by lia.
  specialize (HS0 _ Hs0). specialize (HN1 _ Hs1). specialize (HN2 _ Hs2).
  unfold const_process in HN1, HN2.
  apply Qabs_Qlt_condition in HS0. apply Qabs_Qlt_condition in HN1.
  apply Qabs_Qlt_condition in HN2.
  set (I := PL.lebesgue_process (first_ind enum_Q K) 0 1 (Nat.max S0 (Nat.max N1 N2))) in *.
  set (J := PL.lebesgue_process (fun _ : Q => 1) 0 1 (Nat.max S0 (Nat.max N1 N2))) in *.
  lra.
Qed.

(* ===================================================================== *)
(*  6. Where the premise is discharged: almost uniform convergence        *)
(* ===================================================================== *)

(** The convergence fs n -> f is uniform outside a "bad" set on which the
    integral of the majorant is small; the bad set is shown as data. Then
    the residuals tend to zero. *)
Theorem almost_uniform_residual :
  forall (fs : nat -> Q -> Q) (f g : Q -> Q) (a b : Q),
  a < b ->
  (forall n x, Qabs (fs n x - f x) <= 2 * g x) ->
  (forall delta, 0 < delta ->
     exists (bad : Q -> bool) (S0 : nat),
       (forall s, (S0 <= s)%nat ->
          PL.lebesgue_process (fun x => if bad x then 2 * g x else 0) a b s < delta) /\
       (forall eta, 0 < eta -> exists N, forall n, (N <= n)%nat ->
          forall x, bad x = false -> Qabs (fs n x - f x) <= eta)) ->
  integrals_converge
    (fun k => PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b)
    (const_process 0).
Proof.
  intros fs f g a b Hab Henv Hau eps Heps.
  assert (Hba : 0 < b - a) by lra.
  assert (Hd : 0 < eps / 2) by (apply Qlt_shift_div_l; lra).
  destruct (Hau (eps / 2) Hd) as [bad [S0 [Hbad Hunif]]].
  assert (He : 0 < eps / 2 / (b - a)) by (apply Qlt_shift_div_l; lra).
  destruct (Hunif (eps / 2 / (b - a)) He) as [N HN].
  exists N. intros k Hk. exists S0. intros s Hs. unfold const_process.
  specialize (Hbad s Hs).
  assert (Eeta : eps / 2 / (b - a) * (b - a) == eps / 2) by (field; lra).
  set (eta := eps / 2 / (b - a)) in *.
  assert (Hpt : forall x, Qabs (fs k x - f x) <= (if bad x then 2 * g x else 0) + eta).
  { intro x. destruct (bad x) eqn:Eb.
    - pose proof (Henv k x). lra.
    - pose proof (HN k Hk x Eb). lra. }
  assert (Hle : PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b s
                <= PL.lebesgue_process (fun x => if bad x then 2 * g x else 0) a b s
                   + PL.lebesgue_process (fun _ => eta) a b s).
  { rewrite <- PL.lebesgue_add.
    apply PL.lebesgue_monotone; [ exact Hab | ]. intro x. cbv beta. apply Hpt. }
  assert (Hconst : PL.lebesgue_process (fun _ => eta) a b s <= eta * (b - a)).
  { apply Qle_trans with (Qabs (PL.lebesgue_process (fun _ => eta) a b s));
      [ apply Qle_Qabs | ].
    apply PL.lebesgue_bounded; [ exact Hab | | lra ].
    intro x. rewrite Qabs_pos by lra. apply Qle_refl. }
  assert (H0 : 0 <= PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b s).
  { apply PL.lebesgue_nonneg; [ exact Hab | intro x; apply Qabs_nonneg ]. }
  assert (E : PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b s - 0 ==
              PL.lebesgue_process (fun x => Qabs (fs k x - f x)) a b s) by ring.
  rewrite E. rewrite Qabs_pos by exact H0.
  assert (Ehalf : eps / 2 + eps / 2 == eps) by field.
  set (h := eps / 2) in *.
  lra.
Qed.

(** Dominated convergence with the infinitary step shown as data: if
    |fs n| <= g, |f| <= g and the convergence is uniform outside sets on
    which the integral of 2g is arbitrarily small, the integrals converge. *)
Theorem dominated_almost_uniform_convergence :
  forall (fs : nat -> Q -> Q) (f g : Q -> Q) (a b : Q),
  a < b ->
  (forall n x, Qabs (fs n x) <= g x) ->
  (forall x, Qabs (f x) <= g x) ->
  (forall delta, 0 < delta ->
     exists (bad : Q -> bool) (S0 : nat),
       (forall s, (S0 <= s)%nat ->
          PL.lebesgue_process (fun x => if bad x then 2 * g x else 0) a b s < delta) /\
       (forall eta, 0 < eta -> exists N, forall n, (N <= n)%nat ->
          forall x, bad x = false -> Qabs (fs n x - f x) <= eta)) ->
  integrals_converge
    (fun k => PL.lebesgue_process (fs k) a b)
    (PL.lebesgue_process f a b).
Proof.
  intros fs f g a b Hab Hdom Hf Hau.
  apply process_dct_lebesgue; [ exact Hab | ].
  apply (almost_uniform_residual fs f g a b Hab); [ | exact Hau ].
  intros n x. apply (envelope_from_domination (fs n) f g (Hdom n) Hf x).
Qed.

(** The uniform case: with an explicit bound e n -> 0 the integrals
    converge uniformly in the stage of the grid. *)
Theorem uniform_convergence_integral :
  forall (fs : nat -> Q -> Q) (f : Q -> Q) (e : nat -> Q) (a b : Q),
  a < b ->
  (forall n, 0 <= e n) ->
  (forall n x, Qabs (fs n x - f x) <= e n) ->
  e ~~ const_process 0 ->
  forall eps, 0 < eps ->
    exists N0, forall n, (N0 <= n)%nat -> forall s,
      Qabs (PL.lebesgue_process (fs n) a b s - PL.lebesgue_process f a b s) < eps.
Proof.
  intros fs f e a b Hab He Hunif Hnull eps Heps.
  assert (Hba : 0 < b - a) by lra.
  assert (He' : 0 < eps / (b - a)) by (apply Qlt_shift_div_l; lra).
  destruct (Hnull (eps / (b - a)) He') as [N0 HN0].
  exists N0. intros n Hn s. specialize (HN0 n Hn). unfold const_process in HN0.
  assert (E : e n - 0 == e n) by ring. rewrite E in HN0.
  rewrite Qabs_pos in HN0 by apply He.
  apply Qle_lt_trans with (e n * (b - a)).
  - apply PL.lebesgue_diff_bound;
      [ exact Hab | intro x; apply Hunif | apply He ].
  - apply Qlt_le_trans with (eps / (b - a) * (b - a)).
    + apply Qmult_lt_r; [ exact Hba | exact HN0 ].
    + assert (E2 : eps / (b - a) * (b - a) == eps) by (field; lra).
      rewrite E2. apply Qle_refl.
Qed.

(** The uniform case is an instance of almost uniform convergence: the bad
    set is empty. *)
Corollary uniform_is_almost_uniform :
  forall (fs : nat -> Q -> Q) (f g : Q -> Q) (e : nat -> Q) (a b : Q),
  a < b ->
  (forall n x, Qabs (fs n x - f x) <= e n) ->
  e ~~ const_process 0 ->
  forall delta, 0 < delta ->
    exists (bad : Q -> bool) (S0 : nat),
      (forall s, (S0 <= s)%nat ->
         PL.lebesgue_process (fun x => if bad x then 2 * g x else 0) a b s < delta) /\
      (forall eta, 0 < eta -> exists N, forall n, (N <= n)%nat ->
         forall x, bad x = false -> Qabs (fs n x - f x) <= eta).
Proof.
  intros fs f g e a b Hab Hunif Hnull delta Hdelta.
  exists (fun _ => false), 0%nat. split.
  - intros s _.
    change (PL.lebesgue_process (fun _ : Q => 0) a b s < delta).
    unfold PL.lebesgue_process. rewrite (riemann_process_zero a b s Hab). exact Hdelta.
  - intros eta Heta. destruct (Hnull eta Heta) as [N HN].
    exists N. intros n Hn x _. specialize (HN n Hn). unfold const_process in HN.
    apply Qabs_Qlt_condition in HN.
    pose proof (Hunif n x). lra.
Qed.
