(* ========================================================================= *)
(*        RIEMANN INTEGRATION — SUMS, FTC, INTEGRAL COMPARISON              *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Define Riemann sums on walk-point grids and prove:             *)
(*    - Linearity, monotonicity, bounds for Riemann sums                    *)
(*    - Telescoping sum collapse (Leibniz-exact)                            *)
(*    - Fundamental Theorem of Calculus (grid version)                      *)
(*    - FTC applications: constant, affine, nonneg, linearity, comparison   *)
(*    - udiff closure under addition and scaling                            *)
(*                                                                          *)
(*  AXIOMS: none (fully constructive)                                       *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import EVT_idx.
From ToS Require Import Differentiation.
From ToS Require Import MeanValueTheorem.

Open Scope Q_scope.

(* ========================================================================= *)
(* DEFINITIONS                                                                *)
(* ========================================================================= *)

(** Left Riemann sum on uniform walk-point grid:
    RS(f, a, step, n) = Σ_{k=0}^{n-1} f(walk_point a step k) * step *)
Fixpoint riemann_sum (f : Q -> Q) (a step : Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => f (walk_point a step n') * step + riemann_sum f a step n'
  end.

(** Telescoping sum: Σ_{k=0}^{n-1} [f(y_{k+1}) - f(y_k)] *)
Fixpoint tele_sum (f : Q -> Q) (a step : Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S n' => (f (walk_point a step n) - f (walk_point a step n')) + tele_sum f a step n'
  end.

(* ========================================================================= *)
(* SECTION 1: RIEMANN SUM INFRASTRUCTURE                                     *)
(* ========================================================================= *)

(** L1: Riemann sum of constant function *)
Lemma riemann_sum_const : forall (c a step : Q) (n : nat),
  riemann_sum (fun _ => c) a step n == c * inject_Z (Z.of_nat n) * step.
Proof.
  intros c a step n. induction n as [| n' IH].
  - simpl. ring.
  - simpl riemann_sum. rewrite IH.
    assert (Hinj : inject_Z (Z.of_nat (S n')) == inject_Z (Z.of_nat n') + 1).
    { replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
    rewrite Hinj. ring.
Qed.

(** L2: Riemann sum distributes over addition *)
Lemma riemann_sum_add : forall (f g : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => f x + g x) a step n ==
  riemann_sum f a step n + riemann_sum g a step n.
Proof.
  intros f g a step n. induction n as [| n' IH].
  - simpl. ring.
  - simpl riemann_sum. rewrite IH. ring.
Qed.

(** L3: Riemann sum scales by constant *)
Lemma riemann_sum_scale : forall (c : Q) (f : Q -> Q) (a step : Q) (n : nat),
  riemann_sum (fun x => c * f x) a step n == c * riemann_sum f a step n.
Proof.
  intros c f a step n. induction n as [| n' IH].
  - simpl. ring.
  - simpl riemann_sum. rewrite IH. ring.
Qed.

(** L4: Riemann sum of nonneg function with nonneg step is nonneg *)
Lemma riemann_sum_nonneg : forall (f : Q -> Q) (a step : Q) (n : nat),
  (forall k : nat, (k < n)%nat -> 0 <= f (walk_point a step k)) ->
  0 <= step ->
  0 <= riemann_sum f a step n.
Proof.
  intros f a step n Hf Hstep.
  induction n as [| n' IH].
  - simpl. lra.
  - simpl riemann_sum.
    assert (Hn' : forall k : nat, (k < n')%nat -> 0 <= f (walk_point a step k)).
    { intros k Hk. apply Hf. lia. }
    assert (IHr := IH Hn').
    assert (Hfn : 0 <= f (walk_point a step n')).
    { apply Hf. lia. }
    assert (Hterm : 0 <= f (walk_point a step n') * step).
    { apply Qmult_le_0_compat; assumption. }
    lra.
Qed.

(** L5: Riemann sum is monotone in function values *)
Lemma riemann_sum_monotone : forall (f g : Q -> Q) (a step : Q) (n : nat),
  (forall k : nat, (k < n)%nat -> f (walk_point a step k) <= g (walk_point a step k)) ->
  0 <= step ->
  riemann_sum f a step n <= riemann_sum g a step n.
Proof.
  intros f g a step n Hfg Hstep.
  induction n as [| n' IH].
  - simpl. lra.
  - simpl riemann_sum.
    assert (Hn' : forall k : nat, (k < n')%nat -> f (walk_point a step k) <= g (walk_point a step k)).
    { intros k Hk. apply Hfg. lia. }
    assert (IHr := IH Hn').
    assert (Hfgn : f (walk_point a step n') <= g (walk_point a step n')).
    { apply Hfg. lia. }
    assert (Hterm : f (walk_point a step n') * step <= g (walk_point a step n') * step).
    { apply Qmult_le_compat_r; assumption. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: RIEMANN SUM BOUNDS                                             *)
(* ========================================================================= *)

(** L6: Absolute value bound for Riemann sum *)
Lemma riemann_sum_abs_bound : forall (f : Q -> Q) (a step : Q) (n : nat) (M : Q),
  (forall k : nat, (k < n)%nat -> Qabs (f (walk_point a step k)) <= M) ->
  0 <= step ->
  0 <= M ->
  Qabs (riemann_sum f a step n) <= M * inject_Z (Z.of_nat n) * step.
Proof.
  intros f a step n M Hf Hstep HM.
  induction n as [| n' IH].
  - simpl riemann_sum. simpl Z.of_nat.
    assert (H1 : Qabs 0 == 0) by reflexivity.
    assert (H2 : M * inject_Z 0 * step == 0) by ring.
    lra.
  - simpl riemann_sum.
    assert (Hn' : forall k : nat, (k < n')%nat -> Qabs (f (walk_point a step k)) <= M).
    { intros k Hk. apply Hf. lia. }
    assert (IHr := IH Hn').
    apply Qle_trans with (Qabs (f (walk_point a step n') * step) + Qabs (riemann_sum f a step n')).
    + apply Qabs_triangle.
    + assert (Hfn : Qabs (f (walk_point a step n')) <= M).
      { apply Hf. lia. }
      assert (Hterm : Qabs (f (walk_point a step n') * step) <= M * step).
      { rewrite Qabs_Qmult.
        apply Qle_trans with (M * Qabs step).
        - apply Qmult_le_compat_r; [exact Hfn | apply Qabs_nonneg].
        - assert (Habss : Qabs step == step) by (apply Qabs_pos; assumption).
          setoid_rewrite Habss. lra. }
      assert (Hinj : inject_Z (Z.of_nat (S n')) == inject_Z (Z.of_nat n') + 1).
      { replace (Z.of_nat (S n')) with (Z.of_nat n' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : M * (inject_Z (Z.of_nat n') + 1) * step ==
                        M * step + M * inject_Z (Z.of_nat n') * step) by ring.
      rewrite Hinj. lra.
Qed.

(** L7: Total width equals n * step *)
Lemma riemann_sum_width : forall (a step : Q) (n : nat),
  riemann_sum (fun _ => 1) a step n == inject_Z (Z.of_nat n) * step.
Proof.
  intros a step n.
  assert (H := riemann_sum_const 1 a step n).
  setoid_rewrite H. ring.
Qed.

(** L8: Global bound: lo*width <= RS <= hi*width *)
Lemma riemann_sum_global_bound : forall (f : Q -> Q) (a step : Q) (n : nat) (lo hi : Q),
  (forall k : nat, (k < n)%nat ->
    lo <= f (walk_point a step k) /\ f (walk_point a step k) <= hi) ->
  0 <= step ->
  lo * inject_Z (Z.of_nat n) * step <= riemann_sum f a step n /\
  riemann_sum f a step n <= hi * inject_Z (Z.of_nat n) * step.
Proof.
  intros f a step n lo hi Hfbd Hstep.
  split.
  - (* lo * n * step <= RS(f) *)
    assert (Hlo_le : riemann_sum (fun _ => lo) a step n <= riemann_sum f a step n).
    { apply riemann_sum_monotone; [| exact Hstep].
      intros k Hk. destruct (Hfbd k Hk). exact H. }
    assert (Hlo_eq : riemann_sum (fun _ => lo) a step n == lo * inject_Z (Z.of_nat n) * step).
    { apply riemann_sum_const. }
    lra.
  - (* RS(f) <= hi * n * step *)
    assert (Hhi_le : riemann_sum f a step n <= riemann_sum (fun _ => hi) a step n).
    { apply riemann_sum_monotone; [| exact Hstep].
      intros k Hk. destruct (Hfbd k Hk). exact H0. }
    assert (Hhi_eq : riemann_sum (fun _ => hi) a step n == hi * inject_Z (Z.of_nat n) * step).
    { apply riemann_sum_const. }
    lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: TELESCOPING                                                     *)
(* ========================================================================= *)

(** L9: Telescoping sum collapses *)
Lemma telescope_collapse : forall (f : Q -> Q) (a step : Q) (n : nat),
  tele_sum f a step n == f (walk_point a step n) - f a.
Proof.
  intros f a step n. induction n as [| n' IH].
  - simpl. ring.
  - assert (Hstep : tele_sum f a step (S n') ==
              (f (walk_point a step (S n')) - f (walk_point a step n')) +
              tele_sum f a step n') by reflexivity.
    lra.
Qed.

(** L10: Error bound — direct inductive proof *)
Lemma rs_tele_error_bound : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum f' a step (S N) - tele_sum f a step (S N)) <= eps * (b - a).
Proof.
  intros f f' a b eps [Hab Hudiff] Heps.
  assert (Hba : 0 < b - a) by lra.
  destruct (Hudiff eps Heps) as [delta [Hdelta Hbd]].
  destruct (walk_step_small a b delta Hab Hdelta) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_lt : Qabs step < delta).
  { rewrite Hstep_abs. exact HN. }
  (* Inner induction: |RS(f', k) - tele(f, k)| <= k * eps * step *)
  assert (Hmain : forall k : nat, (k <= S N)%nat ->
    Qabs (riemann_sum f' a step k - tele_sum f a step k) <=
    inject_Z (Z.of_nat k) * eps * step).
  { induction k as [| k' IHk].
    - intros _. simpl riemann_sum. simpl tele_sum. simpl Z.of_nat.
      assert (Hdiff : (0 : Q) - 0 == 0) by ring.
      qabs_rw Hdiff.
      assert (H1 : Qabs 0 == 0) by reflexivity.
      assert (H2 : inject_Z 0 * eps * step == 0) by ring.
      lra.
    - intros Hk. assert (Hk' : (k' <= S N)%nat) by lia.
      specialize (IHk Hk').
      (* Decompose RS and tele at S k' *)
      assert (HRS : riemann_sum f' a step (S k') ==
                     f' (walk_point a step k') * step + riemann_sum f' a step k')
        by reflexivity.
      assert (HTS : tele_sum f a step (S k') ==
                     (f (walk_point a step (S k')) - f (walk_point a step k')) +
                     tele_sum f a step k')
        by reflexivity.
      assert (Hdiff : riemann_sum f' a step (S k') - tele_sum f a step (S k') ==
                        (f' (walk_point a step k') * step -
                         (f (walk_point a step (S k')) - f (walk_point a step k'))) +
                        (riemann_sum f' a step k' - tele_sum f a step k')).
      { lra. }
      (* Error term for step k' *)
      assert (HWP : walk_point a step (S k') = walk_point a step k' + step)
        by reflexivity.
      assert (Herr_eq : f' (walk_point a step k') * step -
                          (f (walk_point a step (S k')) - f (walk_point a step k')) ==
                        -(f (walk_point a step k' + step) - f (walk_point a step k') -
                           f' (walk_point a step k') * step)).
      { rewrite HWP. ring. }
      (* Bound single step error *)
      assert (Hin : a <= walk_point a step k' /\ walk_point a step k' <= b).
      { apply walk_point_in_interval; [exact Hab | exact Hk']. }
      destruct Hin as [Hlo_k Hhi_k].
      assert (Hstep_err : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                                  f' (walk_point a step k') * step) < eps * Qabs step).
      { apply Hbd; assumption. }
      assert (Hstep_err2 : Qabs (f (walk_point a step k' + step) - f (walk_point a step k') -
                                   f' (walk_point a step k') * step) < eps * step).
      { assert (Heq : eps * Qabs step == eps * step) by (rewrite Hstep_abs; reflexivity).
        lra. }
      assert (Herr_abs : Qabs (f' (walk_point a step k') * step -
                                 (f (walk_point a step (S k')) - f (walk_point a step k'))) < eps * step).
      { qabs_rw Herr_eq.
        rewrite Qabs_opp. exact Hstep_err2. }
      (* Triangle inequality *)
      apply Qle_trans with (Qabs (f' (walk_point a step k') * step -
                                    (f (walk_point a step (S k')) - f (walk_point a step k'))) +
                             Qabs (riemann_sum f' a step k' - tele_sum f a step k')).
      { qabs_rw Hdiff. apply Qabs_triangle. }
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      assert (Hring : (inject_Z (Z.of_nat k') + 1) * eps * step ==
                        eps * step + inject_Z (Z.of_nat k') * eps * step) by ring.
      rewrite Hinj. lra. }
  specialize (Hmain (S N) (Nat.le_refl _)).
  assert (Hcancel : inject_Z (Z.of_nat (S N)) * eps * step == eps * (b - a)).
  { unfold step. field.
    intros Hcontra.
    assert (HSN_pos : 0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. }
    lra. }
  setoid_rewrite Hcancel in Hmain. exact Hmain.
Qed.

(* ========================================================================= *)
(* SECTION 4: FUNDAMENTAL THEOREM OF CALCULUS                                 *)
(* ========================================================================= *)

(** L11: FTC — Riemann sum of f' approximates f(end) - f(a) *)
Lemma ftc_grid : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a)) <=
    eps * (b - a).
Proof.
  intros f f' a b eps Hudiff Heps.
  destruct (rs_tele_error_bound f f' a b eps Hudiff Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  assert (Htele : tele_sum f a step (S N) == f (walk_point a step (S N)) - f a).
  { apply telescope_collapse. }
  set (X := riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a)).
  set (Y := riemann_sum f' a step (S N) - tele_sum f a step (S N)).
  assert (HXY : X == Y) by (unfold X, Y; lra).
  (* Prove Qabs X <= Qabs Y via case analysis, then chain with HN *)
  assert (Hkey : Qabs X <= Qabs Y).
  { destruct (Qlt_le_dec X 0) as [Hxn | Hxp];
    destruct (Qlt_le_dec Y 0) as [Hyn | Hyp].
    - assert (Qabs X == -X) by (apply Qabs_neg; lra).
      assert (Qabs Y == -Y) by (apply Qabs_neg; lra). lra.
    - (* X < 0, Y >= 0 — impossible since X == Y *)
      exfalso. lra.
    - (* X >= 0, Y < 0 — impossible since X == Y *)
      exfalso. lra.
    - assert (Qabs X == X) by (apply Qabs_pos; lra).
      assert (Qabs Y == Y) by (apply Qabs_pos; lra). lra. }
  exact (Qle_trans _ _ _ Hkey HN).
Qed.

(** L12: FTC for constant zero — trivial case *)
Lemma ftc_constant : forall (a b eps : Q),
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun _ => 0) a step (S N)) <= eps * (b - a).
Proof.
  intros a b eps Hab Heps.
  exists O.
  set (step := (b - a) / inject_Z (Z.of_nat 1)).
  assert (Hrs : riemann_sum (fun _ => 0) a step 1 == 0).
  { simpl. ring. }
  assert (Habs : Qabs (riemann_sum (fun _ => 0) a step 1) == 0).
  { qabs_rw Hrs. rewrite Qabs_pos; lra. }
  assert (Hba : 0 < b - a) by lra.
  assert (Hrhs : 0 <= eps * (b - a)).
  { apply Qmult_le_0_compat; lra. }
  apply Qle_trans with 0; lra.
Qed.

(** L13: FTC for affine function f(x) = c*x + d *)
Lemma ftc_affine : forall (c d a b eps : Q),
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun _ => c) a step (S N) -
          ((c * walk_point a step (S N) + d) - (c * a + d))) <= eps * (b - a).
Proof.
  intros c d a b eps Hab Heps.
  assert (Hudiff : udiff_on (fun w => c * w + d) (fun _ => c) a b).
  { apply affine_udiff. exact Hab. }
  destruct (ftc_grid (fun w => c * w + d) (fun _ => c) a b eps Hudiff Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  exact HN.
Qed.

(** L14: FTC + nonneg derivative implies integral is near-nonneg *)
Lemma ftc_nonneg_integral : forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> 0 <= f' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    -(eps * (b - a)) <= riemann_sum f' a step (S N).
Proof.
  intros f f' a b eps Hudiff Hnn Heps.
  assert (Hab : a < b) by (destruct Hudiff; exact H).
  assert (Hba : 0 < b - a) by lra.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  (* From ftc_grid with eps/2 *)
  destruct (ftc_grid f f' a b (eps * (1#2)) Hudiff Heps2) as [N1 HN1].
  (* From nonneg_deriv_approx_nondec with eps/2 *)
  destruct (nonneg_deriv_approx_nondec f f' a b (eps * (1#2)) Hudiff Hnn Heps2) as [N2 HN2].
  (* Use the larger N *)
  (* For simplicity, use N1 — the ftc bound gives us what we need *)
  exists N1.
  set (step := (b - a) / inject_Z (Z.of_nat (S N1))).
  (* |RS - (f(end) - f(a))| <= (eps/2)*(b-a) *)
  (* So RS >= f(end) - f(a) - (eps/2)*(b-a) *)
  assert (Habs_bound : Qabs (riemann_sum f' a step (S N1) -
                              (f (walk_point a step (S N1)) - f a)) <=
                        eps * (1#2) * (b - a)).
  { exact HN1. }
  (* RS >= (f(end)-f(a)) - (eps/2)*(b-a) *)
  assert (Hge_minus : -(Qabs (riemann_sum f' a step (S N1) -
                               (f (walk_point a step (S N1)) - f a))) <=
                       riemann_sum f' a step (S N1) -
                       (f (walk_point a step (S N1)) - f a)).
  { destruct (Qlt_le_dec (riemann_sum f' a step (S N1) -
                            (f (walk_point a step (S N1)) - f a)) 0).
    - rewrite Qabs_neg; [| lra]. lra.
    - rewrite Qabs_pos; lra. }
  assert (Hrs_lo : riemann_sum f' a step (S N1) >=
                    (f (walk_point a step (S N1)) - f a) - eps * (1#2) * (b - a)).
  { lra. }
  (* Now we need f(end)-f(a) >= -(eps/2)*(b-a) *)
  (* From nonneg_deriv_approx_nondec: we need this for walk with step based on N1 *)
  (* Actually, riemann_sum_nonneg gives RS >= 0 directly since f' >= 0 and step > 0 *)
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hrs_nn : 0 <= riemann_sum f' a step (S N1)).
  { apply riemann_sum_nonneg; [| lra].
    intros k Hk.
    assert (Hin : a <= walk_point a step k /\ walk_point a step k <= b).
    { apply walk_point_in_interval; [exact Hab | lia]. }
    destruct Hin as [Hlo Hhi].
    apply Hnn; assumption. }
  assert (Hneg : -(eps * (b - a)) <= 0).
  { assert (H0 : 0 <= eps * (b - a)) by (apply Qmult_le_0_compat; lra).
    lra. }
  apply Qle_trans with 0; assumption.
Qed.

(* ========================================================================= *)
(* SECTION 5: COMPOSITION AND APPLICATIONS                                    *)
(* ========================================================================= *)

(** L15: udiff is closed under addition *)
Lemma udiff_add : forall (f f' g g' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  udiff_on (fun x => f x + g x) (fun x => f' x + g' x) a b.
Proof.
  intros f f' g g' a b [Hab Huf] [_ Hug].
  split; [exact Hab |].
  intros eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Huf (eps * (1#2)) Heps2) as [d1 [Hd1 Hbd1]].
  destruct (Hug (eps * (1#2)) Heps2) as [d2 [Hd2 Hbd2]].
  exists (Qmin d1 d2).
  split.
  { apply Q.min_glb_lt; assumption. }
  intros x h Hax Hxb Hh_pos Hh_lt.
  assert (Hh_d1 : Qabs h < d1).
  { apply Qlt_le_trans with (Qmin d1 d2); [exact Hh_lt | apply Q.le_min_l]. }
  assert (Hh_d2 : Qabs h < d2).
  { apply Qlt_le_trans with (Qmin d1 d2); [exact Hh_lt | apply Q.le_min_r]. }
  assert (Herr_eq : (f (x + h) + g (x + h)) - (f x + g x) - (f' x + g' x) * h ==
                     (f (x + h) - f x - f' x * h) + (g (x + h) - g x - g' x * h)) by ring.
  qabs_rw Herr_eq.
  apply Qle_lt_trans with (Qabs (f (x + h) - f x - f' x * h) +
                            Qabs (g (x + h) - g x - g' x * h)).
  { apply Qabs_triangle. }
  assert (Hf_err : Qabs (f (x + h) - f x - f' x * h) < eps * (1#2) * Qabs h).
  { apply Hbd1; assumption. }
  assert (Hg_err : Qabs (g (x + h) - g x - g' x * h) < eps * (1#2) * Qabs h).
  { apply Hbd2; assumption. }
  assert (Hsum : eps * (1#2) * Qabs h + eps * (1#2) * Qabs h == eps * Qabs h) by ring.
  lra.
Qed.

(** L16: udiff is closed under scalar multiplication *)
Lemma udiff_scale : forall (c : Q) (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  udiff_on (fun x => c * f x) (fun x => c * f' x) a b.
Proof.
  intros c f f' a b [Hab Huf].
  split; [exact Hab |].
  intros eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hc_nz].
  - (* c == 0: error is 0 *)
    exists 1. split; [lra |].
    intros x h Hax Hxb Hh_pos Hh_lt.
    assert (Herr : c * f (x + h) - c * f x - c * f' x * h == 0).
    { rewrite Hc0. ring. }
    qabs_rw Herr. rewrite Qabs_pos; [| lra].
    apply Qmult_lt_0_compat; [exact Heps | exact Hh_pos].
  - (* c != 0: use eps/|c| *)
    assert (Hc_abs_pos : 0 < Qabs c).
    { destruct (Qlt_le_dec c 0).
      - rewrite Qabs_neg; lra.
      - assert (c > 0) by (destruct (Qlt_le_dec 0 c); [lra | exfalso; apply Hc_nz; lra]).
        rewrite Qabs_pos; lra. }
    assert (Heps_c : 0 < eps / Qabs c).
    { apply Qlt_shift_div_l; [exact Hc_abs_pos | lra]. }
    destruct (Huf (eps / Qabs c) Heps_c) as [delta [Hdelta Hbd]].
    exists delta. split; [exact Hdelta |].
    intros x h Hax Hxb Hh_pos Hh_lt.
    assert (Herr : c * f (x + h) - c * f x - c * f' x * h ==
                    c * (f (x + h) - f x - f' x * h)) by ring.
    qabs_rw Herr. rewrite Qabs_Qmult.
    assert (Hf_err : Qabs (f (x + h) - f x - f' x * h) < eps / Qabs c * Qabs h).
    { apply Hbd; assumption. }
    (* err * |c| < (eps/|c| * |h|) * |c| *)
    assert (H1 : Qabs (f (x + h) - f x - f' x * h) * Qabs c <
                  (eps / Qabs c * Qabs h) * Qabs c).
    { apply Qmult_lt_compat_r; [exact Hc_abs_pos | exact Hf_err]. }
    (* (eps/|c|*|h|)*|c| == eps*|h| *)
    assert (Hsimp : (eps / Qabs c * Qabs h) * Qabs c == eps * Qabs h).
    { field. intros Hcontra. lra. }
    (* |c|*err == err*|c| *)
    assert (Hcomm : Qabs c * Qabs (f (x + h) - f x - f' x * h) ==
                     Qabs (f (x + h) - f x - f' x * h) * Qabs c) by ring.
    (* Chain: |c|*err == err*|c| < (eps/|c|*|h|)*|c| == eps*|h| *)
    apply Qle_lt_trans with (Qabs (f (x + h) - f x - f' x * h) * Qabs c).
    + lra.
    + apply Qlt_le_trans with ((eps / Qabs c * Qabs h) * Qabs c).
      * exact H1.
      * lra.
Qed.

(** L17: FTC linearity — integral of sum equals sum of integrals *)
Lemma ftc_linearity : forall (f f' g g' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun x => f' x + g' x) a step (S N) -
          ((f (walk_point a step (S N)) + g (walk_point a step (S N))) - (f a + g a))) <=
    eps * (b - a).
Proof.
  intros f f' g g' a b eps Huf Hug Heps.
  assert (Hudiff_sum : udiff_on (fun x => f x + g x) (fun x => f' x + g' x) a b).
  { apply udiff_add; assumption. }
  destruct (ftc_grid (fun x => f x + g x) (fun x => f' x + g' x) a b eps Hudiff_sum Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))).
  exact HN.
Qed.

(** L18: FTC comparison — if f' <= g' then RS(f') <= RS(g') + error *)
Lemma ftc_comparison : forall (f f' g g' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  udiff_on g g' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x <= g' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    riemann_sum f' a step (S N) <= riemann_sum g' a step (S N) + eps * (b - a).
Proof.
  intros f f' g g' a b eps Huf Hug Hfg Heps.
  assert (Hab : a < b) by (destruct Huf; exact H).
  exists O.
  set (step := (b - a) / inject_Z (Z.of_nat 1)).
  assert (Hstep_pos : 0 < step) by (apply walk_step_pos; exact Hab).
  assert (Hba : 0 < b - a) by lra.
  assert (Hmono : riemann_sum f' a step 1 <= riemann_sum g' a step 1).
  { apply riemann_sum_monotone; [| lra].
    intros k Hk. assert (k = 0)%nat by lia. subst k.
    simpl walk_point.
    apply Hfg; lra. }
  assert (Hrhs : 0 <= eps * (b - a)).
  { apply Qmult_le_0_compat; lra. }
  assert (Hsum : riemann_sum g' a step 1 <= riemann_sum g' a step 1 + eps * (b - a)) by lra.
  exact (Qle_trans _ _ _ Hmono Hsum).
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                               *)
(* ========================================================================= *)

Check riemann_sum_const.
Check riemann_sum_add.
Check riemann_sum_scale.
Check riemann_sum_nonneg.
Check riemann_sum_monotone.
Check riemann_sum_abs_bound.
Check riemann_sum_width.
Check riemann_sum_global_bound.
Check telescope_collapse.
Check rs_tele_error_bound.
Check ftc_grid.
Check ftc_constant.
Check ftc_affine.
Check ftc_nonneg_integral.
Check udiff_add.
Check udiff_scale.
Check ftc_linearity.
Check ftc_comparison.

Print Assumptions ftc_grid.
Print Assumptions udiff_add.
Print Assumptions ftc_comparison.
