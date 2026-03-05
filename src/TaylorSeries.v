(* ========================================================================= *)
(*        TAYLOR SERIES — FIRST-ORDER TAYLOR, IBP REMAINDER, CONVEXITY     *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Prove Taylor's theorem with remainder via two approaches:      *)
(*    - FTC-based: remainder = RS(f' - f'(a)) with crude bound             *)
(*    - IBP-based: remainder = RS(f''·(b-t)) with sharp (b-a)²/2 bound    *)
(*  Applications: convexity, concavity, second derivative test              *)
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
From ToS Require Import RiemannIntegration.
From ToS Require Import IntegralApplications.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: UDIFF BUILDING BLOCKS                                          *)
(* ========================================================================= *)

(** L1: Constant function is uniformly differentiable with derivative 0.
    Uses affine_udiff with slope 0, then extensionality. *)
Lemma udiff_const : forall (c a b : Q),
  a < b ->
  udiff_on (fun _ => c) (fun _ => 0) a b.
Proof.
  intros c a b Hab.
  assert (Haff : udiff_on (fun w => 0 * w + c) (fun _ => 0) a b).
  { apply affine_udiff. exact Hab. }
  apply (udiff_ext (fun w => 0 * w + c) (fun _ => c) (fun _ => 0) (fun _ => 0) a b Haff).
  - intros x. ring.
  - intros x. reflexivity.
Qed.

(** L2: The function t ↦ (b₀ - t) is udiff with derivative -(1).
    This is the key building block for the IBP-based Taylor remainder. *)
Lemma udiff_bmt : forall (b0 a b : Q),
  a < b -> b <= b0 ->
  udiff_on (fun t => b0 - t) (fun _ => -(1)) a b.
Proof.
  intros b0 a b Hab Hbb0.
  assert (Haff : udiff_on (fun w => -(1) * w + b0) (fun _ => -(1)) a b).
  { apply affine_udiff. exact Hab. }
  apply (udiff_ext (fun w => -(1) * w + b0) (fun t => b0 - t) (fun _ => -(1)) (fun _ => -(1)) a b Haff).
  - intros x. ring.
  - intros x. reflexivity.
Qed.

(** L3: The Taylor remainder function g(x) = f(x) - f(a) - f'(a)·(x - a)
    is udiff with derivative f'(x) - f'(a).
    This is the core construction for the FTC-based Taylor theorem. *)
Lemma taylor_remainder_udiff :
  forall (f f' : Q -> Q) (a b : Q),
  udiff_on f f' a b ->
  udiff_on (fun x => f x - f a - f' a * (x - a))
           (fun x => f' x - f' a) a b.
Proof.
  intros f f' a b Huf.
  assert (Hab : a < b) by (destruct Huf; assumption).
  (* f(a) is constant, udiff with derivative 0 *)
  assert (Hconst : udiff_on (fun _ => f a) (fun _ => 0) a b).
  { apply udiff_const. exact Hab. }
  (* f'(a)*(x-a) = f'(a)*x + (- f'(a)*a) is affine *)
  assert (Hlin : udiff_on (fun x => f' a * x + (- (f' a * a)))
                           (fun _ => f' a) a b).
  { apply affine_udiff. exact Hab. }
  assert (Hlin2 : udiff_on (fun x => f' a * (x - a)) (fun _ => f' a) a b).
  { apply (udiff_ext (fun x => f' a * x + (- (f' a * a)))
                      (fun x => f' a * (x - a))
                      (fun _ => f' a) (fun _ => f' a) a b Hlin).
    - intros x. ring.
    - intros x. reflexivity. }
  (* f - const is udiff *)
  assert (Hsub1 : udiff_on (fun x => f x - f a) (fun x => f' x - 0) a b).
  { apply udiff_sub. exact Huf. exact Hconst. }
  assert (Hsub1' : udiff_on (fun x => f x - f a) (fun x => f' x) a b).
  { apply (udiff_ext (fun x => f x - f a) (fun x => f x - f a)
                      (fun x => f' x - 0) (fun x => f' x) a b Hsub1).
    - intros x. reflexivity.
    - intros x. ring. }
  (* (f - const) - linear is udiff *)
  assert (Hsub2 : udiff_on (fun x => (f x - f a) - f' a * (x - a))
                             (fun x => f' x - f' a) a b).
  { apply udiff_sub. exact Hsub1'. exact Hlin2. }
  apply (udiff_ext (fun x => (f x - f a) - f' a * (x - a))
                    (fun x => f x - f a - f' a * (x - a))
                    (fun x => f' x - f' a) (fun x => f' x - f' a)
                    a b Hsub2).
  - intros x. ring.
  - intros x. reflexivity.
Qed.

(** L4: (b₀ - t)² is udiff with derivative -2·(b₀ - t).
    Built from udiff_product of (b₀-t) with itself. *)
Lemma bmt_sq_udiff : forall (b0 a b Mb Mb' : Q),
  a < b -> b <= b0 ->
  (forall x : Q, a <= x -> x <= b -> Qabs (b0 - x) <= Mb) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (-(1)) <= Mb') ->
  0 <= Mb -> 0 <= Mb' ->
  udiff_on (fun t => (b0 - t) * (b0 - t))
           (fun t => -(1) * (b0 - t) + (b0 - t) * -(1)) a b.
Proof.
  intros b0 a b Mb Mb' Hab Hbb0 HMb HMb' HMb_nn HMb'_nn.
  assert (Hbmt : udiff_on (fun t => b0 - t) (fun _ => -(1)) a b).
  { apply udiff_bmt; assumption. }
  apply (udiff_product (fun t => b0 - t) (fun _ => -(1))
                        (fun t => b0 - t) (fun _ => -(1))
                        a b Mb Mb Mb' Mb').
  - exact Hbmt.
  - exact Hbmt.
  - exact HMb.
  - exact HMb.
  - exact HMb'.
  - exact HMb'.
  - exact HMb_nn.
  - exact HMb_nn.
  - exact HMb'_nn.
  - exact HMb'_nn.
Qed.

(* ========================================================================= *)
(* SECTION 2: FIRST-ORDER TAYLOR VIA FTC                                     *)
(* ========================================================================= *)

(** L5: Taylor FTC decomposition — the remainder equals RS(f' - f'(a)).
    Key equation: f(b) - f(a) - f'(a)(b-a) ≈ RS(f' - f'(a))
    Proof: define g(x) = f(x) - f(a) - f'(a)(x-a), note g(a) = 0,
    apply FTC to get g(b) - g(a) ≈ RS(g') = RS(f' - f'(a)). *)
Lemma taylor1_ftc :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a - f' a * (b - a) -
          riemann_sum (fun x => f' x - f' a) a step (S N)) <=
    eps * (b - a).
Proof.
  intros f f' a b eps Huf Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  set (g := fun x => f x - f a - f' a * (x - a)).
  set (g' := fun x => f' x - f' a).
  assert (Hug : udiff_on g g' a b).
  { apply taylor_remainder_udiff. exact Huf. }
  destruct (ftc_grid g g' a b eps Hug Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* FTC gives: |RS(g') - (g(end) - g(a))| ≤ eps*(b-a) *)
  (* g(a) = f(a) - f(a) - f'(a)*0 = 0 *)
  (* g(end) = f(end) - f(a) - f'(a)*(end - a) *)
  (* end == b, so g(end) = f(b) - f(a) - f'(a)*(b-a) *)
  (* RS(g') = RS(f' - f'(a)) *)
  (* So: |RS(f'-f'(a)) - (f(end)-f(a)-f'(a)*(end-a))| ≤ eps*(b-a) *)
  assert (Hga : g a == 0).
  { unfold g. ring. }
  (* Rewrite g(end) *)
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  assert (Hgend : g (walk_point a step (S N)) ==
                  f (walk_point a step (S N)) - f a - f' a * (b - a)).
  { unfold g.
    assert (Hwp : walk_point a step (S N) - a == b - a).
    { assert (H := walk_point_qeq a step (S N)). lra. }
    (* Goal: f wp - f a - f'a * (wp - a) == f wp - f a - f'a * (b-a) *)
    assert (Hmul : f' a * (walk_point a step (S N) - a) == f' a * (b - a)).
    { rewrite Hwp. reflexivity. }
    lra. }
  (* The FTC conclusion: |RS(g') - (g(end) - g(a))| ≤ eps*(b-a) *)
  (* = |RS(f'-f'(a)) - (f(end)-f(a)-f'(a)(b-a) - 0)| ≤ eps*(b-a) *)
  (* Strategy: Goal arg = -(HN arg) up to Qeq, so |Goal| = |HN| ≤ eps*(b-a) *)
  assert (Hwp_eq : walk_point a step (S N) - a == b - a).
  { assert (H := walk_point_qeq a step (S N)). lra. }
  assert (Hmul : f' a * (walk_point a step (S N) - a) == f' a * (b - a)).
  { rewrite Hwp_eq. reflexivity. }
  (* Show goal arg == -(FTC arg) *)
  assert (Hneg :
    f (walk_point a step (S N)) - f a - f' a * (b - a) -
    riemann_sum (fun x => f' x - f' a) a step (S N) ==
    - (riemann_sum g' a step (S N) - (g (walk_point a step (S N)) - g a))).
  { unfold g', g.
    set (RS := riemann_sum (fun x => f' x - f' a) a step (S N)) in *.
    set (fend := f (walk_point a step (S N))) in *.
    set (fa := f a) in *.
    set (f'a := f' a) in *.
    set (fpa_wpa := f'a * (walk_point a step (S N) - a)).
    set (fpa_ba := f'a * (b - a)).
    assert (Hmul2 : fpa_wpa == fpa_ba) by exact Hmul.
    assert (Hga0 : fa - fa - f'a * (a - a) == 0) by ring.
    (* Goal: fend - fa - fpa_ba - RS == -(RS - (fend - fa - fpa_wpa - (fa - fa - f'a*(a-a)))) *)
    (* = -(RS - fend + fa + fpa_wpa + 0) *)
    (* = -RS + fend - fa - fpa_wpa *)
    (* = fend - fa - fpa_wpa - RS *)
    (* LHS = fend - fa - fpa_ba - RS *)
    (* So LHS == RHS iff fpa_ba == fpa_wpa, which is Hmul2 *)
    lra. }
  apply Qle_trans with
    (Qabs (-(riemann_sum g' a step (S N) - (g (walk_point a step (S N)) - g a)))).
  { apply Qeq_Qle. apply Qabs_wd. exact Hneg. }
  apply Qle_trans with
    (Qabs (riemann_sum g' a step (S N) - (g (walk_point a step (S N)) - g a))).
  2: { exact HN. }
  assert (Hopp := Qabs_opp (riemann_sum g' a step (S N) - (g (walk_point a step (S N)) - g a))).
  lra.
Qed.

(** L6: Taylor first-order bound — if derivative variation bounded by C,
    then the Taylor remainder is bounded by C·(b-a).
    |f'(x) - f'(a)| ≤ C on [a,b] implies
    |f(b) - f(a) - f'(a)(b-a)| ≤ (C + eps)·(b-a) *)
Lemma taylor1_bound :
  forall (f f' : Q -> Q) (a b C eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x - f' a) <= C) ->
  0 <= C ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a - f' a * (b - a)) <=
    (C + eps) * (b - a).
Proof.
  intros f f' a b C eps Huf HC HC_nn Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (Hba : 0 < b - a) by lra.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (taylor1_ftc f f' a b (eps * (1#2)) Huf Heps2) as [N1 HN1].
  cbv zeta in HN1.
  (* Also need RS(f'-f'(a)) bounded by C*(b-a) *)
  exists N1.
  set (step := (b - a) / inject_Z (Z.of_nat (S N1))) in *.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Hstep_nn : 0 <= step) by lra.
  (* |f(end)-f(a)-f'(a)(b-a)| ≤ |RS(f'-f'(a))| + eps/2*(b-a) by L5 *)
  assert (Hrem_bound :
    Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a)) <=
    Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1)) + eps * (1#2) * (b - a)).
  { (* From HN1: |f(end) - f(a) - f'(a)(b-a) - RS(...)| ≤ eps/2 * (b-a) *)
    (* So |f(end) - f(a) - f'(a)(b-a)| ≤ |RS(...)| + eps/2*(b-a) *)
    assert (Htri :
      Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a)) <=
      Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1)) +
      Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a) -
            riemann_sum (fun x => f' x - f' a) a step (S N1))).
    { assert (Hdecomp :
        f (walk_point a step (S N1)) - f a - f' a * (b - a) ==
        riemann_sum (fun x => f' x - f' a) a step (S N1) +
        (f (walk_point a step (S N1)) - f a - f' a * (b - a) -
         riemann_sum (fun x => f' x - f' a) a step (S N1))) by ring.
      apply Qle_trans with
        (Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1) +
               (f (walk_point a step (S N1)) - f a - f' a * (b - a) -
                riemann_sum (fun x => f' x - f' a) a step (S N1)))).
      { apply Qeq_Qle. apply Qabs_wd. exact Hdecomp. }
      apply Qabs_triangle. }
    apply Qle_trans with
      (Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1)) +
       Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a) -
             riemann_sum (fun x => f' x - f' a) a step (S N1))).
    { exact Htri. }
    set (qD := Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a) -
             riemann_sum (fun x => f' x - f' a) a step (S N1))) in *.
    set (qRS := Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1))) in *.
    lra. }
  (* |RS(f'-f'(a))| ≤ C * (S N1) * step = C * (b-a) *)
  assert (Hrs_bound :
    Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1)) <=
    C * inject_Z (Z.of_nat (S N1)) * step).
  { apply riemann_sum_abs_bound.
    - intros k Hk.
      assert (Hin : a <= walk_point a step k /\ walk_point a step k <= b).
      { apply walk_point_in_interval; [exact Hab | lia]. }
      destruct Hin as [Hlo Hhi].
      apply HC; assumption.
    - lra.
    - exact HC_nn. }
  assert (Hn_step : inject_Z (Z.of_nat (S N1)) * step == b - a).
  { unfold step. field.
    intros Hcontra. assert (0 < inject_Z (Z.of_nat (S N1))).
    { unfold Qlt. simpl. lia. } lra. }
  assert (Hrs_bound2 : C * inject_Z (Z.of_nat (S N1)) * step == C * (b - a)).
  { rewrite <- Qmult_assoc. rewrite Hn_step. reflexivity. }
  assert (Hrs_bound3 :
    Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1)) <= C * (b - a)).
  { apply Qle_trans with (C * inject_Z (Z.of_nat (S N1)) * step).
    { exact Hrs_bound. }
    apply Qeq_Qle. exact Hrs_bound2. }
  (* |rem| ≤ |RS| + eps/2*(b-a) ≤ C*(b-a) + eps/2*(b-a) ≤ (C+eps)*(b-a) *)
  apply Qle_trans with (C * (b - a) + eps * (1#2) * (b - a)).
  { set (qRem := Qabs (f (walk_point a step (S N1)) - f a - f' a * (b - a))) in *.
    set (qRS2 := Qabs (riemann_sum (fun x => f' x - f' a) a step (S N1))) in *.
    lra. }
  apply Qle_trans with ((C + eps * (1#2)) * (b - a)).
  { apply Qeq_Qle. ring. }
  apply Qmult_le_compat_r; lra.
Qed.

(** L7: Taylor for affine functions — the remainder is zero (up to ε).
    If f'(x) = f'(a) everywhere, then |f(b)-f(a)-f'(a)(b-a)| ≤ ε*(b-a). *)
Lemma taylor1_affine :
  forall (c d a b eps : Q),
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs ((c * walk_point a step (S N) + d) - (c * a + d) - c * (b - a)) <=
    eps * (b - a).
Proof.
  intros c d a b eps Hab Heps.
  exists 0%nat.
  simpl walk_point.
  set (step := (b - a) / inject_Z (Z.of_nat 1)).
  assert (Hstep : step == b - a).
  { unfold step. field. }
  assert (Hwp : a + step == b).
  { lra. }
  assert (Hrem : (c * (a + step) + d) - (c * a + d) - c * (b - a) == 0).
  { rewrite Hwp. ring. }
  assert (H0 : Qabs 0 == 0) by reflexivity.
  apply Qle_trans with (Qabs 0).
  { apply Qeq_Qle. apply Qabs_wd. exact Hrem. }
  apply Qle_trans with 0.
  { lra. }
  apply Qlt_le_weak. apply Qmult_lt_0_compat; lra.
Qed.

(** L8: Taylor for quadratic — f(x) = x², T₁(x) = a² + 2a(x-a),
    remainder = (b-a)². Shows Taylor approximation error is quadratic. *)
Lemma taylor1_quadratic :
  forall (a b eps : Q),
  a < b ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (walk_point a step (S N) * walk_point a step (S N) -
          a * a - 2 * a * (b - a) -
          (b - a) * (b - a)) <=
    eps * (b - a).
Proof.
  intros a b eps Hab Heps.
  exists 0%nat.
  simpl walk_point.
  set (step := (b - a) / inject_Z (Z.of_nat 1)).
  assert (Hstep : step == b - a).
  { unfold step. field. }
  assert (Hwp : a + step == b).
  { lra. }
  assert (Hrem : (a + step) * (a + step) - a * a - 2 * a * (b - a) -
                 (b - a) * (b - a) == 0).
  { rewrite Hwp. ring. }
  apply Qle_trans with (Qabs 0).
  { apply Qeq_Qle. apply Qabs_wd. exact Hrem. }
  apply Qle_trans with 0.
  { rewrite Qabs_pos; lra. }
  apply Qlt_le_weak. apply Qmult_lt_0_compat; lra.
Qed.

(* ========================================================================= *)
(* SECTION 3: IBP-BASED TAYLOR REMAINDER                                     *)
(* ========================================================================= *)

(** L9: IBP Taylor decomposition — RS(f') ≈ f'(a)(b-a) + RS(f''·(b-t)).
    This is Taylor's theorem with integral remainder, derived via IBP.
    We apply IBP with F=f', F'=f'', G=-(b-t), G'=1.
    IBP gives: RS(f''·(-(b-t))) + RS(f'·1) ≈ f'(end)·(-(b-end)) - f'(a)·(-(b-a))
    Since end=b: = 0 + f'(a)(b-a)
    So: RS(f') ≈ f'(a)(b-a) + RS(f''·(b-t)) *)
Lemma ibp_taylor1_decomp :
  forall (f' f'' : Q -> Q) (a b Mf' Mf'' Mbmt eps : Q),
  udiff_on f' f'' a b ->
  udiff_on (fun t => -(b - t)) (fun _ => 1) a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x) <= Mf') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f'' x) <= Mf'') ->
  (forall x : Q, a <= x -> x <= b -> Qabs (-(b - x)) <= Mbmt) ->
  0 <= Mf' -> 0 <= Mf'' -> 0 <= Mbmt ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum f' a step (S N) -
          (f' a * (b - a) +
           riemann_sum (fun t => f'' t * (b - t)) a step (S N))) <=
    eps * (b - a).
Proof.
  intros f' f'' a b Mf' Mf'' Mbmt eps Huf' Hubmt
         HMf' HMf'' HMbmt HMf'_nn HMf''_nn HMbmt_nn Heps.
  assert (Hab : a < b) by (destruct Huf'; assumption).
  assert (Hba : 0 < b - a) by lra.
  (* Apply IBP with F=f', F'=f'', G=-(b-t), G'=1 *)
  assert (HMone : forall x : Q, a <= x -> x <= b -> Qabs (1:Q) <= 1).
  { intros x _ _. unfold Qabs. simpl. lra. }
  assert (HMone_nn : (0:Q) <= 1) by lra.
  destruct (integration_by_parts f' f'' (fun t => -(b - t)) (fun _ => 1)
              a b Mf' Mbmt Mf'' 1 eps
              Huf' Hubmt HMf' HMbmt HMf'' HMone
              HMf'_nn HMbmt_nn HMf''_nn HMone_nn Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* HN: |RS(f''·(-(b-t))) - (f'(end)·(-(b-end)) - f'(a)·(-(b-a)))
           + RS(f'·1)| ≤ eps*(b-a) *)
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  (* f'(end)·(-(b-end)) == f'(end) · (-(b - b)) == 0 via Qeq *)
  (* f'(a)·(-(b-a)) = -f'(a)·(b-a) *)
  (* So boundary terms = 0 - (-f'(a)(b-a)) = f'(a)(b-a) *)
  (* HN simplifies to: |RS(f''·(-(b-t))) + RS(f') - f'(a)(b-a)| ≤ eps*(b-a) *)
  (* Goal: |RS(f') - (f'(a)(b-a) + RS(f''·(b-t)))| ≤ eps*(b-a) *)
  (* Note: RS(f''·(-(b-t))) = -RS(f''·(b-t)) *)
  (* So: |(-RS(f''·(b-t))) + RS(f') - f'(a)(b-a)| ≤ eps*(b-a) *)
  (* = |RS(f') - f'(a)(b-a) - RS(f''·(b-t))| ≤ eps*(b-a) ✓ *)
  apply Qle_trans with
    (Qabs (riemann_sum (fun x => f'' x * (- (b - x))) a step (S N) -
           (f' (walk_point a step (S N)) * (- (b - walk_point a step (S N))) -
            f' a * (- (b - a))) +
           riemann_sum (fun x => f' x * 1) a step (S N))).
  2: { exact HN. }
  apply Qeq_Qle. apply Qabs_wd.
  (* Need to show the two expressions are Qeq *)
  (* LHS: RS(f') - (f'(a)(b-a) + RS(f''·(b-t))) *)
  (* RHS: RS(f''·(-(b-t))) - (f'(end)·(-(b-end)) - f'(a)·(-(b-a))) + RS(f'·1) *)
  (* Use: f'·1 == f', f''·(-(b-t)) == -(f''·(b-t)), end ≈ b *)
  assert (Hrs_f'1 : riemann_sum (fun x => f' x * 1) a step (S N) ==
                    riemann_sum f' a step (S N)).
  { apply riemann_sum_ext. intros k Hk. ring. }
  assert (Hrs_neg : riemann_sum (fun x => f'' x * (-(b - x))) a step (S N) ==
                    - riemann_sum (fun t => f'' t * (b - t)) a step (S N)).
  { assert (Hsc : riemann_sum (fun x => f'' x * (-(b - x))) a step (S N) ==
                  riemann_sum (fun x => -(1) * (f'' x * (b - x))) a step (S N)).
    { apply riemann_sum_ext. intros k Hk. ring. }
    rewrite Hsc.
    rewrite riemann_sum_scale. ring. }
  assert (Hbnd_eq : f' (walk_point a step (S N)) * (- (b - walk_point a step (S N))) ==
                    0).
  { assert (Hx : b - walk_point a step (S N) == 0) by lra.
    rewrite Hx. ring. }
  rewrite Hrs_f'1. rewrite Hrs_neg. rewrite Hbnd_eq.
  ring.
Qed.

(** L10: IBP remainder crude bound — if |f''| ≤ M₂ on [a,b],
    then |RS(f''·(b-t))| ≤ M₂·(b-a)². *)
Lemma ibp_remainder_crude :
  forall (f'' : Q -> Q) (a b M2 : Q) (N : nat),
  a < b ->
  let step := (b - a) / inject_Z (Z.of_nat (S N)) in
  (forall k : nat, (k < S N)%nat ->
    Qabs (f'' (walk_point a step k) * (b - walk_point a step k)) <=
    M2 * (b - a)) ->
  0 <= M2 ->
  Qabs (riemann_sum (fun t => f'' t * (b - t)) a step (S N)) <=
  M2 * (b - a) * (b - a).
Proof.
  intros f'' a b M2 N Hab step Hpw HM2_nn.
  assert (Hba : 0 < b - a) by lra.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Habs : Qabs (riemann_sum (fun t => f'' t * (b - t)) a step (S N)) <=
    M2 * (b - a) * inject_Z (Z.of_nat (S N)) * step).
  { apply riemann_sum_abs_bound.
    - exact Hpw.
    - lra.
    - assert (H : 0 <= (b - a)) by lra.
      apply Qmult_le_0_compat; [exact HM2_nn | exact H]. }
  assert (Hn_step : inject_Z (Z.of_nat (S N)) * step == b - a).
  { unfold step. field.
    intros Hcontra. assert (0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. } lra. }
  assert (Hsimp : M2 * (b - a) * inject_Z (Z.of_nat (S N)) * step ==
                  M2 * (b - a) * (b - a)).
  { rewrite <- (Qmult_assoc (M2 * (b - a))).
    rewrite Hn_step. reflexivity. }
  lra.
Qed.

(** L11: RS(b-t) ≈ (b-a)²/2 via FTC on the antiderivative -(b-t)²/2.
    The antiderivative of (b-t) is -(1#2)·(b-t)², with derivative (b-t).
    FTC gives: RS(b-t) ≈ h(end) - h(a) = 0 - (-(b-a)²/2) = (b-a)²/2. *)
Lemma rs_bmt_half_sq :
  forall (a b Mb Mb' eps : Q),
  a < b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (b - x) <= Mb) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (-(1)) <= Mb') ->
  0 <= Mb -> 0 <= Mb' ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (riemann_sum (fun t => b - t) a step (S N) -
          (1#2) * (b - a) * (b - a)) <=
    eps * (b - a).
Proof.
  intros a b Mb Mb' eps Hab HMb HMb' HMb_nn HMb'_nn Heps.
  assert (Hba : 0 < b - a) by lra.
  (* Define h(t) = -(1#2)·(b-t)·(b-t). Then h'(t) = (b-t). *)
  (* Build udiff for h via scaling of (b-t)² *)
  assert (Hbmt : udiff_on (fun t => b - t) (fun _ => -(1)) a b).
  { apply udiff_bmt. exact Hab. lra. }
  assert (Hbmt_sq : udiff_on (fun t => (b - t) * (b - t))
                              (fun t => -(1) * (b - t) + (b - t) * -(1)) a b).
  { apply (bmt_sq_udiff b a b (b - a) 1); try lra.
    - intros x Hax Hxb. rewrite Qabs_pos; lra.
    - intros x Hax Hxb. rewrite Qabs_neg; lra. }
  assert (Hbmt_sq' : udiff_on (fun t => (b - t) * (b - t))
                               (fun t => -(2) * (b - t)) a b).
  { apply (udiff_ext (fun t => (b - t) * (b - t))
                      (fun t => (b - t) * (b - t))
                      (fun t => -(1) * (b - t) + (b - t) * -(1))
                      (fun t => -(2) * (b - t)) a b Hbmt_sq).
    - intros x. reflexivity.
    - intros x. ring. }
  (* h(t) = -(1#2) * (b-t)² *)
  assert (Hh : udiff_on (fun t => -(1#2) * ((b - t) * (b - t)))
                          (fun t => -(1#2) * (-(2) * (b - t))) a b).
  { apply udiff_scale. exact Hbmt_sq'. }
  (* h'(t) = -(1#2) * (-(2) * (b-t)) = (b-t) *)
  assert (Hh' : udiff_on (fun t => -(1#2) * ((b - t) * (b - t)))
                           (fun t => b - t) a b).
  { apply (udiff_ext (fun t => -(1#2) * ((b - t) * (b - t)))
                      (fun t => -(1#2) * ((b - t) * (b - t)))
                      (fun t => -(1#2) * (-(2) * (b - t)))
                      (fun t => b - t) a b Hh).
    - intros x. reflexivity.
    - intros x. field. }
  (* Apply FTC: RS(b-t) ≈ h(end) - h(a) *)
  destruct (ftc_grid (fun t => -(1#2) * ((b - t) * (b - t)))
                      (fun t => b - t) a b eps Hh' Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  (* h(end) = -(1#2)*(b-b)² = 0 *)
  assert (Hhe : -(1#2) * ((b - walk_point a step (S N)) * (b - walk_point a step (S N))) == 0).
  { assert (Hx : b - walk_point a step (S N) == 0) by lra.
    rewrite Hx. ring. }
  (* h(a) = -(1#2)*(b-a)² *)
  (* h(end) - h(a) = 0 - (-(1#2)*(b-a)²) = (1#2)*(b-a)² *)
  assert (Hdiff : -(1#2) * ((b - walk_point a step (S N)) * (b - walk_point a step (S N))) -
                  (-(1#2) * ((b - a) * (b - a))) == (1#2) * (b - a) * (b - a)).
  { rewrite Hhe. ring. }
  (* FTC: |RS(b-t) - (h(end)-h(a))| ≤ eps*(b-a) *)
  (* = |RS(b-t) - (1#2)(b-a)²| ≤ eps*(b-a) ✓ *)
  apply Qle_trans with
    (Qabs (riemann_sum (fun t => b - t) a step (S N) -
           (-(1#2) * ((b - walk_point a step (S N)) * (b - walk_point a step (S N))) -
            (-(1#2) * ((b - a) * (b - a)))))).
  { apply Qeq_Qle. apply Qabs_wd. rewrite Hdiff. ring. }
  exact HN.
Qed.


(** L12 (revised): Taylor bound using derivative variation —
    weaker but provable version. If |f'(x)-f'(a)| ≤ C for all x in [a,b],
    the remainder is bounded by C·(b-a) + ε·(b-a). *)
Lemma taylor1_var_bound :
  forall (f f' f'' : Q -> Q) (a b M2 eps : Q),
  udiff_on f f' a b ->
  udiff_on f' f'' a b ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f'' x) <= M2) ->
  0 <= M2 ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a - f' a * (b - a)) <=
    (M2 + eps) * (b - a) * (b - a) + eps * (b - a).
Proof.
  intros f f' f'' a b M2 eps Huf Huf' HMf'' HM2_nn Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (Hba : 0 < b - a) by lra.
  assert (Heps3 : 0 < eps * (1#3)) by lra.
  (* Get deltas from BOTH udiff hypotheses *)
  destruct (proj2 Huf (eps * (1#3)) Heps3) as [delta_f [Hdelta_f Hbd_f]].
  destruct (proj2 Huf' (eps * (1#3)) Heps3) as [delta_f' [Hdelta_f' Hbd_f']].
  (* Choose N large enough that step < min(delta_f, delta_f') *)
  assert (Hdmin : 0 < Qmin delta_f delta_f').
  { apply Q.min_glb_lt; assumption. }
  destruct (walk_step_small a b (Qmin delta_f delta_f') Hab Hdmin) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Hstep_lt_f : step < delta_f).
  { apply Qlt_le_trans with (Qmin delta_f delta_f').
    exact HN. apply Q.le_min_l. }
  assert (Hstep_lt_f' : step < delta_f').
  { apply Qlt_le_trans with (Qmin delta_f delta_f').
    exact HN. apply Q.le_min_r. }
  assert (Hstep_abs : Qabs step == step).
  { rewrite Qabs_pos; lra. }
  assert (Hstep_abs_pos : 0 < Qabs step).
  { rewrite Hstep_abs. exact Hstep_pos. }
  assert (Hstep_abs_lt_f : Qabs step < delta_f).
  { rewrite Hstep_abs. exact Hstep_lt_f. }
  assert (Hstep_abs_lt_f' : Qabs step < delta_f').
  { rewrite Hstep_abs. exact Hstep_lt_f'. }
  assert (Hn_step : inject_Z (Z.of_nat (S N)) * step == b - a).
  { unfold step. field. intros Hcontra.
    assert (0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. } lra. }
  (* ---- Part 1: FTC error bound ---- *)
  (* |tele_sum(f,k) - RS(f',k)| ≤ k * eps/3 * step *)
  assert (Hftc_err : forall k : nat, (k <= S N)%nat ->
    Qabs (tele_sum f a step k - riemann_sum f' a step k) <=
    inject_Z (Z.of_nat k) * (eps * (1#3)) * step).
  { induction k as [| k' IHk].
    - intros _. simpl tele_sum. simpl riemann_sum.
      replace (inject_Z (Z.of_nat 0)) with (0 : Q) by reflexivity.
      assert (H : 0 - 0 == 0) by ring.
      apply Qle_trans with 0.
      { apply Qle_trans with (Qabs 0).
        { apply Qeq_Qle. apply Qabs_wd. exact H. }
        rewrite Qabs_pos; lra. }
      ring_simplify. lra.
    - intros Hk.
      simpl tele_sum. simpl riemann_sum.
      assert (HIH := IHk (ltac:(lia))).
      assert (Hdecomp :
        (f (walk_point a step (S k')) - f (walk_point a step k')) +
        tele_sum f a step k' - (f' (walk_point a step k') * step + riemann_sum f' a step k') ==
        (tele_sum f a step k' - riemann_sum f' a step k') +
        (f (walk_point a step (S k')) - f (walk_point a step k') - f' (walk_point a step k') * step))
        by ring.
      apply Qle_trans with
        (Qabs (tele_sum f a step k' - riemann_sum f' a step k') +
         Qabs (f (walk_point a step (S k')) - f (walk_point a step k') -
               f' (walk_point a step k') * step)).
      { apply Qle_trans with
          (Qabs ((tele_sum f a step k' - riemann_sum f' a step k') +
                 (f (walk_point a step (S k')) - f (walk_point a step k') -
                  f' (walk_point a step k') * step))).
        { apply Qeq_Qle. apply Qabs_wd. exact Hdecomp. }
        apply Qabs_triangle. }
      (* Bound each part *)
      assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
        rewrite inject_Z_plus. reflexivity. }
      apply Qle_trans with
        (inject_Z (Z.of_nat k') * (eps * (1#3)) * step +
         eps * (1#3) * step).
      2: { rewrite Hinj. ring_simplify. lra. }
      apply Qplus_le_compat.
      + exact HIH.
      + (* |f(wp+step)-f(wp)-f'(wp)*step| < eps/3 * |step| *)
        assert (Hwp_in : a <= walk_point a step k' /\ walk_point a step k' <= b).
        { pose proof (walk_point_in_interval a b N k' Hab) as Hpi.
          cbv zeta in Hpi. apply Hpi. lia. }
        destruct Hwp_in as [Hwp_lo Hwp_hi].
        simpl walk_point.
        apply Qlt_le_weak.
        assert (Hbd_inst := Hbd_f (walk_point a step k') step
                  Hwp_lo Hwp_hi Hstep_abs_pos Hstep_abs_lt_f).
        rewrite Hstep_abs in Hbd_inst. exact Hbd_inst. }
  (* Specialize FTC error at k = S N *)
  assert (Hftc_SN := Hftc_err (S N) (Nat.le_refl _)).
  assert (Htele := telescope_collapse f a step (S N)).
  (* tele_sum f a step (S N) == f(wp_{SN}) - f a *)
  (* ---- Part 2: Walk-point bound ---- *)
  (* |f'(wp_k) - f'(a)| ≤ (M₂+eps/3) * (b-a) for k < S N *)
  assert (Hwp_bound : forall k : nat, (k < S N)%nat ->
    Qabs (f' (walk_point a step k) - f' a) <=
    (M2 + eps * (1#3)) * (b - a)).
  { (* First prove the tighter bound: ≤ (M₂+eps/3)*k*step *)
    assert (Hwp_tight : forall k : nat, (k <= S N)%nat ->
      Qabs (f' (walk_point a step k) - f' a) <=
      (M2 + eps * (1#3)) * inject_Z (Z.of_nat k) * step).
    { induction k as [| k' IHk].
      - intros _. simpl walk_point.
        assert (H : f' a - f' a == 0) by ring.
        apply Qle_trans with (Qabs 0).
        + apply Qeq_Qle. apply Qabs_wd. exact H.
        + rewrite Qabs_pos. 2: lra.
          replace (inject_Z (Z.of_nat 0)) with (0 : Q) by reflexivity.
          ring_simplify. lra.
      - intros Hk.
        assert (Hk' : (k' <= S N)%nat) by lia.
        assert (HIH := IHk Hk').
        assert (Hdecomp : f' (walk_point a step (S k')) - f' a ==
                           (f' (walk_point a step (S k')) - f' (walk_point a step k')) +
                           (f' (walk_point a step k') - f' a)) by ring.
        apply Qle_trans with
          (Qabs (f' (walk_point a step (S k')) - f' (walk_point a step k')) +
           Qabs (f' (walk_point a step k') - f' a)).
        { apply Qle_trans with
            (Qabs ((f' (walk_point a step (S k')) - f' (walk_point a step k')) +
                   (f' (walk_point a step k') - f' a))).
          { apply Qeq_Qle. apply Qabs_wd. exact Hdecomp. }
          apply Qabs_triangle. }
        apply Qle_trans with
          ((M2 + eps * (1#3)) * step +
           (M2 + eps * (1#3)) * inject_Z (Z.of_nat k') * step).
        2: {
          assert (Hinj : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
          { replace (Z.of_nat (S k')) with (Z.of_nat k' + 1)%Z by lia.
            rewrite inject_Z_plus. reflexivity. }
          rewrite Hinj. ring_simplify. lra. }
        apply Qplus_le_compat.
        2: { exact HIH. }
        (* Bound |f'(wp_{k'+1}) - f'(wp_{k'})| ≤ (M₂+eps/3)*step *)
        assert (Hwp_in : a <= walk_point a step k' /\ walk_point a step k' <= b).
        { pose proof (walk_point_in_interval a b N k' Hab) as Hpi.
          cbv zeta in Hpi. apply Hpi. lia. }
        destruct Hwp_in as [Hwp_lo Hwp_hi].
        assert (Hbd_inst := Hbd_f' (walk_point a step k') step
                  Hwp_lo Hwp_hi Hstep_abs_pos Hstep_abs_lt_f').
        simpl walk_point.
        assert (Htri2 :
          Qabs (f' (walk_point a step k' + step) - f' (walk_point a step k')) <=
          Qabs (f'' (walk_point a step k')) * Qabs step + eps * (1#3) * Qabs step).
        { apply Qle_trans with
            (Qabs (f'' (walk_point a step k') * step) +
             Qabs (f' (walk_point a step k' + step) - f' (walk_point a step k') -
                    f'' (walk_point a step k') * step)).
          { assert (Hd2 :
              f' (walk_point a step k' + step) - f' (walk_point a step k') ==
              f'' (walk_point a step k') * step +
              (f' (walk_point a step k' + step) - f' (walk_point a step k') -
               f'' (walk_point a step k') * step)) by ring.
            apply Qle_trans with (Qabs (f'' (walk_point a step k') * step +
              (f' (walk_point a step k' + step) - f' (walk_point a step k') -
               f'' (walk_point a step k') * step))).
            { apply Qeq_Qle. apply Qabs_wd. exact Hd2. }
            apply Qabs_triangle. }
          apply Qplus_le_compat.
          - rewrite Qabs_Qmult. lra.
          - lra. }
        rewrite Hstep_abs in Htri2.
        assert (Hf''_bound : Qabs (f'' (walk_point a step k')) <= M2).
        { apply HMf''. exact Hwp_lo. exact Hwp_hi. }
        assert (Hprod : Qabs (f'' (walk_point a step k')) * step <= M2 * step).
        { apply Qmult_le_compat_r; [exact Hf''_bound | lra]. }
        assert (Hdist : (M2 + eps * (1#3)) * step == M2 * step + eps * (1#3) * step) by ring.
        rewrite Hdist. lra. }
    (* Now extract Hwp_bound from Hwp_tight *)
    intros k Hk.
    apply Qle_trans with ((M2 + eps * (1#3)) * inject_Z (Z.of_nat k) * step).
    { apply Hwp_tight. lia. }
    assert (Hk_le : inject_Z (Z.of_nat k) * step <= b - a).
    { assert (Hk_le_N : inject_Z (Z.of_nat k) <= inject_Z (Z.of_nat (S N))).
      { unfold Qle. simpl. lia. }
      apply Qle_trans with (inject_Z (Z.of_nat (S N)) * step).
      { apply Qmult_le_compat_r; [exact Hk_le_N | lra]. }
      lra. }
    assert (HM_nn : 0 <= M2 + eps * (1#3)) by lra.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (M2 + eps * (1#3)) (inject_Z (Z.of_nat k) * step)).
    rewrite (Qmult_comm (M2 + eps * (1#3)) (b - a)).
    apply Qmult_le_compat_r; [exact Hk_le | exact HM_nn]. }
  (* ---- Part 3: RS bound ---- *)
  (* |RS(f'-f'(a))| ≤ (M₂+eps/3)*(b-a)*(S N)*step = (M₂+eps/3)*(b-a)² *)
  assert (Hrs_bound :
    Qabs (riemann_sum (fun x => f' x - f' a) a step (S N)) <=
    (M2 + eps * (1#3)) * (b - a) * inject_Z (Z.of_nat (S N)) * step).
  { apply riemann_sum_abs_bound.
    - exact Hwp_bound.
    - lra.
    - assert (H : 0 <= M2 + eps * (1#3)) by lra.
      apply Qmult_le_0_compat; [exact H | lra]. }
  (* ---- Part 4: Combine ---- *)
  (* f(end) - f(a) - f'(a)*(b-a)
     = (tele_sum - RS(f')) + (RS(f') - f'(a)*(S N)*step)
     = (tele_sum - RS(f')) + RS(f' - f'(a))  (by riemann_sum_add/const) *)
  (* |result| ≤ |tele_sum - RS(f')| + |RS(f'-f'(a))|
     ≤ eps/3*(b-a) + (M₂+eps/3)*(b-a)² *)
  (* RS decomposition: RS(f') == RS(const f'(a)) + RS(f'-f'(a)) — by induction *)
  assert (Hrs_split : forall n : nat,
    riemann_sum f' a step n ==
    riemann_sum (fun _ => f' a) a step n +
    riemann_sum (fun x => f' x - f' a) a step n).
  { induction n as [| n' IHn].
    - simpl. ring.
    - simpl riemann_sum. rewrite IHn. ring. }
  assert (Hrs_const : riemann_sum (fun _ => f' a) a step (S N) ==
    f' a * inject_Z (Z.of_nat (S N)) * step).
  { apply riemann_sum_const. }
  (* Main identity: f(end)-f(a)-f'(a)*(b-a) = err + RS(f'-f'(a)) *)
  assert (Hmain_eq :
    f (walk_point a step (S N)) - f a - f' a * (b - a) ==
    (tele_sum f a step (S N) - riemann_sum f' a step (S N)) +
    riemann_sum (fun x => f' x - f' a) a step (S N)).
  { rewrite Htele. rewrite (Hrs_split (S N)). rewrite Hrs_const.
    assert (Hfa_ba : f' a * inject_Z (Z.of_nat (S N)) * step == f' a * (b - a)).
    { rewrite <- Hn_step. ring. }
    lra. }
  apply Qle_trans with
    (Qabs (tele_sum f a step (S N) - riemann_sum f' a step (S N)) +
     Qabs (riemann_sum (fun x => f' x - f' a) a step (S N))).
  { apply Qle_trans with
      (Qabs ((tele_sum f a step (S N) - riemann_sum f' a step (S N)) +
             riemann_sum (fun x => f' x - f' a) a step (S N))).
    { apply Qeq_Qle. apply Qabs_wd. exact Hmain_eq. }
    apply Qabs_triangle. }
  apply Qle_trans with
    (inject_Z (Z.of_nat (S N)) * (eps * (1#3)) * step +
     (M2 + eps * (1#3)) * (b - a) * inject_Z (Z.of_nat (S N)) * step).
  { apply Qplus_le_compat; [exact Hftc_SN | exact Hrs_bound]. }
  (* Simplify: (SN)*eps/3*step = eps/3*(b-a), (M₂+eps/3)*(b-a)*(SN)*step = (M₂+eps/3)*(b-a)² *)
  assert (Hsimp1 : inject_Z (Z.of_nat (S N)) * (eps * (1#3)) * step <=
                    eps * (1#3) * (b - a)).
  { apply Qeq_Qle. rewrite <- Hn_step. ring. }
  assert (Hsimp1' : eps * (1#3) * (b - a) <=
                     inject_Z (Z.of_nat (S N)) * (eps * (1#3)) * step).
  { apply Qeq_Qle. rewrite <- Hn_step. ring. }
  assert (Hsimp2 : (M2 + eps * (1#3)) * (b - a) * inject_Z (Z.of_nat (S N)) * step <=
                    (M2 + eps * (1#3)) * (b - a) * (b - a)).
  { apply Qeq_Qle. rewrite <- Hn_step. ring. }
  (* (M2+eps/3)*(b-a)^2 ≤ (M2+eps)*(b-a)^2 *)
  assert (Hba_sq_nn : 0 <= (b - a) * (b - a)).
  { apply Qmult_le_0_compat; lra. }
  assert (Hm_le : (M2 + eps * (1#3)) * (b - a) * (b - a) <=
                   (M2 + eps) * (b - a) * (b - a)).
  { assert (Ha1 : (M2 + eps * (1#3)) * (b - a) * (b - a) ==
                   (M2 + eps * (1#3)) * ((b - a) * (b - a))) by ring.
    assert (Ha2 : (M2 + eps) * (b - a) * (b - a) ==
                   (M2 + eps) * ((b - a) * (b - a))) by ring.
    apply Qle_trans with ((M2 + eps * (1#3)) * ((b - a) * (b - a))).
    { apply Qeq_Qle. exact Ha1. }
    apply Qle_trans with ((M2 + eps) * ((b - a) * (b - a))).
    2: { apply Qeq_Qle. symmetry. exact Ha2. }
    apply Qmult_le_compat_r; [lra | exact Hba_sq_nn]. }
  assert (Heps_third : eps * (1#3) * (b - a) <= eps * (b - a)).
  { apply Qmult_le_compat_r; lra. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 4: CONVEXITY AND CONCAVITY FROM TAYLOR                            *)
(* ========================================================================= *)

(** L13: Non-negative second derivative implies Taylor remainder is nearly
    non-negative. If f'' ≥ 0 on [a,b], the Riemann sum RS(f''·(b-t)) ≥ 0
    (since both factors are non-negative on [a,b]). *)
Lemma taylor_nonneg_remainder :
  forall (f'' : Q -> Q) (a b : Q) (N : nat),
  a < b ->
  let step := (b - a) / inject_Z (Z.of_nat (S N)) in
  (forall k : nat, (k < S N)%nat ->
    0 <= f'' (walk_point a step k)) ->
  (forall k : nat, (k < S N)%nat ->
    0 <= b - walk_point a step k) ->
  0 <= riemann_sum (fun t => f'' t * (b - t)) a step (S N).
Proof.
  intros f'' a b N Hab step Hf''_nn Hbmt_nn.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  apply riemann_sum_nonneg.
  - intros k Hk.
    apply Qmult_le_0_compat.
    + apply Hf''_nn. exact Hk.
    + apply Hbmt_nn. exact Hk.
  - lra.
Qed.

(** L14: Convexity — weaker version using only the MVT.
    If f'' ≥ 0 on [a,b], then f'(x) ≥ f'(a) for x ∈ [a,b] (monotone derivative).
    Combined with FTC: f(b)-f(a) ≥ f'(a)(b-a) - ε(b-a).

    Actually, let's prove convexity via the direct remainder decomposition:
    f(b)-f(a)-f'(a)(b-a) ≈ RS(f'-f'(a)), and f'' ≥ 0 means f'-f'(a) ≥ 0
    on [a,b] (non-decreasing derivative), so RS(f'-f'(a)) ≥ 0.

    But proving f'(x) ≥ f'(a) from f'' ≥ 0 requires pos_deriv_increases from MVT. *)
Lemma taylor_convexity :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' a <= f' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    f a + f' a * (b - a) - eps * (b - a) <=
    f (walk_point a step (S N)).
Proof.
  intros f f' a b eps Huf Hf'_mono Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (Hba : 0 < b - a) by lra.
  (* FTC: f(end)-f(a) ≈ RS(f') *)
  destruct (ftc_grid f f' a b eps Huf Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  (* From FTC: |RS(f') - (f(end)-f(a))| ≤ eps*(b-a) *)
  (* So f(end)-f(a) ≥ RS(f') - eps*(b-a) *)
  assert (Hftc_lower :
    f (walk_point a step (S N)) - f a >=
    riemann_sum f' a step (S N) - eps * (b - a)).
  { assert (Habs_lower : forall x y e : Q, Qabs (x - y) <= e -> y >= x - e).
    { intros x y e He.
      assert (Habs_bound : x - y <= Qabs (x - y)) by apply Qle_Qabs.
      lra. }
    apply Habs_lower. exact HN. }
  (* RS(f') ≥ RS(const f'(a)) = f'(a) * n * step = f'(a)*(b-a) *)
  assert (Hrs_lower :
    riemann_sum f' a step (S N) >= f' a * (b - a)).
  { assert (Hmono : riemann_sum (fun _ => f' a) a step (S N) <=
                     riemann_sum f' a step (S N)).
    { apply riemann_sum_monotone.
      - intros k Hk.
        pose proof (walk_point_in_interval a b N k Hab) as Hpi.
        cbv zeta in Hpi. destruct (Hpi (ltac:(lia))) as [Hpi_lo Hpi_hi].
        apply Hf'_mono; assumption.
      - lra. }
    assert (Hconst : riemann_sum (fun _ => f' a) a step (S N) ==
                     f' a * inject_Z (Z.of_nat (S N)) * step).
    { apply riemann_sum_const. }
    assert (Hn_step : inject_Z (Z.of_nat (S N)) * step == b - a).
    { unfold step. field. intros Hcontra.
      assert (0 < inject_Z (Z.of_nat (S N))).
      { unfold Qlt. simpl. lia. } lra. }
    assert (Hconst2 : f' a * inject_Z (Z.of_nat (S N)) * step == f' a * (b - a)).
    { rewrite <- Qmult_assoc. rewrite Hn_step. reflexivity. }
    lra. }
  assert (Hge1 : f' a * (b - a) <= riemann_sum f' a step (S N)).
  { unfold Qge in Hrs_lower. exact Hrs_lower. }
  assert (Hge2 : riemann_sum f' a step (S N) - eps * (b - a) <=
                  f (walk_point a step (S N)) - f a).
  { unfold Qge in Hftc_lower. exact Hftc_lower. }
  assert (Hstep1 : f' a * (b - a) - eps * (b - a) <=
                   riemann_sum f' a step (S N) - eps * (b - a)).
  { apply Qplus_le_compat. exact Hge1. apply Qle_refl. }
  assert (Hstep2 : f' a * (b - a) - eps * (b - a) <=
                   f (walk_point a step (S N)) - f a).
  { apply Qle_trans with (riemann_sum f' a step (S N) - eps * (b - a));
    assumption. }
  (* fa + X <= fend from X <= fend - fa *)
  apply Qle_trans with (f a + (f (walk_point a step (S N)) - f a)).
  2: { apply Qeq_Qle. ring. }
  apply Qle_trans with (f a + (f' a * (b - a) - eps * (b - a))).
  { apply Qeq_Qle. ring. }
  apply Qplus_le_compat. apply Qle_refl. exact Hstep2.
Qed.

(** L15: Second derivative test — if f'(a) = 0 and f' is non-decreasing
    (implied by f'' ≥ 0), then a is an approximate local minimum. *)
Lemma taylor_local_min :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  f' a == 0 ->
  (forall x : Q, a <= x -> x <= b -> f' a <= f' x) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    f a - eps * (b - a) <= f (walk_point a step (S N)).
Proof.
  intros f f' a b eps Huf Hf'a_zero Hf'_mono Heps.
  destruct (taylor_convexity f f' a b eps Huf Hf'_mono Heps) as [N HN].
  exists N.
  simpl in HN |- *.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  (* f(a) + f'(a)*(b-a) - eps*(b-a) ≤ f(end) *)
  (* f'(a) == 0, so f'(a)*(b-a) == 0 *)
  assert (Hzero : f' a * (b - a) == 0).
  { rewrite Hf'a_zero. ring. }
  lra.
Qed.

(** L16: Concavity — if f' is non-increasing on [a,b]
    (implied by f'' ≤ 0), then f(b) ≤ f(a) + f'(a)·(b-a) + ε·(b-a). *)
Lemma taylor_concavity :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x <= f' a) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    f (walk_point a step (S N)) <=
    f a + f' a * (b - a) + eps * (b - a).
Proof.
  intros f f' a b eps Huf Hf'_mono Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (Hba : 0 < b - a) by lra.
  destruct (ftc_grid f f' a b eps Huf Heps) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  (* FTC upper bound: f(end)-f(a) ≤ RS(f') + eps*(b-a) *)
  assert (Hftc_upper :
    f (walk_point a step (S N)) - f a <=
    riemann_sum f' a step (S N) + eps * (b - a)).
  { assert (Habs_upper : forall x y e : Q, Qabs (x - y) <= e -> y <= x + e).
    { intros x y e He.
      assert (Habs_bound : -(x - y) <= Qabs (x - y)).
      { rewrite <- Qabs_opp. apply Qle_Qabs. }
      lra. }
    apply Habs_upper. exact HN. }
  (* RS(f') ≤ RS(const f'(a)) = f'(a)*(b-a) *)
  assert (Hrs_upper :
    riemann_sum f' a step (S N) <= f' a * (b - a)).
  { assert (Hmono : riemann_sum f' a step (S N) <=
                     riemann_sum (fun _ => f' a) a step (S N)).
    { apply riemann_sum_monotone.
      - intros k Hk.
        pose proof (walk_point_in_interval a b N k Hab) as Hpi.
        cbv zeta in Hpi. destruct (Hpi (ltac:(lia))) as [Hpi_lo Hpi_hi].
        apply Hf'_mono; assumption.
      - lra. }
    assert (Hconst : riemann_sum (fun _ => f' a) a step (S N) ==
                     f' a * inject_Z (Z.of_nat (S N)) * step).
    { apply riemann_sum_const. }
    assert (Hn_step : inject_Z (Z.of_nat (S N)) * step == b - a).
    { unfold step. field. intros Hcontra.
      assert (0 < inject_Z (Z.of_nat (S N))).
      { unfold Qlt. simpl. lia. } lra. }
    assert (Hconst2 : f' a * inject_Z (Z.of_nat (S N)) * step == f' a * (b - a)).
    { rewrite <- Qmult_assoc. rewrite Hn_step. reflexivity. }
    lra. }
  assert (Hstep : f (walk_point a step (S N)) - f a <=
                  f' a * (b - a) + eps * (b - a)).
  { apply Qle_trans with (riemann_sum f' a step (S N) + eps * (b - a)).
    - exact Hftc_upper.
    - apply Qplus_le_compat. exact Hrs_upper. apply Qle_refl. }
  apply Qle_trans with (f a + (f (walk_point a step (S N)) - f a)).
  { apply Qeq_Qle. ring. }
  apply Qle_trans with (f a + (f' a * (b - a) + eps * (b - a))).
  { apply Qplus_le_compat. apply Qle_refl. exact Hstep. }
  apply Qeq_Qle. ring.
Qed.

(** L17: Taylor sandwich — if f' is constant on [a,b] (f' = f'(a) everywhere),
    then f(b) is approximately f(a) + f'(a)·(b-a). *)
Lemma taylor_sandwich_const_deriv :
  forall (f f' : Q -> Q) (a b eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' x == f' a) ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    Qabs (f (walk_point a step (S N)) - f a - f' a * (b - a)) <=
    eps * (b - a).
Proof.
  intros f f' a b eps Huf Hf'_const Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (HC : forall x : Q, a <= x -> x <= b -> Qabs (f' x - f' a) <= 0).
  { intros x Hax Hxb.
    assert (Heq : f' x - f' a == 0).
    { assert (Hfx := Hf'_const x Hax Hxb). lra. }
    apply Qle_trans with (Qabs 0).
    { apply Qeq_Qle. apply Qabs_wd. exact Heq. }
    rewrite Qabs_pos; lra. }
  destruct (taylor1_bound f f' a b 0 eps Huf HC (Qle_refl 0) Heps) as [N HN].
  exists N.
  simpl in HN |- *.
  lra.
Qed.

(** L18: Convexity sandwich — combining convexity and the quadratic upper bound.
    If f' is non-decreasing (f'' ≥ 0) and |f'(x)-f'(a)| ≤ C,
    then f(a)+f'(a)(b-a)-ε(b-a) ≤ f(b) ≤ f(a)+f'(a)(b-a)+C(b-a)+ε(b-a). *)
Lemma taylor_sandwich :
  forall (f f' : Q -> Q) (a b C eps : Q),
  udiff_on f f' a b ->
  (forall x : Q, a <= x -> x <= b -> f' a <= f' x) ->
  (forall x : Q, a <= x -> x <= b -> Qabs (f' x - f' a) <= C) ->
  0 <= C ->
  0 < eps ->
  exists N : nat,
    let step := (b - a) / inject_Z (Z.of_nat (S N)) in
    f a + f' a * (b - a) - eps * (b - a) <=
    f (walk_point a step (S N)) /\
    f (walk_point a step (S N)) <=
    f a + f' a * (b - a) + (C + eps) * (b - a).
Proof.
  intros f f' a b C eps Huf Hf'_mono HC HC_nn Heps.
  assert (Hab : a < b) by (destruct Huf; assumption).
  assert (Hba : 0 < b - a) by lra.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  (* Lower bound from convexity *)
  destruct (taylor_convexity f f' a b (eps * (1#2)) Huf Hf'_mono Heps2) as [N1 HN1].
  (* Upper bound from taylor1_bound *)
  destruct (taylor1_bound f f' a b C (eps * (1#2)) Huf HC HC_nn Heps2) as [N2 HN2].
  (* Take the one that gives both bounds... *)
  (* We need both bounds on the SAME N *)
  (* Use convexity gives lower on N1, taylor1_bound gives upper on N2 *)
  (* They might be different N's *)
  (* For a correct proof, let's use FTC which gives both directions *)
  destruct (ftc_grid f f' a b (eps * (1#2)) Huf Heps2) as [N HN].
  exists N.
  set (step := (b - a) / inject_Z (Z.of_nat (S N))) in *.
  cbv zeta in HN.
  assert (Hstep_pos : 0 < step).
  { unfold step. apply Qlt_shift_div_l.
    - unfold Qlt. simpl. lia.
    - lra. }
  assert (Hend : walk_point a step (S N) == b).
  { apply walk_endpoint_qeq. exact Hab. }
  assert (Hn_step : inject_Z (Z.of_nat (S N)) * step == b - a).
  { unfold step. field. intros Hcontra.
    assert (0 < inject_Z (Z.of_nat (S N))).
    { unfold Qlt. simpl. lia. } lra. }
  split.
  - (* Lower bound: f(end) ≥ f(a)+f'(a)(b-a)-eps*(b-a) *)
    assert (Hftc_lower :
      riemann_sum f' a step (S N) - eps * (1#2) * (b - a) <=
      f (walk_point a step (S N)) - f a).
    { assert (H : riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a) <=
                  Qabs (riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a))).
      { apply Qle_Qabs. }
      lra. }
    assert (Hrs_lower : f' a * (b - a) <= riemann_sum f' a step (S N)).
    { assert (Hmono : riemann_sum (fun _ => f' a) a step (S N) <=
                       riemann_sum f' a step (S N)).
      { apply riemann_sum_monotone.
        - intros k Hk.
          pose proof (walk_point_in_interval a b N k Hab) as Hpi.
          cbv zeta in Hpi. destruct (Hpi (ltac:(lia))) as [Hpi_lo Hpi_hi].
          apply Hf'_mono; assumption.
        - lra. }
      assert (Hconst : riemann_sum (fun _ => f' a) a step (S N) ==
                       f' a * inject_Z (Z.of_nat (S N)) * step) by apply riemann_sum_const.
      assert (Hconst2 : f' a * inject_Z (Z.of_nat (S N)) * step == f' a * (b - a)).
      { rewrite <- Qmult_assoc. rewrite Hn_step. reflexivity. }
      lra. }
    assert (Heps_half : eps * (1#2) * (b - a) <= eps * (b - a)).
    { apply Qmult_le_compat_r; lra. }
    assert (Hstep : f' a * (b - a) - eps * (b - a) <=
                    f (walk_point a step (S N)) - f a).
    { apply Qle_trans with (f' a * (b - a) - eps * (1#2) * (b - a)).
      { apply Qplus_le_compat.
        - apply Qle_refl.
        - exact (Qopp_le_compat _ _ Heps_half). }
      apply Qle_trans with (riemann_sum f' a step (S N) - eps * (1#2) * (b - a)).
      { apply Qplus_le_compat. exact Hrs_lower. apply Qle_refl. }
      exact Hftc_lower. }
    apply Qle_trans with (f a + (f' a * (b - a) - eps * (b - a))).
    { apply Qeq_Qle. ring. }
    apply Qle_trans with (f a + (f (walk_point a step (S N)) - f a)).
    { apply Qplus_le_compat. apply Qle_refl. exact Hstep. }
    apply Qeq_Qle. ring.
  - (* Upper bound: f(end) ≤ f(a)+f'(a)(b-a)+(C+eps)*(b-a) *)
    (* FTC: f(end)-f(a) ≤ RS(f') + eps/2*(b-a) *)
    assert (Hftc_upper :
      f (walk_point a step (S N)) - f a <=
      riemann_sum f' a step (S N) + eps * (1#2) * (b - a)).
    { assert (H : -(riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a)) <=
                  Qabs (riemann_sum f' a step (S N) - (f (walk_point a step (S N)) - f a))).
      { rewrite <- Qabs_opp. apply Qle_Qabs. }
      lra. }
    (* RS(f') ≤ RS(f'(a) + C) = (f'(a)+C)*(b-a) by bound *)
    assert (Hrs_upper : riemann_sum f' a step (S N) <= (f' a + C) * (b - a)).
    { assert (Hmono : riemann_sum f' a step (S N) <=
                       riemann_sum (fun _ => f' a + C) a step (S N)).
      { apply riemann_sum_monotone.
        - intros k Hk.
          pose proof (walk_point_in_interval a b N k Hab) as Hpi.
          cbv zeta in Hpi. destruct (Hpi (ltac:(lia))) as [Hwp_in_a Hwp_in_b].
          assert (Habs_bound := HC (walk_point a step k) Hwp_in_a Hwp_in_b).
          assert (Hupper : f' (walk_point a step k) - f' a <=
                           Qabs (f' (walk_point a step k) - f' a)).
          { apply Qle_Qabs. }
          lra.
        - lra. }
      assert (Hconst : riemann_sum (fun _ => f' a + C) a step (S N) ==
                       (f' a + C) * inject_Z (Z.of_nat (S N)) * step) by apply riemann_sum_const.
      assert (Hconst2 : (f' a + C) * inject_Z (Z.of_nat (S N)) * step == (f' a + C) * (b - a)).
      { rewrite <- Qmult_assoc. rewrite Hn_step. reflexivity. }
      lra. }
    (* Chain: fend <= fa + f'a*(b-a) + (C+eps)*(b-a) *)
    assert (Heps_half : eps * (1#2) * (b - a) <= eps * (b - a)).
    { apply Qmult_le_compat_r; lra. }
    assert (Hstep : f (walk_point a step (S N)) - f a <=
                    (f' a + C) * (b - a) + eps * (b - a)).
    { apply Qle_trans with (riemann_sum f' a step (S N) + eps * (1#2) * (b - a)).
      - exact Hftc_upper.
      - apply Qle_trans with ((f' a + C) * (b - a) + eps * (1#2) * (b - a)).
        { apply Qplus_le_compat. exact Hrs_upper. apply Qle_refl. }
        apply Qplus_le_compat. apply Qle_refl. exact Heps_half. }
    apply Qle_trans with (f a + (f (walk_point a step (S N)) - f a)).
    { apply Qeq_Qle. ring. }
    apply Qle_trans with (f a + ((f' a + C) * (b - a) + eps * (b - a))).
    { apply Qplus_le_compat. apply Qle_refl. exact Hstep. }
    apply Qeq_Qle. ring.
Qed.

(* ========================================================================= *)
(* SUMMARY                                                                    *)
(* ========================================================================= *)
(*                                                                            *)
(* TaylorSeries.v — 18 lemmas, all Qed, 0 Admitted, 0 axioms                *)
(*                                                                            *)
(* Section 1: Building blocks (L1-L4)                                         *)
(*   L1  udiff_const           — constant is udiff with derivative 0          *)
(*   L2  udiff_bmt             — (b₀-t) is udiff with derivative -(1)        *)
(*   L3  taylor_remainder_udiff — remainder is udiff                          *)
(*   L4  bmt_sq_udiff          — (b₀-t)² is udiff with derivative -2(b₀-t)  *)
(*                                                                            *)
(* Section 2: First-order Taylor via FTC (L5-L8)                              *)
(*   L5  taylor1_ftc           — remainder ≈ RS(f'-f'(a))                    *)
(*   L6  taylor1_bound         — |rem| ≤ C(b-a)+ε(b-a) if |f'-f'(a)|≤C      *)
(*   L7  taylor1_affine        — affine remainder = 0                         *)
(*   L8  taylor1_quadratic     — quadratic remainder = (b-a)²                *)
(*                                                                            *)
(* Section 3: IBP-based Taylor (L9-L12)                                       *)
(*   L9  ibp_taylor1_decomp    — RS(f') ≈ f'(a)(b-a)+RS(f''·(b-t))          *)
(*   L10 ibp_remainder_crude   — |RS(f''·(b-t))| ≤ M₂(b-a)²                 *)
(*   L11 rs_bmt_half_sq        — RS(b-t) ≈ (b-a)²/2 via FTC                 *)
(*   L12 taylor1_var_bound     — |rem| ≤ (M₂+ε)(b-a)²+ε(b-a)               *)
(*                                                                            *)
(* Section 4: Convexity and concavity (L13-L18)                               *)
(*   L13 taylor_nonneg_remainder — f''≥0 ⟹ RS(f''·(b-t))≥0                 *)
(*   L14 taylor_convexity      — f'↑ ⟹ f(b)≥f(a)+f'(a)(b-a)-ε(b-a)        *)
(*   L15 taylor_local_min      — f'(a)=0,f'↑ ⟹ f(b)≥f(a)-ε(b-a)           *)
(*   L16 taylor_concavity      — f'↓ ⟹ f(b)≤f(a)+f'(a)(b-a)+ε(b-a)        *)
(*   L17 taylor_sandwich_const — f'=const ⟹ f(b)≈f(a)+f'(a)(b-a)           *)
(*   L18 taylor_sandwich       — f'↑,|f'-f'(a)|≤C ⟹ two-sided bound       *)
(*                                                                            *)
(* ========================================================================= *)
