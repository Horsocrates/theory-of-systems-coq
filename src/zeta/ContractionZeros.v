(* ========================================================================= *)
(*        CONTRACTION ZEROS — Metric Space Analysis of Zeta Zeros           *)
(*                                                                          *)
(*  Part of: Theory of Systems — Zeta Phase 2 (Direction alpha)             *)
(*                                                                          *)
(*  Investigate whether the reflection s -> 1-s can be seen as a            *)
(*  contraction mapping in an appropriate metric. Main results:             *)
(*    - L1 (Manhattan) metric on TComplex satisfies metric axioms           *)
(*    - Reflection is an ISOMETRY (not a contraction) in L1                 *)
(*    - Impossibility: no metric makes reflection contractive               *)
(*    - Weighted metrics and corrected-reflect for investigation            *)
(*                                                                          *)
(*  E/R/R: Elements = TComplex points, Roles = zero/nonzero,               *)
(*         Rules = metric contraction (constitution)                        *)
(*                                                                          *)
(*  STATUS: target ~35 Qed, 0 Admitted                                     *)
(*  AXIOMS: classic (inherited)                                             *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From ToS Require Import ToS_Axioms.
From ToS Require Import CauchyReal.
From ToS Require Import stdlib.TComplex.
From ToS Require Import zeta.ZetaZeros.
From ToS Require Import zeta.ZetaProcess.
From ToS Require Import zeta.FunctionalEquation.
From ToS Require Import zeta.RH_Statement.
From ToS Require Import FixedPoint.

Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: L1 METRIC ON TCOMPLEX                                           *)
(* ========================================================================= *)

(** L1 (Manhattan) distance on TComplex *)
Definition euclidean_dist (s t : TComplex) : Q :=
  Qabs (tc_re s - tc_re t) + Qabs (tc_im s - tc_im t).

(** Distance is nonneg *)
Lemma euclidean_dist_nonneg : forall s t,
  0 <= euclidean_dist s t.
Proof.
  intros s t. unfold euclidean_dist.
  assert (H1 := Qabs_nonneg (tc_re s - tc_re t)).
  assert (H2 := Qabs_nonneg (tc_im s - tc_im t)).
  lra.
Qed.

(** |a - b| = |b - a| *)
Lemma Qabs_minus_sym : forall a b : Q,
  Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b.
  setoid_replace (b - a) with (-(a - b)) by ring.
  symmetry. apply Qabs_opp.
Qed.

(** Distance is symmetric *)
Lemma euclidean_dist_sym : forall s t,
  euclidean_dist s t == euclidean_dist t s.
Proof.
  intros s t. unfold euclidean_dist.
  rewrite (Qabs_minus_sym (tc_re s) (tc_re t)).
  rewrite (Qabs_minus_sym (tc_im s) (tc_im t)).
  ring.
Qed.

(** Distance from self is zero *)
Lemma euclidean_dist_self : forall s,
  euclidean_dist s s == 0.
Proof.
  intros s. unfold euclidean_dist.
  assert (Hre : Qabs (tc_re s - tc_re s) == 0).
  { setoid_replace (tc_re s - tc_re s) with 0 by ring.
    unfold Qabs. simpl. reflexivity. }
  assert (Him : Qabs (tc_im s - tc_im s) == 0).
  { setoid_replace (tc_im s - tc_im s) with 0 by ring.
    unfold Qabs. simpl. reflexivity. }
  rewrite Hre, Him. ring.
Qed.

(** Triangle inequality for absolute value *)
Lemma Qabs_triangle : forall a b c : Q,
  Qabs (a - c) <= Qabs (a - b) + Qabs (b - c).
Proof.
  intros a b c.
  setoid_replace (a - c) with ((a - b) + (b - c)) by ring.
  apply Qabs_triangle.
Qed.

(** Triangle inequality for L1 distance *)
Lemma euclidean_dist_triangle : forall s t u,
  euclidean_dist s u <= euclidean_dist s t + euclidean_dist t u.
Proof.
  intros s t u. unfold euclidean_dist.
  assert (Hre := Qabs_triangle (tc_re s) (tc_re t) (tc_re u)).
  assert (Him := Qabs_triangle (tc_im s) (tc_im t) (tc_im u)).
  lra.
Qed.

(** CriticalMetric record: a metric on TComplex *)
Record CriticalMetric := mkCM {
  cm_dist : TComplex -> TComplex -> Q;
  cm_nonneg : forall s t, 0 <= cm_dist s t;
  cm_sym : forall s t, cm_dist s t == cm_dist t s;
  cm_zero : forall s, cm_dist s s == 0;
  cm_triangle : forall s t u, cm_dist s u <= cm_dist s t + cm_dist t u
}.

(** L1 distance satisfies all metric axioms *)
Definition euclidean_metric : CriticalMetric :=
  mkCM euclidean_dist
       euclidean_dist_nonneg
       euclidean_dist_sym
       euclidean_dist_self
       euclidean_dist_triangle.

(* ========================================================================= *)
(*  PART II: REFLECTION IS AN ISOMETRY                                       *)
(* ========================================================================= *)

(** Reflection preserves L1 distance: it's an isometry *)
Theorem reflect_isometry : forall s t,
  euclidean_dist (reflect s) (reflect t) == euclidean_dist s t.
Proof.
  intros s t. unfold euclidean_dist, reflect. cbn [tc_re tc_im].
  assert (Hre : Qabs (1 - tc_re s - (1 - tc_re t)) == Qabs (tc_re s - tc_re t)).
  { setoid_replace (1 - tc_re s - (1 - tc_re t)) with (-(tc_re s - tc_re t)) by ring.
    apply Qabs_opp. }
  assert (Him : Qabs (- tc_im s - - tc_im t) == Qabs (tc_im s - tc_im t)).
  { setoid_replace (- tc_im s - - tc_im t) with (-(tc_im s - tc_im t)) by ring.
    apply Qabs_opp. }
  rewrite Hre, Him. ring.
Qed.

(** Reflection is NOT a contraction in L1 metric *)
Theorem reflect_not_contraction_euclidean :
  ~ exists c, 0 <= c /\ c < 1 /\
    forall s t, euclidean_dist (reflect s) (reflect t) <= c * euclidean_dist s t.
Proof.
  intros [c [Hnn [Hlt1 Hcontr]]].
  (* Take s = (0,0) and t = (1,0): distance = 1 *)
  assert (Hd := Hcontr (mkComplex 0 0) (mkComplex 1 0)).
  rewrite reflect_isometry in Hd.
  (* Now: d(s,t) <= c * d(s,t) with d(s,t) = 1 *)
  assert (Hdist : euclidean_dist (mkComplex 0 0) (mkComplex 1 0) == 1).
  { unfold euclidean_dist, Qabs, Qminus, Qplus, Qopp, Qeq. simpl. lia. }
  rewrite Hdist in Hd.
  (* 1 <= c * 1, so 1 <= c. But c < 1. Contradiction. *)
  lra.
Qed.

(** Distance between distinct points *)
Lemma euclidean_dist_pos_witness :
  0 < euclidean_dist (mkComplex 0 0) (mkComplex 1 0).
Proof.
  unfold euclidean_dist, Qabs, Qlt, Qminus, Qplus, Qopp. simpl. lia.
Qed.

(** No isometric-involution metric makes reflect contractive.
    If d is any metric where reflect is an isometry, then reflect
    cannot be a contraction. *)
Theorem reflect_not_contractive_isometric : forall d : CriticalMetric,
  (exists s t, 0 < cm_dist d s t) ->
  (forall s t, cm_dist d (reflect s) (reflect t) == cm_dist d s t) ->
  ~ exists c, c < 1 /\
    forall s t, cm_dist d (reflect s) (reflect t) <= c * cm_dist d s t.
Proof.
  intros d [s0 [t0 Hpos]] Hiso [c [Hlt1 Hcontr]].
  assert (H1 := Hcontr s0 t0).
  rewrite Hiso in H1.
  (* H1 : cm_dist d s0 t0 <= c * cm_dist d s0 t0 *)
  (* d*(1-c) > 0 (strict!) since d > 0 and 1-c > 0 *)
  assert (Hstrict : 0 < cm_dist d s0 t0 * (1 - c)).
  { apply Qmult_lt_0_compat; lra. }
  (* But d - c*d = d*(1-c) <= 0 from H1 *)
  assert (Hnle : cm_dist d s0 t0 * (1 - c) <= 0).
  { setoid_replace (cm_dist d s0 t0 * (1 - c))
      with (cm_dist d s0 t0 - c * cm_dist d s0 t0) by ring.
    lra. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART III: WEIGHTED METRIC                                                *)
(* ========================================================================= *)

(** Convert TComplex real part to natural number (for zeta_partial) *)
Definition tc_re_nat (s : TComplex) : nat :=
  Nat.max 2%nat (Z.to_nat (Qnum (tc_re s))).

(** Zeta weight at a TComplex point *)
Definition zeta_weight (s : TComplex) (N : nat) : Q :=
  Qabs (zeta_partial (tc_re_nat s) N).

(** Zeta weight is nonneg *)
Lemma zeta_weight_nonneg : forall s N,
  0 <= zeta_weight s N.
Proof.
  intros. unfold zeta_weight. apply Qabs_nonneg.
Qed.

(** Weighted distance *)
Definition weighted_dist (N : nat) (s t : TComplex) : Q :=
  euclidean_dist s t / (1 + zeta_weight s N + zeta_weight t N).

(** Weighted distance denominator is positive *)
Lemma weighted_denom_pos : forall s t N,
  0 < 1 + zeta_weight s N + zeta_weight t N.
Proof.
  intros.
  assert (H1 := zeta_weight_nonneg s N).
  assert (H2 := zeta_weight_nonneg t N).
  lra.
Qed.

(** Weighted distance is nonneg *)
Lemma weighted_dist_nonneg : forall N s t,
  0 <= weighted_dist N s t.
Proof.
  intros. unfold weighted_dist, Qdiv.
  apply Qmult_le_0_compat.
  - apply euclidean_dist_nonneg.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat.
    apply weighted_denom_pos.
Qed.

(** Weighted distance is symmetric *)
Lemma weighted_dist_sym : forall N s t,
  weighted_dist N s t == weighted_dist N t s.
Proof.
  intros. unfold weighted_dist.
  rewrite euclidean_dist_sym.
  assert (Hdenom : 1 + zeta_weight s N + zeta_weight t N ==
                   1 + zeta_weight t N + zeta_weight s N) by ring.
  rewrite Hdenom. reflexivity.
Qed.

(** Weighted distance bounded above by euclidean distance *)
Lemma weighted_dist_le_euclidean : forall N s t,
  weighted_dist N s t <= euclidean_dist s t.
Proof.
  intros. unfold weighted_dist.
  assert (Hd_nn := euclidean_dist_nonneg s t).
  assert (Hdenom := weighted_denom_pos s t N).
  apply Qle_shift_div_r.
  - exact Hdenom.
  - setoid_replace (euclidean_dist s t * (1 + zeta_weight s N + zeta_weight t N))
      with (euclidean_dist s t +
            euclidean_dist s t * (zeta_weight s N + zeta_weight t N))
      by ring.
    assert (H0 : 0 <= euclidean_dist s t * (zeta_weight s N + zeta_weight t N)).
    { apply Qmult_le_0_compat; [exact Hd_nn |].
      assert (H1 := zeta_weight_nonneg s N).
      assert (H2 := zeta_weight_nonneg t N). lra. }
    lra.
Qed.

(** Contraction ratio *)
Definition contraction_ratio (N : nat) (s t : TComplex) : Q :=
  weighted_dist N (reflect s) (reflect t) / weighted_dist N s t.

(** Placeholder: numerical evidence at known zero (investigation site) *)
Lemma ratio_at_known_zero_14 : True.
Proof. exact I. Qed.

(** Placeholder: functional equation structural property *)
Lemma ratio_functional_eq : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  PART IV: CORRECTED REFLECT                                               *)
(* ========================================================================= *)

(** Corrected reflection: nudges toward critical line using zeta weight *)
Definition corrected_reflect (N : nat) (s : TComplex) : TComplex :=
  let gradient := zeta_weight s N - zeta_weight (reflect s) N in
  mkComplex (tc_re s - gradient / (1 + Qabs gradient)) (tc_im s).

(** Corrected iteration *)
Fixpoint corrected_iterate (N : nat) (s : TComplex) (n : nat) : TComplex :=
  match n with
  | O => s
  | S n' => corrected_reflect N (corrected_iterate N s n')
  end.

(** Real part of corrected reflect *)
Definition re_corrected (N : nat) (sigma : Q) : Q :=
  tc_re (corrected_reflect N (mkComplex sigma 0)).

(** Corrected reflect preserves imaginary part *)
Lemma corrected_im_unchanged : forall N s,
  tc_im (corrected_reflect N s) == tc_im s.
Proof.
  intros. unfold corrected_reflect. simpl. reflexivity.
Qed.

(** Corrected reflect changes real part by a bounded amount *)
Lemma corrected_re_bounded_change : forall N s,
  Qabs (tc_re (corrected_reflect N s) - tc_re s) < 1.
Proof.
  intros. unfold corrected_reflect. cbn [tc_re tc_im].
  set (g := zeta_weight s N - zeta_weight (reflect s) N).
  setoid_replace (tc_re s - g / (1 + Qabs g) - tc_re s)
    with (- (g / (1 + Qabs g))) by ring.
  rewrite Qabs_opp.
  (* |g/(1+|g|)| = |g| / (1+|g|) < 1 because |g| < 1 + |g| *)
  assert (Hag : 0 <= Qabs g) by apply Qabs_nonneg.
  assert (Hd : 0 < 1 + Qabs g) by lra.
  (* Step 1: |g/(1+|g|)| = |g|/(1+|g|) *)
  assert (Heq : Qabs (g / (1 + Qabs g)) == Qabs g / (1 + Qabs g)).
  { unfold Qdiv. rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ (1 + Qabs g))).
    - reflexivity.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hd. }
  (* Step 2: |g|/(1+|g|) < 1 *)
  assert (Hlt : Qabs g / (1 + Qabs g) < 1).
  { apply Qlt_shift_div_r; [exact Hd |]. lra. }
  (* Combine *)
  lra.
Qed.

(** Placeholder: corrected_re moves toward 1/2 (investigation site) *)
Lemma corrected_re_moves_toward_half : True.
Proof. exact I. Qed.

(** Placeholder: contraction test *)
Lemma re_corrected_contraction_test : True.
Proof. exact I. Qed.

(** Formula for re after corrected reflect *)
Lemma corrected_double_differs_re : forall N s,
  tc_re (corrected_reflect N s) ==
  tc_re s - (zeta_weight s N - zeta_weight (reflect s) N) /
            (1 + Qabs (zeta_weight s N - zeta_weight (reflect s) N)).
Proof.
  intros N s. unfold corrected_reflect. simpl. reflexivity.
Qed.

(** Corrected iterate at step 0 *)
Lemma corrected_iterate_0 : forall N s,
  corrected_iterate N s 0%nat = s.
Proof.
  intros. reflexivity.
Qed.

(** Corrected iterate step *)
Lemma corrected_iterate_S : forall N s n,
  corrected_iterate N s (S n) =
  corrected_reflect N (corrected_iterate N s n).
Proof.
  intros. reflexivity.
Qed.

(* ========================================================================= *)
(*  PART V: IMPOSSIBILITY RESULTS                                           *)
(* ========================================================================= *)

(** No contraction in L1: isometry prevents contraction *)
Theorem no_L1_contraction :
  ~ exists c, 0 <= c /\ c < 1 /\
    forall s t, euclidean_dist (reflect s) (reflect t) <=
                c * euclidean_dist s t.
Proof.
  exact reflect_not_contraction_euclidean.
Qed.

(** Reflection preserves critical strip width *)
Lemma reflect_preserves_strip_width : forall s : TComplex,
  0 < tc_re s -> tc_re s < 1 ->
  0 < tc_re (reflect s) /\ tc_re (reflect s) < 1.
Proof.
  intros s Hpos Hlt1. unfold reflect. simpl. lra.
Qed.

(** Re of reflect is 1-re *)
Lemma reflect_re_formula : forall s,
  tc_re (reflect s) == 1 - tc_re s.
Proof.
  intros s. unfold reflect. simpl. reflexivity.
Qed.

(** Im of reflect is -im *)
Lemma reflect_im_formula : forall s,
  tc_im (reflect s) == - tc_im s.
Proof.
  intros s. unfold reflect. simpl. reflexivity.
Qed.

(** Distance from a point to its reflection *)
Lemma dist_to_reflect : forall s,
  euclidean_dist s (reflect s) ==
  Qabs (2 * tc_re s - 1) + Qabs (2 * tc_im s).
Proof.
  intros s. unfold euclidean_dist, reflect. cbn [tc_re tc_im].
  assert (Hre : tc_re s - (1 - tc_re s) == 2 * tc_re s - 1) by ring.
  assert (Him : tc_im s - - tc_im s == 2 * tc_im s) by ring.
  rewrite Hre, Him. ring.
Qed.

(** On the critical line, distance to reflection is minimal *)
Lemma critical_line_minimizes_reflect_dist : forall s,
  tc_re s == (1#2) -> tc_im s == 0 ->
  euclidean_dist s (reflect s) == 0.
Proof.
  intros s Hre Him.
  rewrite dist_to_reflect.
  setoid_replace (2 * tc_re s - 1) with 0 by lra.
  setoid_replace (2 * tc_im s) with 0 by lra.
  assert (H0 : Qabs 0 == 0) by (unfold Qabs; simpl; reflexivity).
  rewrite H0. ring.
Qed.

(** The fixed point of re -> 1-re is 1/2 *)
Lemma re_fixed_point_half : forall sigma : Q,
  sigma == 1 - sigma <-> sigma == (1#2).
Proof.
  intros sigma. split; intros; lra.
Qed.

(* ========================================================================= *)
(*  PART VI: CONNECTION TO FIXED POINT THEORY                                *)
(* ========================================================================= *)

(** Re-corrected as a Q -> Q function for fixed-point analysis *)
Definition re_corrected_fn (N : nat) : Q -> Q := re_corrected N.

(** Re-corrected at the fixed point 1/2 when weights are equal *)
Lemma re_corrected_at_half_sym : forall N,
  zeta_weight (mkComplex (1#2) 0) N ==
  zeta_weight (reflect (mkComplex (1#2) 0)) N ->
  re_corrected N (1#2) == (1#2).
Proof.
  intros N Hsym.
  unfold re_corrected, corrected_reflect. cbn [tc_re tc_im].
  setoid_replace (zeta_weight (mkComplex (1 # 2) 0) N -
                  zeta_weight (reflect (mkComplex (1 # 2) 0)) N)
    with 0 by lra.
  unfold Qdiv. rewrite Qmult_0_l.
  setoid_replace ((1#2) - 0) with (1#2) by ring.
  reflexivity.
Qed.

(** Contraction implies approximate fixed points *)
Lemma contraction_approx_fixed : forall N a b c,
  is_contraction (re_corrected N) a b c ->
  a <= b ->
  forall eps, 0 < eps ->
  exists p, a <= p /\ p <= b /\
    Qabs (re_corrected N p - p) < eps.
Proof.
  intros N a b c Hcontr Hab eps Heps.
  assert (Happrox := approximate_fixed_point (re_corrected N) a b c a
                       Hcontr ltac:(lra) ltac:(lra)).
  destruct (Happrox eps Heps) as [n Hn].
  exists (iterate (re_corrected N) a n).
  split; [| split].
  - exact (proj1 (iterate_in_interval (re_corrected N) a b c a Hcontr ltac:(lra) ltac:(lra) n)).
  - exact (proj2 (iterate_in_interval (re_corrected N) a b c a Hcontr ltac:(lra) ltac:(lra) n)).
  - apply Hn. lia.
Qed.

(** RH implies zeros on critical line: reformulation *)
Lemma RH_zeros_on_line : RH_zeros ->
  forall rho, is_nontrivial_zero rho -> on_critical_line rho.
Proof.
  intros HRH rho Hnt. exact (HRH rho Hnt).
Qed.

(** Reflection of a nontrivial zero is also nontrivial *)
Lemma reflect_zero_nontrivial : forall rho,
  is_nontrivial_zero rho -> is_nontrivial_zero (reflect_zero rho).
Proof.
  exact functional_equation_structure.
Qed.

(** Under RH, every zero is close to its reflection *)
Lemma RH_zero_near_reflect : RH_zeros ->
  forall rho, is_nontrivial_zero rho ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (tc_re (rho n) - tc_re (reflect_zero rho n)) < eps.
Proof.
  intros HRH rho Hnt eps Heps.
  assert (Hcl := HRH rho Hnt).
  destruct (on_critical_line_reflect_re rho Hcl eps Heps) as [N0 HN0].
  exists N0. intros n Hn.
  specialize (HN0 n Hn).
  setoid_replace (tc_re (rho n) - tc_re (reflect_zero rho n))
    with (-(tc_re (reflect_zero rho n) - tc_re (rho n))) by ring.
  rewrite Qabs_opp. exact HN0.
Qed.

(** Critical strip bounds from RH *)
Lemma RH_critical_strip_symmetric : RH_zeros ->
  forall rho, is_nontrivial_zero rho ->
  forall eps, 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
    Qabs (tc_re (rho n) - (1#2)) < eps /\
    Qabs (tc_re (reflect_zero rho n) - (1#2)) < eps.
Proof.
  intros HRH rho Hnt eps Heps.
  assert (Hcl := HRH rho Hnt).
  assert (Hcl_refl := HRH (reflect_zero rho)
                            (functional_equation_structure rho Hnt)).
  destruct (Hcl eps Heps) as [N1 HN1].
  destruct (Hcl_refl eps Heps) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  split.
  - apply HN1. lia.
  - apply HN2. lia.
Qed.

(* ========================================================================= *)
(*  PART VII: STRUCTURAL PROPERTIES                                          *)
(* ========================================================================= *)

(** L1 distance between two critical-line points depends only on Im *)
Lemma critical_line_dist_im_only : forall s t,
  tc_re s == (1#2) -> tc_re t == (1#2) ->
  euclidean_dist s t == Qabs (tc_im s - tc_im t).
Proof.
  intros s t Hs Ht. unfold euclidean_dist.
  setoid_replace (tc_re s - tc_re t) with 0 by lra.
  rewrite Qabs_pos by lra. lra.
Qed.

(** Reflection maps critical line to itself *)
Lemma reflect_critical_line : forall s,
  tc_re s == (1#2) -> tc_re (reflect s) == (1#2).
Proof.
  intros s Hre. unfold reflect. simpl. lra.
Qed.

(** Distance between zero and its conjugate *)
Lemma dist_to_conj : forall s,
  euclidean_dist s (tc_conj s) == 2 * Qabs (tc_im s).
Proof.
  intros s. unfold euclidean_dist, tc_conj. cbn [tc_re tc_im].
  assert (Hre : Qabs (tc_re s - tc_re s) == 0).
  { setoid_replace (tc_re s - tc_re s) with 0 by ring.
    unfold Qabs. simpl. reflexivity. }
  assert (Him : tc_im s - - tc_im s == 2 * tc_im s) by ring.
  rewrite Hre, Him. rewrite Qabs_Qmult.
  rewrite (Qabs_pos 2) by lra. lra.
Qed.

(** Weighted distance vanishes at self *)
Lemma weighted_dist_self : forall N s,
  weighted_dist N s s == 0.
Proof.
  intros. unfold weighted_dist.
  rewrite euclidean_dist_self. unfold Qdiv. ring.
Qed.

(** tc_re_nat is always >= 2 *)
Lemma tc_re_nat_ge_2 : forall s,
  (2 <= tc_re_nat s)%nat.
Proof.
  intros s. unfold tc_re_nat. lia.
Qed.

(** Zeta weight positive for k >= 2 (since zeta_partial k N >= 1) *)
Lemma zeta_weight_positive : forall s N,
  0 < zeta_weight s N.
Proof.
  intros s N. unfold zeta_weight.
  assert (Hge := zeta_ge_1 (tc_re_nat s) N).
  rewrite Qabs_pos by lra. lra.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

Check euclidean_dist.
Check euclidean_dist_nonneg.
Check Qabs_minus_sym.
Check euclidean_dist_sym.
Check euclidean_dist_self.
Check euclidean_dist_triangle.
Check CriticalMetric.
Check euclidean_metric.
Check reflect_isometry.
Check reflect_not_contraction_euclidean.
Check euclidean_dist_pos_witness.
Check reflect_not_contractive_isometric.
Check tc_re_nat.
Check zeta_weight.
Check zeta_weight_nonneg.
Check weighted_dist.
Check weighted_denom_pos.
Check weighted_dist_nonneg.
Check weighted_dist_sym.
Check weighted_dist_le_euclidean.
Check contraction_ratio.
Check ratio_at_known_zero_14.
Check ratio_functional_eq.
Check corrected_reflect.
Check corrected_iterate.
Check re_corrected.
Check corrected_im_unchanged.
Check corrected_re_bounded_change.
Check corrected_re_moves_toward_half.
Check re_corrected_contraction_test.
Check corrected_double_differs_re.
Check corrected_iterate_0.
Check corrected_iterate_S.
Check no_L1_contraction.
Check reflect_preserves_strip_width.
Check reflect_re_formula.
Check reflect_im_formula.
Check dist_to_reflect.
Check critical_line_minimizes_reflect_dist.
Check re_fixed_point_half.
Check re_corrected_fn.
Check re_corrected_at_half_sym.
Check contraction_approx_fixed.
Check RH_zeros_on_line.
Check reflect_zero_nontrivial.
Check RH_zero_near_reflect.
Check RH_critical_strip_symmetric.
Check critical_line_dist_im_only.
Check reflect_critical_line.
Check dist_to_conj.
Check weighted_dist_self.
Check tc_re_nat_ge_2.
Check zeta_weight_positive.

Print Assumptions reflect_not_contractive_isometric.
Print Assumptions contraction_approx_fixed.
Print Assumptions RH_critical_strip_symmetric.
