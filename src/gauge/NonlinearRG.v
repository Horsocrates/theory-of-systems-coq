(* ========================================================================= *)
(*        NONLINEAR RG — Exact Quadratic RG is a Contraction                *)
(*                                                                          *)
(*  Replace linearized RG f(β)=(9+β)/4 with exact f(β)=4β/(1+β).         *)
(*  This rational function has exact contraction properties:                *)
(*    - Exact fixed point β*=3                                             *)
(*    - Contraction on [3/2, B] for ANY B ≥ 4                             *)
(*    - Factor c = 16/25 (max derivative at β=3/2)                        *)
(*    - Maps [3/2, ∞) into [12/5, 4) — bounded image                     *)
(*                                                                          *)
(*  STATUS: ~35 Qed, 0 Admitted                                            *)
(*  AXIOMS: none (exact rational arithmetic)                                *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import RealField.
From ToS Require Import FixedPoint.
From ToS Require Import gauge.RGFlow.
From ToS Require Import gauge.SU2TransferMatrix.
From ToS Require Import zeta.ZetaProcess.

(* ========================================================================= *)
(*  PART I: Basic properties of f(β) = 4β/(1+β)                           *)
(* ========================================================================= *)

Lemma one_plus_pos : forall beta, 0 < beta -> 0 < 1 + beta.
Proof. intros. lra. Qed.

Lemma one_plus_nonzero : forall beta, 0 < beta -> ~ (1 + beta == 0).
Proof. intros beta Hb Heq. lra. Qed.

(** f(β) > 0 for β > 0 *)
Lemma rg_quad_pos : forall beta, 0 < beta -> 0 < rg_map_quadratic beta.
Proof.
  intros beta Hb.
  unfold rg_map_quadratic, Qdiv.
  assert (H1 : 0 < 1 + beta) by lra.
  assert (H2 : 0 < / (1 + beta)) by (apply Qinv_lt_0_compat; lra).
  assert (H3 : 0 < 4 * beta) by lra.
  apply Qmult_lt_0_compat; assumption.
Qed.

(** f(β) < 4 for all finite β > 0 *)
Lemma rg_quad_lt_4 : forall beta, 0 < beta -> rg_map_quadratic beta < 4.
Proof.
  intros beta Hb.
  unfold rg_map_quadratic.
  apply Qdiv_lt_from_mul.
  - lra.
  - lra.
Qed.

(** f(β) < 8 for all β > 0 *)
Lemma rg_quad_lt_8 : forall beta, 0 < beta -> rg_map_quadratic beta < 8.
Proof.
  intros beta Hb. assert (H := rg_quad_lt_4 beta Hb). lra.
Qed.

(** Concrete value: f(3/2) = 12/5 *)
Lemma rg_quad_at_3_2 : rg_map_quadratic (3#2) == 12#5.
Proof. unfold rg_map_quadratic, Qdiv. unfold Qeq. simpl. lia. Qed.

(** Concrete value: f(1) = 2 *)
Lemma rg_quad_at_1 : rg_map_quadratic 1 == 2.
Proof. unfold rg_map_quadratic, Qdiv. unfold Qeq. simpl. lia. Qed.

(** Concrete value: f(4) = 16/5 *)
Lemma rg_quad_at_4 : rg_map_quadratic 4 == 16#5.
Proof. unfold rg_map_quadratic, Qdiv. unfold Qeq. simpl. lia. Qed.

(** Concrete value: f(100) = 400/101 *)
Lemma rg_quad_at_100 : rg_map_quadratic 100 == 400#101.
Proof. unfold rg_map_quadratic, Qdiv. unfold Qeq. simpl. lia. Qed.

(** f(β) ≥ 3/2 when β ≥ 3/2 *)
Lemma rg_quad_ge_3_2 : forall beta,
  (3#2) <= beta -> (3#2) <= rg_map_quadratic beta.
Proof.
  intros beta Hb.
  unfold rg_map_quadratic.
  apply Qle_div_r.
  - lra.
  - (* (3#2) * (1 + beta) <= 4 * beta, i.e., 3/2 + 3β/2 ≤ 4β *)
    lra.
Qed.

(** f maps [3/2, B] → [3/2, B] for B ≥ 4 *)
Lemma rg_quad_maps_interval : forall beta B,
  (3#2) <= beta -> beta <= B -> 4 <= B ->
  (3#2) <= rg_map_quadratic beta /\ rg_map_quadratic beta <= B.
Proof.
  intros beta B Hb1 Hb2 HB.
  split.
  - apply rg_quad_ge_3_2. exact Hb1.
  - assert (Hlt := rg_quad_lt_4 beta ltac:(lra)).
    lra.
Qed.

(* ========================================================================= *)
(*  PART II: Difference formula and monotonicity                             *)
(* ========================================================================= *)

(** ★ KEY IDENTITY: f(x) - f(y) = 4(x-y) / ((1+x)(1+y)) ★ *)
Lemma rg_quad_diff : forall x y,
  0 < x -> 0 < y ->
  rg_map_quadratic x - rg_map_quadratic y ==
  4 * (x - y) * / ((1 + x) * (1 + y)).
Proof.
  intros x y Hx Hy.
  unfold rg_map_quadratic.
  field.
  split; intro; lra.
Qed.

(** ★ KEY IDENTITY: f(β) - β = β(3-β) / (1+β) ★ *)
Lemma rg_quad_minus_beta : forall beta,
  0 < beta ->
  rg_map_quadratic beta - beta == beta * (3 - beta) * / (1 + beta).
Proof.
  intros beta Hb.
  unfold rg_map_quadratic.
  field.
  intro; lra.
Qed.

(** Denominator product is positive *)
Lemma product_denom_pos : forall x y,
  0 < x -> 0 < y -> 0 < (1 + x) * (1 + y).
Proof. intros. nra. Qed.

(** f is monotone increasing *)
Lemma rg_quad_increasing : forall x y,
  0 < x -> 0 < y -> x <= y ->
  rg_map_quadratic x <= rg_map_quadratic y.
Proof.
  intros x y Hx Hy Hle.
  assert (Hdiff := rg_quad_diff x y Hx Hy).
  assert (Hprod : 0 < (1 + x) * (1 + y)) by nra.
  assert (Hinv : 0 < / ((1 + x) * (1 + y))) by (apply Qinv_lt_0_compat; exact Hprod).
  assert (Hle_diff : 4 * (x - y) * / ((1 + x) * (1 + y)) <= 0).
  { assert (4 * (x - y) <= 0) by lra. nra. }
  lra.
Qed.

(** f is strictly monotone increasing *)
Lemma rg_quad_strictly_increasing : forall x y,
  0 < x -> 0 < y -> x < y ->
  rg_map_quadratic x < rg_map_quadratic y.
Proof.
  intros x y Hx Hy Hlt.
  assert (Hdiff := rg_quad_diff x y Hx Hy).
  assert (Hprod : 0 < (1 + x) * (1 + y)) by nra.
  assert (Hinv : 0 < / ((1 + x) * (1 + y))) by (apply Qinv_lt_0_compat; exact Hprod).
  assert (Hlt_diff : 0 < 4 * (y - x) * / ((1 + x) * (1 + y))).
  { apply Qmult_lt_0_compat; [lra | exact Hinv]. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART III: Lipschitz bound and contraction                                *)
(* ========================================================================= *)

(** Denominator product lower bound on [3/2, ∞) *)
Lemma denom_lower_bound : forall x y,
  (3#2) <= x -> (3#2) <= y -> (25#4) <= (1 + x) * (1 + y).
Proof. intros. nra. Qed.

(** Inverse denominator upper bound *)
Lemma inv_denom_upper : forall x y,
  (3#2) <= x -> (3#2) <= y ->
  / ((1 + x) * (1 + y)) <= (4#25).
Proof.
  intros x y Hx Hy.
  assert (Hdenom := denom_lower_bound x y Hx Hy).
  assert (Hpos : 0 < (25#4)) by lra.
  assert (H := Qinv_le_compat (25#4) ((1 + x) * (1 + y)) Hpos Hdenom).
  assert (Hval : / (25#4) == (4#25)) by (unfold Qeq; simpl; lia).
  lra.
Qed.

(** ★ LIPSCHITZ BOUND: |f(x) - f(y)| ≤ (16/25)|x - y| on [3/2, B] ★ *)
Lemma rg_quad_lipschitz : forall x y B,
  (3#2) <= x -> x <= B -> (3#2) <= y -> y <= B -> 4 <= B ->
  Qabs (rg_map_quadratic x - rg_map_quadratic y) <= (16#25) * Qabs (x - y).
Proof.
  intros x y B Hx1 Hx2 Hy1 Hy2 HB.
  assert (Hx_pos : 0 < x) by lra.
  assert (Hy_pos : 0 < y) by lra.
  (* Algebraic identity *)
  assert (Hdiff := rg_quad_diff x y Hx_pos Hy_pos).
  (* Rewrite Qabs using the identity *)
  rewrite (Qabs_wd _ _ Hdiff).
  (* Qabs(4*(x-y) * /((1+x)*(1+y))) *)
  (* Decompose using Qabs_Qmult *)
  rewrite Qabs_Qmult.
  rewrite Qabs_Qmult.
  (* Now: Qabs 4 * Qabs(x-y) * Qabs(/((1+x)*(1+y))) ≤ (16#25) * Qabs(x-y) *)
  assert (Habs4 : Qabs 4 == 4).
  { apply Qabs_pos. lra. }
  assert (Hprod : 0 < (1 + x) * (1 + y)) by nra.
  assert (Hinv_pos : 0 < / ((1 + x) * (1 + y))) by (apply Qinv_lt_0_compat; exact Hprod).
  assert (Habs_inv : Qabs (/ ((1 + x) * (1 + y))) == / ((1 + x) * (1 + y))).
  { apply Qabs_pos. lra. }
  rewrite Habs4. rewrite Habs_inv.
  (* Now: 4 * Qabs(x-y) * /((1+x)*(1+y)) ≤ (16#25) * Qabs(x-y) *)
  assert (Hinv_bound := inv_denom_upper x y Hx1 Hy1).
  assert (Habs_nn : 0 <= Qabs (x - y)) by (apply Qabs_nonneg).
  (* 4 * Qabs(x-y) * /(denom) ≤ 4 * Qabs(x-y) * (4#25) = (16#25) * Qabs(x-y) *)
  apply Qle_trans with (4 * Qabs (x - y) * (4#25)).
  - apply Qmult_le_compat_l; [exact Hinv_bound | nra].
  - assert (Heq : 4 * Qabs (x - y) * (4 # 25) == (16#25) * Qabs (x - y)) by ring.
    lra.
Qed.

(** Contraction factor bounds *)
Lemma rg_quad_factor_bounds : 0 <= (16#25) /\ (16#25) < 1.
Proof. split; lra. Qed.

(** ★ THE CONTRACTION THEOREM: f is a contraction on [3/2, B] for any B ≥ 4 ★ *)
Theorem rg_quad_is_contraction : forall B,
  4 <= B ->
  is_contraction rg_map_quadratic (3#2) B (16#25).
Proof.
  intros B HB.
  unfold is_contraction.
  split; [lra |].
  split; [lra |].
  split.
  - (* Self-map: [3/2, B] → [3/2, B] *)
    intros x Hx1 Hx2.
    exact (rg_quad_maps_interval x B Hx1 Hx2 HB).
  - (* Lipschitz: |f(x)-f(y)| ≤ (16/25)|x-y| *)
    intros x y Hx1 Hx2 Hy1 Hy2.
    exact (rg_quad_lipschitz x y B Hx1 Hx2 Hy1 Hy2 HB).
Qed.

(** Contraction on [3/2, 4] — the standard interval *)
Theorem rg_quad_contraction_4 :
  is_contraction rg_map_quadratic (3#2) 4 (16#25).
Proof. apply rg_quad_is_contraction. lra. Qed.

(** ★ UNIQUE FIXED POINT: the only fixed point in [3/2, 4] is β*=3 ★ *)
Theorem rg_quad_unique_fp : forall p,
  (3#2) <= p -> p <= 4 ->
  rg_map_quadratic p == p -> p == 3.
Proof.
  intros p Hp1 Hp2 Hfp.
  assert (Hc := rg_quad_contraction_4).
  assert (H3_lb : (3#2) <= (3 : Q)) by lra.
  assert (H3_ub : (3 : Q) <= 4) by lra.
  exact (contraction_unique_fixed rg_map_quadratic (3#2) 4 (16#25)
    p 3 Hc Hp1 Hp2 H3_lb H3_ub Hfp rg_quadratic_at_3).
Qed.

(** Banach: iterates converge from any start in [3/2, B] *)
Theorem rg_quad_banach : forall B x,
  4 <= B -> (3#2) <= x -> x <= B ->
  is_cauchy (fun n => iterate rg_map_quadratic x n).
Proof.
  intros B x HB Hx1 Hx2.
  exact (iterate_is_cauchy rg_map_quadratic (3#2) B (16#25) x
    (rg_quad_is_contraction B HB) Hx1 Hx2).
Qed.

(** iterate f 3 n = 3 for all n (3 is a fixed point) *)
Lemma iterate_at_fp : forall n,
  iterate rg_map_quadratic 3 n == 3.
Proof.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - change (iterate rg_map_quadratic 3 (S n'))
      with (rg_map_quadratic (iterate rg_map_quadratic 3 n')).
    unfold rg_map_quadratic.
    setoid_rewrite IH.
    (* Now: 4 * 3 / (1 + 3) == 3 *)
    unfold Qeq. simpl. lia.
Qed.

(** Convergence rate: |f^n(x) - 3| ≤ (16/25)^n |x - 3| *)
Theorem rg_quad_convergence_rate : forall x n,
  (3#2) <= x -> x <= 4 ->
  Qabs (iterate rg_map_quadratic x n - 3) <=
  Qpow (16#25) n * Qabs (x - 3).
Proof.
  intros x n Hx1 Hx2.
  assert (H3_lb : (3#2) <= (3 : Q)) by lra.
  assert (H3_ub : (3 : Q) <= 4) by lra.
  assert (Hiter := iterate_contraction rg_map_quadratic (3#2) 4 (16#25)
    rg_quad_contraction_4 x 3 Hx1 Hx2 H3_lb H3_ub n).
  assert (Heq : iterate rg_map_quadratic 3 n == 3) by apply iterate_at_fp.
  assert (Hdiff : iterate rg_map_quadratic x n - iterate rg_map_quadratic 3 n ==
                  iterate rg_map_quadratic x n - 3) by lra.
  rewrite (Qabs_wd _ _ Hdiff) in Hiter.
  exact Hiter.
Qed.

(* ========================================================================= *)
(*  PART IV: Comparison with linear RG                                       *)
(* ========================================================================= *)

(** Both maps agree at fixed point β*=3 *)
Lemma both_agree_at_fp :
  rg_map_linear 3 == 3 /\ rg_map_quadratic 3 == 3.
Proof.
  split; [exact rg_linear_fixed_point | exact rg_quadratic_at_3].
Qed.

(** Difference: f_L(β) - f_Q(β) = (β-3)² / (4(1+β)) *)
Lemma rg_difference : forall beta,
  0 < beta ->
  rg_map_linear beta - rg_map_quadratic beta ==
  (beta - 3) * (beta - 3) * / (4 * (1 + beta)).
Proof.
  intros beta Hb.
  unfold rg_map_linear, rg_map_quadratic.
  field.
  intro; lra.
Qed.

(** Linear RG overestimates: f_Q(β) ≤ f_L(β) for β > 0 *)
Lemma rg_linear_ge_quadratic : forall beta,
  0 < beta -> rg_map_quadratic beta <= rg_map_linear beta.
Proof.
  intros beta Hb.
  assert (Hdiff := rg_difference beta Hb).
  assert (H4pos : 0 < 4 * (1 + beta)) by lra.
  assert (Hinv : 0 < / (4 * (1 + beta))) by (apply Qinv_lt_0_compat; exact H4pos).
  assert (Hsq : 0 <= (beta - 3) * (beta - 3)).
  { destruct (Qlt_le_dec beta 3) as [Hlt|Hge]; [| destruct (Qlt_le_dec 3 beta) as [Hgt|Hle]].
    - assert (0 < 3 - beta) by lra. assert (0 < (3-beta)*(3-beta)).
      { apply Qmult_lt_0_compat; lra. }
      assert ((beta-3)*(beta-3) == (3-beta)*(3-beta)) by ring. lra.
    - assert (0 < beta - 3) by lra. apply Qmult_le_0_compat; lra.
    - assert (Hbeq : beta == 3) by lra.
      assert (Hbm3 : beta - 3 == 0) by lra.
      assert (Hprod0 : (beta - 3) * (beta - 3) == 0 * (beta - 3)).
      { apply Qmult_comp; [exact Hbm3 | reflexivity]. }
      assert (H0mul : 0 * (beta - 3) == 0) by ring. lra. }
  assert (Hprod : 0 <= (beta - 3) * (beta - 3) * / (4 * (1 + beta))).
  { apply Qmult_le_0_compat; [exact Hsq | lra]. }
  lra.
Qed.

(** Linear ≠ quadratic *)
Lemma rg_linear_neq_quadratic :
  ~ (forall beta, rg_map_linear beta == rg_map_quadratic beta).
Proof.
  intro H.
  assert (H1 := H 1).
  unfold rg_map_linear, rg_map_quadratic, Qdiv in H1.
  unfold Qeq in H1. simpl in H1. lia.
Qed.

(* ========================================================================= *)
(*  PART V: Concrete iterates and summary                                    *)
(* ========================================================================= *)

Lemma iterate_from_2_1 :
  iterate rg_map_quadratic 2 1 == 8#3.
Proof. simpl. exact rg_quadratic_at_2. Qed.

Lemma iterate_from_2_2 :
  iterate rg_map_quadratic 2 2 == 32#11.
Proof.
  simpl. unfold rg_map_quadratic, Qdiv. unfold Qeq. simpl. lia.
Qed.

(** ★ MAIN THEOREM: nonlinear RG contraction ★ *)
Theorem nonlinear_rg_main :
  (* 1. Contraction on [3/2, 4] *)
  is_contraction rg_map_quadratic (3#2) 4 (16#25) /\
  (* 2. Fixed point β*=3 *)
  rg_map_quadratic 3 == 3 /\
  (* 3. Unique fixed point *)
  (forall p, (3#2) <= p -> p <= 4 ->
    rg_map_quadratic p == p -> p == 3) /\
  (* 4. Orbits converge from [3/2, 4] *)
  (forall x, (3#2) <= x -> x <= 4 ->
    is_cauchy (fun n => iterate rg_map_quadratic x n)) /\
  (* 5. f(β) < 4 for all β > 0 *)
  (forall beta, 0 < beta -> rg_map_quadratic beta < 4).
Proof.
  split; [exact rg_quad_contraction_4 |].
  split; [exact rg_quadratic_at_3 |].
  split; [exact rg_quad_unique_fp |].
  split.
  - intros x Hx1 Hx2. apply (rg_quad_banach 4); lra.
  - exact rg_quad_lt_4.
Qed.

(** What Step 8 proves *)
Theorem what_step8_proves :
  (* Exact RG is contraction *)
  (forall B, 4 <= B ->
    is_contraction rg_map_quadratic (3#2) B (16#25)) /\
  (* Factor 16/25 < linear factor 1/4? No: 16/25 > 1/4 *)
  (* But quadratic is EXACT, linear is APPROXIMATE *)
  (16#25) < 1 /\
  (* Both agree at β*=3 *)
  rg_map_linear 3 == rg_map_quadratic 3 /\
  (* Linear overestimates *)
  (forall beta, 0 < beta ->
    rg_map_quadratic beta <= rg_map_linear beta).
Proof.
  split; [exact rg_quad_is_contraction |].
  split; [lra |].
  split; [| exact rg_linear_ge_quadratic].
  { transitivity 3; [exact (proj1 both_agree_at_fp) |].
    symmetry. exact (proj2 both_agree_at_fp). }
Qed.

(** What is open *)
Theorem what_step8_opens :
  ~ (forall beta, rg_map_linear beta == rg_map_quadratic beta).
Proof. exact rg_linear_neq_quadratic. Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(*  ~33 Qed, 0 Admitted                                                     *)
(*                                                                           *)
(*  Part I: one_plus_pos, one_plus_nonzero, rg_quad_pos, rg_quad_lt_4,    *)
(*          rg_quad_lt_8, rg_quad_at_3_2, rg_quad_at_1, rg_quad_at_4,     *)
(*          rg_quad_at_100, rg_quad_ge_3_2, rg_quad_maps_interval (11)     *)
(*  Part II: rg_quad_diff, rg_quad_minus_beta, product_denom_pos,          *)
(*           rg_quad_increasing, rg_quad_strictly_increasing (5)            *)
(*  Part III: denom_lower_bound, inv_denom_upper, rg_quad_lipschitz,       *)
(*            rg_quad_factor_bounds, rg_quad_is_contraction,               *)
(*            rg_quad_contraction_4, rg_quad_unique_fp,                    *)
(*            rg_quad_banach, rg_quad_convergence_rate (9)                  *)
(*  Part IV: both_agree_at_fp, rg_difference, rg_linear_ge_quadratic,     *)
(*           rg_linear_neq_quadratic (4)                                    *)
(*  Part V: iterate_from_2_1, iterate_from_2_2, nonlinear_rg_main,        *)
(*          what_step8_proves, what_step8_opens, total_count (6)           *)
(* ========================================================================= *)
