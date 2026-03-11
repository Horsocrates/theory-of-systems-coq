(* ========================================================================= *)
(*        EXTENDED INTERVAL — All Orbits Converge for β > 0                *)
(*                                                                          *)
(*  All orbits of f(β)=4β/(1+β) converge for ANY β > 0:                  *)
(*    - β < 3: orbit is increasing, bounded by 4 → Cauchy (MCT)           *)
(*    - β = 3: orbit is constant at fixed point                            *)
(*    - β > 3: orbit is decreasing, bounded below by 3 → Cauchy (MCT)    *)
(*  Mass gap positive at every iterate: all in (0,8).                      *)
(*                                                                          *)
(*  STATUS: ~30 Qed, 0 Admitted                                            *)
(*  AXIOMS: classic (via MonotoneConvergence)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs List Lia ZArith.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import FixedPoint.
From ToS Require Import MonotoneConvergence.
From ToS Require Import gauge.RGFlow.
From ToS Require Import gauge.SU2TransferMatrix.
From ToS Require Import RealField.
From ToS Require Import gauge.NonlinearRG.

(* ========================================================================= *)
(*  PART I: Push up / push down                                              *)
(* ========================================================================= *)

(** f pushes β up when β < 3 *)
Lemma rg_pushes_up : forall beta,
  0 < beta -> beta < 3 -> beta < rg_map_quadratic beta.
Proof.
  intros beta Hpos Hlt3.
  assert (Hdiff := rg_quad_minus_beta beta Hpos).
  (* Hdiff : f(β) - β == β*(3-β)*/(1+β) *)
  assert (Hnum : 0 < beta * (3 - beta)) by nra.
  assert (Hdenom : 0 < 1 + beta) by lra.
  assert (Hinv : 0 < / (1 + beta)) by (apply Qinv_lt_0_compat; exact Hdenom).
  assert (Hprod : 0 < beta * (3 - beta) * / (1 + beta)).
  { apply Qmult_lt_0_compat; [exact Hnum | exact Hinv]. }
  lra.
Qed.

(** f pushes β up or fixes it when β ≤ 3 *)
Lemma rg_pushes_up_le : forall beta,
  0 < beta -> beta <= 3 -> beta <= rg_map_quadratic beta.
Proof.
  intros beta Hpos Hle3.
  destruct (Qlt_le_dec beta 3) as [Hlt|Hge].
  - apply Qlt_le_weak. apply rg_pushes_up; assumption.
  - assert (Hbeq : beta == 3) by lra.
    assert (Hf : rg_map_quadratic beta == rg_map_quadratic 3).
    { unfold rg_map_quadratic. setoid_rewrite Hbeq. reflexivity. }
    assert (Hf3 := rg_quadratic_at_3). lra.
Qed.

(** f pushes β down when β > 3 *)
Lemma rg_pushes_down : forall beta,
  3 < beta -> rg_map_quadratic beta < beta.
Proof.
  intros beta Hgt3.
  assert (Hpos : 0 < beta) by lra.
  assert (Hdiff := rg_quad_minus_beta beta Hpos).
  assert (Hnum : beta * (3 - beta) < 0) by nra.
  assert (Hdenom : 0 < 1 + beta) by lra.
  assert (Hinv : 0 < / (1 + beta)) by (apply Qinv_lt_0_compat; exact Hdenom).
  (* neg * pos < 0: use Qle_div_r style or direct *)
  assert (Hprod : beta * (3 - beta) * / (1 + beta) < 0).
  { (* beta*(3-beta) < 0, /(1+beta) > 0, so product < 0 *)
    (* -(beta*(3-beta)) > 0, so -(beta*(3-beta))*/(1+beta) > 0 *)
    assert (Hneg : 0 < -(beta * (3 - beta))) by lra.
    assert (Hpos2 : 0 < -(beta * (3 - beta)) * /(1+beta)).
    { apply Qmult_lt_0_compat; [exact Hneg | exact Hinv]. }
    assert (Hring : -(beta * (3 - beta)) * /(1+beta) ==
                     -(beta * (3 - beta) * /(1+beta))) by ring.
    lra. }
  lra.
Qed.

(** f pushes β down or fixes it when β ≥ 3 *)
Lemma rg_pushes_down_le : forall beta,
  0 < beta -> 3 <= beta -> rg_map_quadratic beta <= beta.
Proof.
  intros beta Hpos Hge3.
  destruct (Qlt_le_dec 3 beta) as [Hgt|Hle].
  - apply Qlt_le_weak. apply rg_pushes_down; assumption.
  - assert (Hbeq : beta == 3) by lra.
    assert (Hf : rg_map_quadratic beta == rg_map_quadratic 3).
    { unfold rg_map_quadratic. setoid_rewrite Hbeq. reflexivity. }
    assert (Hf3 := rg_quadratic_at_3). lra.
Qed.

(** When β < 3, f(β) stays below 3 *)
Lemma rg_below_3_stays : forall beta,
  0 < beta -> beta < 3 -> rg_map_quadratic beta < 3.
Proof.
  intros beta Hpos Hlt3.
  (* f(β) < 3 ← f(β) < f(3) = 3, using f increasing and β < 3 *)
  (* But we don't have strict increasing with ≤ hypothesis. Use direct: *)
  (* f(β) - β = β(3-β)/(1+β) > 0, and we need f(β) < 3. *)
  (* f(β) = β + β(3-β)/(1+β). Want β + β(3-β)/(1+β) < 3. *)
  (* ↔ β(3-β)/(1+β) < 3-β ↔ β/(1+β) < 1 ↔ β < 1+β ✓ *)
  assert (Hdiff := rg_quad_minus_beta beta Hpos).
  (* Hdiff : f(β) - β == β*(3-β)*/(1+β) *)
  assert (Hdenom : 0 < 1 + beta) by lra.
  assert (Hinv : 0 < / (1 + beta)) by (apply Qinv_lt_0_compat; exact Hdenom).
  (* Need: f(β) < 3, i.e., f(β) - β < 3 - β *)
  (* f(β) - β == β*(3-β)*/(1+β) < 3 - β *)
  (* ↔ β*/(1+β) < 1 (divide both sides by (3-β) > 0) *)
  (* ↔ β < 1+β ✓ *)
  assert (H3mb : 0 < 3 - beta) by lra.
  assert (Htarget : beta * (3 - beta) * / (1 + beta) < 3 - beta).
  { assert (Hlt : beta * (3 - beta) < (3 - beta) * (1 + beta)) by nra.
    assert (Hgoal : beta * (3 - beta) * / (1 + beta) <
                    (3 - beta) * (1 + beta) * / (1 + beta)).
    { apply Qmult_lt_compat_r; [exact Hinv | exact Hlt]. }
    assert (Heq : (3 - beta) * (1 + beta) * / (1 + beta) == 3 - beta).
    { field. intro Habs. lra. }
    lra. }
  lra.
Qed.

(** When β > 3, f(β) stays above 3 *)
Lemma rg_above_3_stays : forall beta,
  3 < beta -> 3 < rg_map_quadratic beta.
Proof.
  intros beta Hgt3.
  assert (Hpos : 0 < beta) by lra.
  (* f is increasing and f(3) = 3, so f(β) > f(3) = 3 for β > 3 *)
  assert (H3pos : 0 < (3 : Q)) by lra.
  assert (Hle : (3 : Q) <= beta) by lra.
  assert (Hinc := rg_quad_increasing 3 beta H3pos Hpos Hle).
  assert (Hf3 := rg_quadratic_at_3).
  (* Hinc : f(3) ≤ f(β), Hf3 : f(3) == 3 *)
  (* Need: 3 < f(β), i.e., 3 ≤ f(β) and 3 ≠ f(β) ... *)
  (* Actually rg_quad_increasing gives ≤ but we need strict. *)
  (* Use strictly_increasing instead or use pushes_down complement *)
  (* f(β) = β would mean β is fixed point = 3, contradicting β > 3. *)
  (* So f(β) ≠ β. Also β > f(β) by rg_pushes_down. So f(β) < β. *)
  (* But we need f(β) > 3. From rg_pushes_down: f(β) < β. *)
  (* And f(3) = 3. Since f is increasing, f(3) ≤ f(β). So 3 ≤ f(β). *)
  (* Need strict: if f(β) = 3 then f(β) = f(3), but f strictly increasing *)
  (* means β = 3, contradiction. *)
  (* Actually, let's just use: f(β) - β == β(3-β)/(1+β) < 0, so f(β) < β. *)
  (* And f(β) > 0 (rg_quad_pos). We need f(β) > 3. *)
  (* f(β) - 3 == f(β) - f(3) == 4(β-3)/((1+β)(1+3)) > 0 since β > 3 *)
  assert (Hdiff := rg_quad_diff 3 beta H3pos Hpos).
  (* Hdiff : f(3) - f(β) == 4*(3-β)*... hmm the order matters *)
  (* rg_quad_diff : f(x)-f(y) == 4(x-y)*/(...)  *)
  assert (Hdiff2 := rg_quad_diff beta 3 Hpos H3pos).
  (* Hdiff2 : f(β) - f(3) == 4*(β-3)*/ ((1+β)*(1+3)) *)
  assert (Hbm3 : 0 < beta - 3) by lra.
  assert (Hd1 : 0 < (1 + beta) * (1 + 3)) by nra.
  assert (Hd1_inv : 0 < / ((1 + beta) * (1 + 3))) by (apply Qinv_lt_0_compat; exact Hd1).
  assert (Hprod : 0 < 4 * (beta - 3) * / ((1 + beta) * (1 + 3))).
  { apply Qmult_lt_0_compat; [nra | exact Hd1_inv]. }
  lra.
Qed.

(* ========================================================================= *)
(*  PART II: Orbit monotonicity                                              *)
(* ========================================================================= *)

(** Orbit stays below 3 *)
Lemma orbit_below_3 : forall beta n,
  0 < beta -> beta < 3 ->
  0 < iterate rg_map_quadratic beta n /\
  iterate rg_map_quadratic beta n < 3.
Proof.
  intros beta n Hpos Hlt3.
  induction n as [|n' IH].
  - simpl. split; assumption.
  - destruct IH as [IHpos IHlt3].
    simpl. split.
    + apply rg_quad_pos. exact IHpos.
    + apply rg_below_3_stays; assumption.
Qed.

(** Orbit stays above 3 *)
Lemma orbit_above_3 : forall beta n,
  3 < beta ->
  3 < iterate rg_map_quadratic beta n.
Proof.
  intros beta n Hgt3.
  induction n as [|n' IH].
  - simpl. exact Hgt3.
  - simpl. apply rg_above_3_stays. exact IH.
Qed.

(** Orbit is increasing when β < 3 *)
Lemma orbit_inc_below : forall beta n,
  0 < beta -> beta < 3 ->
  iterate rg_map_quadratic beta n <= iterate rg_map_quadratic beta (S n).
Proof.
  intros beta n Hpos Hlt3.
  simpl.
  assert (Horb := orbit_below_3 beta n Hpos Hlt3).
  destruct Horb as [Horb_pos Horb_lt3].
  apply rg_pushes_up_le; [exact Horb_pos | lra].
Qed.

(** Orbit is decreasing when β > 3 *)
Lemma orbit_dec_above : forall beta n,
  3 < beta ->
  iterate rg_map_quadratic beta (S n) <= iterate rg_map_quadratic beta n.
Proof.
  intros beta n Hgt3.
  simpl.
  assert (Horb := orbit_above_3 beta n Hgt3).
  assert (Hpos : 0 < iterate rg_map_quadratic beta n) by lra.
  assert (Hge : 3 <= iterate rg_map_quadratic beta n) by lra.
  apply rg_pushes_down_le; assumption.
Qed.

(** All iterates are positive *)
Lemma orbit_pos : forall beta n,
  0 < beta -> 0 < iterate rg_map_quadratic beta n.
Proof.
  intros beta n Hpos.
  induction n as [|n' IH].
  - simpl. exact Hpos.
  - simpl. apply rg_quad_pos. exact IH.
Qed.

(** All iterates from n≥1 are below 4 *)
Lemma orbit_lt_4_from_1 : forall beta n,
  0 < beta -> (1 <= n)%nat -> iterate rg_map_quadratic beta n < 4.
Proof.
  intros beta n Hpos Hn.
  destruct n as [|n']; [lia |].
  simpl. apply rg_quad_lt_4. apply orbit_pos. exact Hpos.
Qed.

(** f(β) < 4 for all β > 0 *)
Lemma orbit_step_lt_4 : forall beta,
  0 < beta -> rg_map_quadratic beta < 4.
Proof.
  exact rg_quad_lt_4.
Qed.

(** All iterates from n≥1 are in (0, 4) *)
Lemma orbit_in_bounds : forall beta n,
  0 < beta -> (1 <= n)%nat ->
  0 < iterate rg_map_quadratic beta n /\
  iterate rg_map_quadratic beta n < 4.
Proof.
  intros beta n Hpos Hn.
  split; [apply orbit_pos; exact Hpos | apply orbit_lt_4_from_1; assumption].
Qed.

(* ========================================================================= *)
(*  PART III: Orbit convergence via MCT                                      *)
(* ========================================================================= *)

(** Orbit Cauchy when β < 3: increasing and bounded *)
Lemma orbit_cauchy_below : forall beta,
  0 < beta -> beta < 3 ->
  is_cauchy (iterate rg_map_quadratic beta).
Proof.
  intros beta Hpos Hlt3.
  apply q_inc_bounded_cauchy with 4.
  - intros n. apply orbit_inc_below; assumption.
  - intros n. destruct n as [|n'].
    + simpl. lra.
    + apply Qlt_le_weak. apply orbit_lt_4_from_1; [exact Hpos | lia].
Qed.

(** Orbit Cauchy when β > 3: decreasing and bounded below *)
Lemma orbit_cauchy_above : forall beta,
  3 < beta ->
  is_cauchy (iterate rg_map_quadratic beta).
Proof.
  intros beta Hgt3.
  apply q_dec_bounded_cauchy with 3.
  - intros n. apply orbit_dec_above. exact Hgt3.
  - intros n. apply Qlt_le_weak. apply orbit_above_3. exact Hgt3.
Qed.

(** Orbit Cauchy at β = 3: constant sequence *)
Lemma orbit_cauchy_at_3 :
  is_cauchy (iterate rg_map_quadratic 3).
Proof.
  unfold is_cauchy. intros eps Heps.
  exists 0%nat. intros m n Hm Hn.
  assert (Hm3 := iterate_at_fp m).
  assert (Hn3 := iterate_at_fp n).
  assert (Hdiff : iterate rg_map_quadratic 3 m - iterate rg_map_quadratic 3 n == 0)
    by lra.
  rewrite (Qabs_wd _ _ Hdiff).
  rewrite Qabs_pos; lra.
Qed.

(** ★ KEY: All orbits converge for ANY β > 0 ★ *)
Theorem orbit_cauchy_all : forall beta,
  0 < beta ->
  is_cauchy (iterate rg_map_quadratic beta).
Proof.
  intros beta Hpos.
  destruct (Qlt_le_dec beta 3) as [Hlt|Hge].
  - (* β < 3: increasing orbit *)
    apply orbit_cauchy_below; assumption.
  - destruct (Qlt_le_dec 3 beta) as [Hgt|Hle].
    + (* β > 3: decreasing orbit *)
      apply orbit_cauchy_above; exact Hgt.
    + (* β = 3: constant orbit *)
      assert (Hbeq : beta == 3) by lra.
      unfold is_cauchy. intros eps Heps.
      exists 0%nat. intros m n Hm Hn.
      (* Prove iterate_qeq: if x == y then iterate f x k == iterate f y k *)
      assert (iterate_qeq : forall k,
        iterate rg_map_quadratic beta k == iterate rg_map_quadratic 3 k).
      { induction k as [|k' IHk].
        - simpl. exact Hbeq.
        - simpl. unfold rg_map_quadratic. unfold Qdiv.
          apply Qmult_comp.
          + apply Qmult_comp; [reflexivity | exact IHk].
          + apply Qinv_comp. apply Qplus_comp; [reflexivity | exact IHk]. }
      assert (Hm3 := iterate_at_fp m).
      assert (Hn3 := iterate_at_fp n).
      assert (Hbeta_m := iterate_qeq m).
      assert (Hbeta_n := iterate_qeq n).
      assert (Hdiff : iterate rg_map_quadratic beta m -
                      iterate rg_map_quadratic beta n == 0) by lra.
      rewrite (Qabs_wd _ _ Hdiff). rewrite Qabs_pos; lra.
Qed.

(** All iterates from n≥1 stay in gap range (0, 8) *)
Lemma orbit_in_gap_range : forall beta n,
  0 < beta -> (1 <= n)%nat ->
  0 < iterate rg_map_quadratic beta n /\
  iterate rg_map_quadratic beta n < 8.
Proof.
  intros beta n Hpos Hn.
  split.
  - apply orbit_pos. exact Hpos.
  - assert (H4 := orbit_lt_4_from_1 beta n Hpos Hn). lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Gap along orbits                                                *)
(* ========================================================================= *)

(** ★ Gap positive at every iterate from n≥1 ★ *)
Theorem orbit_gap_positive : forall beta n,
  0 < beta -> (1 <= n)%nat ->
  0 < su2_mass_gap (iterate rg_map_quadratic beta n).
Proof.
  intros beta n Hpos Hn.
  assert (Hrange := orbit_in_gap_range beta n Hpos Hn).
  destruct Hrange as [Horb_pos Horb_lt8].
  apply su2_mass_gap_positive; assumption.
Qed.

(** Gap positive at iterate 0 when β < 8 *)
Lemma orbit_gap_positive_0 : forall beta,
  0 < beta -> beta < 8 ->
  0 < su2_mass_gap (iterate rg_map_quadratic beta 0).
Proof.
  intros beta Hpos Hlt8. simpl. apply su2_mass_gap_positive; assumption.
Qed.

(** RG prevents deconfinement: f(β) < 8 *)
Lemma rg_prevents_deconfinement : forall beta,
  0 < beta -> rg_map_quadratic beta < 8.
Proof.
  intros beta Hpos.
  assert (H := rg_quad_lt_4 beta Hpos). lra.
Qed.

(** Confinement for all iterates from n≥1 *)
Theorem confinement_via_rg : forall beta n,
  0 < beta -> (1 <= n)%nat ->
  iterate rg_map_quadratic beta n < 8.
Proof.
  intros beta n Hpos Hn.
  assert (H := orbit_lt_4_from_1 beta n Hpos Hn). lra.
Qed.

(** Double iterate: f²(β) = 16β/(1+5β) *)
Lemma double_iterate : forall beta,
  0 < beta ->
  rg_map_quadratic (rg_map_quadratic beta) == 16 * beta / (1 + 5 * beta).
Proof.
  intros beta Hpos.
  unfold rg_map_quadratic at 1 2.
  unfold Qdiv. field.
  split.
  - (* 1 + 5*beta ≠ 0 *)
    intro Habs. lra.
  - (* 1 + 4*beta*/(1+beta) ≠ 0 *)
    intro Habs.
    assert (Hdenom : 0 < 1 + beta) by lra.
    assert (Hinv : 0 < /(1+beta)) by (apply Qinv_lt_0_compat; exact Hdenom).
    assert (H4b : 0 < 4 * beta * /(1+beta)) by nra.
    lra.
Qed.

(* ========================================================================= *)
(*  PART V: Summary                                                          *)
(* ========================================================================= *)

(** Mass gap positive for all β ∈ (0,8) — direct from SU2TransferMatrix *)
Lemma mass_gap_all_beta : forall beta,
  0 < beta -> beta < 8 -> 0 < su2_mass_gap beta.
Proof.
  exact su2_mass_gap_positive.
Qed.

(** Extended interval main theorem *)
Theorem extended_main :
  (* All orbits converge *)
  (forall beta, 0 < beta ->
    is_cauchy (iterate rg_map_quadratic beta)) /\
  (* Gap positive at every iterate from n≥1 *)
  (forall beta n, 0 < beta -> (1 <= n)%nat ->
    0 < su2_mass_gap (iterate rg_map_quadratic beta n)) /\
  (* No deconfinement from n≥1 *)
  (forall beta n, 0 < beta -> (1 <= n)%nat ->
    iterate rg_map_quadratic beta n < 8).
Proof.
  split; [exact orbit_cauchy_all |].
  split; [exact orbit_gap_positive |].
  exact confinement_via_rg.
Qed.

(** What Step 9 proves *)
Theorem what_step9_proves :
  (* Orbits below 3 are increasing *)
  (forall beta n, 0 < beta -> beta < 3 ->
    iterate rg_map_quadratic beta n <=
    iterate rg_map_quadratic beta (S n)) /\
  (* Orbits above 3 are decreasing *)
  (forall beta n, 3 < beta ->
    iterate rg_map_quadratic beta (S n) <=
    iterate rg_map_quadratic beta n) /\
  (* All orbits converge *)
  (forall beta, 0 < beta ->
    is_cauchy (iterate rg_map_quadratic beta)) /\
  (* Gap positive at every iterate from n≥1 *)
  (forall beta n, 0 < beta -> (1 <= n)%nat ->
    0 < su2_mass_gap (iterate rg_map_quadratic beta n)).
Proof.
  split; [exact orbit_inc_below |].
  split; [exact orbit_dec_above |].
  split; [exact orbit_cauchy_all |].
  exact orbit_gap_positive.
Qed.

(** End marker *)
Theorem total_count : True.
Proof. exact I. Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(*  ~27 Qed, 0 Admitted                                                     *)
(*                                                                           *)
(*  Part I: rg_pushes_up, rg_pushes_up_le, rg_pushes_down,                *)
(*          rg_pushes_down_le, rg_below_3_stays, rg_above_3_stays (6)     *)
(*  Part II: orbit_below_3, orbit_above_3, orbit_inc_below,               *)
(*           orbit_dec_above, orbit_pos, orbit_lt_4 (6)                    *)
(*  Part III: orbit_cauchy_below, orbit_cauchy_above,                       *)
(*            orbit_cauchy_at_3, orbit_cauchy_all, orbit_in_gap_range (5)  *)
(*  Part IV: orbit_gap_positive, rg_prevents_deconfinement,                *)
(*           confinement_via_rg, double_iterate (4)                        *)
(*  Part V: mass_gap_all_beta, extended_main, what_step9_proves,           *)
(*          total_count (4)                                                *)
(* ========================================================================= *)
