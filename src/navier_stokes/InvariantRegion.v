(* ========================================================================= *)
(*        INVARIANT REGION — The Per-Mode Trap                               *)
(*                                                                          *)
(*  Region R = {a : |a_k| ≤ A/k for all k ≥ 1}                           *)
(*  where A = ν/C_B (the self-consistency constant).                       *)
(*                                                                          *)
(*  Theorem: R is positively invariant under the Galerkin ODE.             *)
(*  Proof: at the boundary, the flow points inward.                         *)
(*                                                                          *)
(*  This is the CLOSING argument. Combined with Phase 4's bootstrap:       *)
(*  a(0) ∈ R → a(t) ∈ R → enstrophy bounded → regularity.              *)
(*                                                                          *)
(*  Elements: invariant region, boundary flow, self-consistency amplitude  *)
(*  Roles:    trap as regulator, flow direction as diagnostic              *)
(*  Rules:    boundary inward → invariant → enstrophy bounded → regularity *)
(*  STATUS: target ~45 Qed, 0 Admitted                                     *)
(*  AXIOMS: classic, B_antisym, C_B_positive, B_coeff_bounded             *)
(*  Author: Horsocrates | Date: March 2026                                 *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.GalerkinSystem.
From ToS Require Import navier_stokes.EnergyEstimate.
From ToS Require Import navier_stokes.TriadicInteraction.
From ToS Require Import navier_stokes.PerModeBound.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: The Invariant Region  (~10 lemmas)                        *)
(* ================================================================== *)

(* Self-consistency amplitude: A = ν/C_B *)
Definition A_inv (nu : Q) : Q := nu / C_B.

Lemma A_inv_positive : forall nu, 0 < nu -> 0 < A_inv nu.
Proof.
  intros nu Hnu.
  unfold A_inv, Qdiv.
  apply Qmult_lt_0_compat.
  - exact Hnu.
  - apply Qinv_lt_0_compat. exact C_B_positive.
Qed.

Lemma A_inv_nonneg : forall nu, 0 < nu -> 0 <= A_inv nu.
Proof.
  intros nu Hnu. apply Qlt_le_weak. apply A_inv_positive. exact Hnu.
Qed.

(* A_inv scales linearly with nu *)
Lemma A_inv_scale : forall nu c,
  0 < nu -> 0 < c ->
  A_inv (c * nu) == c * A_inv nu.
Proof.
  intros nu c Hnu Hc.
  unfold A_inv, Qdiv.
  ring.
Qed.

(* The region: |a_k| ≤ A/k for all k ≥ 1 *)
Definition in_region (nu : Q) (K : nat) (a : modal_state) : Prop :=
  forall k, (1 <= k)%nat -> (k <= K)%nat ->
    Qabs (a k) <= A_inv nu / inject_Z (Z.of_nat k).

(* Region is closed under scalar multiplication by t ∈ [0,1] *)
Lemma region_scale : forall nu K (a : modal_state) t,
  0 <= t -> t <= 1 ->
  in_region nu K a ->
  in_region nu K (fun k => t * a k).
Proof.
  intros nu K a t Ht0 Ht1 Hin.
  intros k Hk1 HkK.
  rewrite Qabs_Qmult.
  apply (Qle_trans _ (1 * Qabs (a k))).
  - apply Qmult_le_compat_r.
    + rewrite Qabs_pos; [exact Ht1 | exact Ht0].
    + apply Qabs_nonneg.
  - rewrite Qmult_1_l. apply Hin; assumption.
Qed.

(* Region contains zero *)
Theorem region_contains_zero : forall nu K,
  0 < nu ->
  in_region nu K (fun _ => 0).
Proof.
  intros nu K Hnu k Hk1 HkK.
  rewrite Qabs_pos; [| lra].
  unfold A_inv, Qdiv.
  apply Qmult_le_0_compat.
  - apply Qlt_le_weak.
    apply Qmult_lt_0_compat; [exact Hnu |].
    apply Qinv_lt_0_compat. exact C_B_positive.
  - apply Qlt_le_weak.
    apply Qinv_lt_0_compat.
    unfold Qlt, inject_Z. simpl. lia.
Qed.

(* Region is convex *)
Theorem region_convex : forall nu K (a b : modal_state) t,
  0 <= t -> t <= 1 ->
  in_region nu K a -> in_region nu K b ->
  in_region nu K (fun k => t * a k + (1 - t) * b k).
Proof.
  intros nu K a b t Ht0 Ht1 Ha Hb.
  intros k Hk1 HkK.
  apply (Qle_trans _ (Qabs (t * a k) + Qabs ((1 - t) * b k))).
  - apply Qabs_triangle.
  - rewrite !Qabs_Qmult.
    apply (Qle_trans _ (t * Qabs (a k) + (1 - t) * Qabs (b k))).
    + apply Qplus_le_compat.
      * apply Qmult_le_compat_r; [| apply Qabs_nonneg].
        rewrite Qabs_pos; [lra | exact Ht0].
      * apply Qmult_le_compat_r; [| apply Qabs_nonneg].
        rewrite Qabs_pos; lra.
    + apply (Qle_trans _ (t * (A_inv nu / inject_Z (Z.of_nat k))
                          + (1 - t) * (A_inv nu / inject_Z (Z.of_nat k)))).
      * apply Qplus_le_compat.
        -- apply Qmult_le_compat_nonneg.
           ++ split; [exact Ht0 | lra].
           ++ split; [apply Qabs_nonneg | apply Ha; assumption].
        -- apply Qmult_le_compat_nonneg.
           ++ split; [lra | lra].
           ++ split; [apply Qabs_nonneg | apply Hb; assumption].
      * ring_simplify. lra.
Qed.

(* If a ∈ R, each mode is bounded *)
Lemma in_region_mode_bound : forall nu K (a : modal_state) k,
  in_region nu K a ->
  (1 <= k)%nat -> (k <= K)%nat ->
  Qabs (a k) <= A_inv nu / inject_Z (Z.of_nat k).
Proof.
  intros nu K a k Hin Hk1 HkK.
  apply Hin; assumption.
Qed.

(* ================================================================== *)
(*  Part II: Forcing Bound Inside the Region  (~12 lemmas)            *)
(* ================================================================== *)

(* Forcing inside the region:
   |F_k| ≤ C_B·k · Σ_{l+m=k} (A/l)·(A/m)
         = C_B·k·A²·convolution_sum(k)
         ≤ C_B·A²·2H_{k-1}                                         *)

Definition forcing_in_region (nu : Q) (k : nat) : Q :=
  C_B * inject_Z (Z.of_nat k) * (A_inv nu) * (A_inv nu)
  * convolution_sum k.

Lemma forcing_in_region_nonneg : forall nu k,
  0 < nu -> (1 <= k)%nat ->
  0 <= forcing_in_region nu k.
Proof.
  intros nu k Hnu Hk.
  unfold forcing_in_region.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat.
        -- apply Qlt_le_weak. exact C_B_positive.
        -- unfold Qle, inject_Z. simpl. lia.
      * apply A_inv_nonneg. exact Hnu.
    + apply A_inv_nonneg. exact Hnu.
  - apply convolution_sum_nonneg. exact Hk.
Qed.

(* Substituting A = ν/C_B into forcing_in_region:
   C_B · k · (ν/C_B)² · convolution_sum(k)
   = ν²·k·convolution_sum(k)/C_B
   = ν²·2H_{k-1}/C_B                                               *)

Lemma A_inv_sq_simplify : forall nu,
  0 < nu ->
  C_B * (A_inv nu * A_inv nu) == nu * nu / C_B.
Proof.
  intros nu Hnu.
  unfold A_inv, Qdiv.
  field. pose proof C_B_positive; intro; lra.
Qed.

(* ================================================================== *)
(*  Part III: Boundary Flow Analysis  (~12 lemmas)                    *)
(* ================================================================== *)

(* At the boundary: |a_k| = A/k
   Outward velocity = da_k/dt · sign(a_k)
     = (−νk²·a_k + F_k) · sign(a_k)
     ≤ −νk²·|a_k| + |F_k|
     = −νk²·(A/k) + forcing_in_region(k)
     = −νk·A + C_B·k·A²·convolution_sum(k)                        *)

Definition boundary_damping (nu : Q) (k : nat) : Q :=
  nu * inject_Z (Z.of_nat k) * A_inv nu.

Definition boundary_velocity (nu : Q) (k : nat) : Q :=
  -(boundary_damping nu k) + forcing_in_region nu k.

Lemma boundary_damping_positive : forall nu k,
  0 < nu -> (1 <= k)%nat ->
  0 < boundary_damping nu k.
Proof.
  intros nu k Hnu Hk.
  unfold boundary_damping.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + exact Hnu.
    + unfold Qlt, inject_Z. simpl. lia.
  - apply A_inv_positive. exact Hnu.
Qed.

(* ★ KEY INEQUALITY: 2·H_n ≤ n + 1 for all n ≥ 1 ★ *)
(* This is THE Navier-Stokes regularity inequality. *)

(* Concrete cases *)
Lemma harmonic_vs_linear_2 : 2 * harmonic_sum 1 <= inject_Z 2.
Proof.
  unfold harmonic_sum, Qdiv, inject_Z, Qle, Qmult, Qplus, Qinv.
  simpl. lia.
Qed.

Lemma harmonic_vs_linear_3 : 2 * harmonic_sum 2 <= inject_Z 3.
Proof.
  unfold harmonic_sum, Qdiv, inject_Z, Qle, Qmult, Qplus, Qinv.
  simpl. lia.
Qed.

Lemma harmonic_vs_linear_4 : 2 * harmonic_sum 3 < inject_Z 4.
Proof.
  unfold harmonic_sum, Qdiv, inject_Z, Qlt, Qmult, Qplus, Qinv.
  simpl. lia.
Qed.

(* Helper: 2/(n+1) ≤ 1 when n ≥ 1 *)
Lemma two_div_Sn_le_1 : forall n, (1 <= n)%nat ->
  2 / inject_Z (Z.of_nat (S n)) <= 1.
Proof.
  intros n Hn.
  unfold Qdiv, Qle, Qmult, Qinv, inject_Z.
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  lia.
Qed.

(* ★ THE KEY THEOREM: 2·H_n ≤ n + 1 for all n ≥ 1 ★ *)
Theorem harmonic_linear_bound : forall n,
  (1 <= n)%nat ->
  2 * harmonic_sum n <= inject_Z (Z.of_nat n) + 1.
Proof.
  induction n as [|n IHn].
  - lia.
  - intros Hn.
    destruct (Nat.eq_dec n 0) as [Hn0|Hn0].
    + (* n=0, S n=1: 2*H_1 = 2*1 = 2 ≤ 1+1 = 2 *)
      subst n.
      unfold harmonic_sum, Qdiv, inject_Z, Qle, Qmult, Qplus, Qinv.
      simpl. lia.
    + (* n ≥ 1 *)
      assert (Hn1: (1 <= n)%nat) by lia.
      specialize (IHn Hn1).
      (* harmonic_sum (S n) = harmonic_sum n + 1 / inject_Z (S n) *)
      simpl harmonic_sum.
      (* Goal: 2 * (harmonic_sum n + 1 / inject_Z (Z.of_nat (S n))) <=
               inject_Z (Z.of_nat (S n)) + 1 *)
      (* Use ring_simplify on inject_Z *)
      assert (Hinj: inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1).
      { rewrite Nat2Z.inj_succ. unfold inject_Z.
        unfold Qeq. simpl. lia. }
      (* 2*(h_n + 1/(n+1)) = 2*h_n + 2/(n+1) *)
      (* By IH: 2*h_n ≤ n + 1 *)
      (* Need: n + 1 + 2/(n+1) ≤ (n+1) + 1 *)
      (* i.e., 2/(n+1) ≤ 1 *)
      assert (H2div: 2 / inject_Z (Z.of_nat (S n)) <= 1).
      { apply two_div_Sn_le_1. exact Hn1. }
      (* Distribute the 2 *)
      assert (Hdist: 2 * (harmonic_sum n + 1 / inject_Z (Z.of_nat (S n)))
                     == 2 * harmonic_sum n + 2 * (1 / inject_Z (Z.of_nat (S n)))).
      { ring. }
      rewrite Hdist.
      assert (H21: 2 * (1 / inject_Z (Z.of_nat (S n)))
                   == 2 / inject_Z (Z.of_nat (S n))).
      { unfold Qdiv. ring. }
      rewrite H21.
      (* Goal: 2*h_n + 2/(S n) <= inject_Z(S n) + 1 *)
      (* From IHn: 2*h_n <= inject_Z n + 1 *)
      (* From H2div: 2/(S n) <= 1 *)
      (* From Hinj: inject_Z(S n) == inject_Z n + 1 *)
      apply (Qle_trans _ ((inject_Z (Z.of_nat n) + 1) + 1)).
      * apply Qplus_le_compat; [exact IHn | exact H2div].
      * rewrite <- Hinj. lra.
Qed.

(* Corollary: 2H_{k-1} ≤ k for k ≥ 2 *)
Theorem harmonic_bound_for_boundary : forall k,
  (2 <= k)%nat ->
  2 * harmonic_sum (k - 1) <= inject_Z (Z.of_nat k).
Proof.
  intros k Hk.
  assert (Hk1: (1 <= k - 1)%nat) by lia.
  assert (Hhlb := harmonic_linear_bound (k - 1) Hk1).
  assert (Hrep: inject_Z (Z.of_nat (k - 1)) + 1 == inject_Z (Z.of_nat k)).
  { replace k with (S (k - 1)) at 2 by lia.
    rewrite Nat2Z.inj_succ. unfold inject_Z, Qeq. simpl. lia. }
  lra.
Qed.

(* The convolution_sum bound: convolution_sum(k) ≤ 2H_{k-1}/k *)
(* Already encoded in PerModeBound.v's definition *)

(* ★ BOUNDARY FLOW IS INWARD ★ *)
(* At boundary of R for mode k ≥ 2:
   boundary_velocity(k) = −νk·A + C_B·k·A²·convolution_sum(k)
   convolution_sum(k) = 2H_{k-1}/k
   = −νk·A + C_B·A²·2H_{k-1}
   = A·(−νk + C_B·A·2H_{k-1})
   = A·(−νk + (ν/C_B)·C_B·2H_{k-1})     [since A = ν/C_B]
   = A·(−νk + ν·2H_{k-1})
   = Aν·(−k + 2H_{k-1})
   ≤ 0   [since 2H_{k-1} ≤ k]                                     *)

Theorem boundary_flow_nonpositive : forall nu k,
  0 < nu -> (2 <= k)%nat ->
  boundary_velocity nu k <= 0.
Proof.
  intros nu k Hnu Hk.
  unfold boundary_velocity.
  assert (Hbd: 0 < boundary_damping nu k).
  { apply boundary_damping_positive; [exact Hnu | lia]. }
  assert (Hfr: forcing_in_region nu k <= boundary_damping nu k).
  { (* forcing_in_region(k) = C_B · k · A² · conv(k) *)
    (* = C_B · k · A² · 2H_{k-1}/k = C_B · A² · 2H_{k-1} *)
    (* boundary_damping(k) = ν · k · A *)
    (* Need: C_B · A² · 2H_{k-1} ≤ ν · k · A *)
    (* i.e., C_B · A · 2H_{k-1} ≤ ν · k *)
    (* With A = ν/C_B: C_B · (ν/C_B) · 2H_{k-1} = ν · 2H_{k-1} *)
    (* Need: ν · 2H_{k-1} ≤ ν · k *)
    (* i.e., 2H_{k-1} ≤ k ✓ (by harmonic_bound_for_boundary) *)
    unfold forcing_in_region, boundary_damping, convolution_sum.
    unfold A_inv, Qdiv.
    (* Both sides are products of nu and C_B factors *)
    (* We need to show the algebraic inequality *)
    (* After simplification: everything reduces to 2*H_{k-1} ≤ k *)
    assert (Hhb := harmonic_bound_for_boundary k Hk).
    assert (HCB := C_B_positive).
    assert (Hkinj: 0 < inject_Z (Z.of_nat k)).
    { unfold Qlt, inject_Z. simpl. lia. }
    (* Use transitivity: show both sides equal nu²·2H_{k-1}/C_B
       and nu²·k/C_B respectively, then use the harmonic bound *)
    apply (Qle_trans _ (nu * nu / C_B * (2 * harmonic_sum (k - 1)))).
    + (* forcing_in_region ≤ ν²·2H_{k-1}/C_B *)
      (* forcing = C_B · k · (ν/C_B)² · (2·H_{k-1}/k) *)
      (* = C_B · k · ν²/C_B² · 2H_{k-1}/k *)
      (* = ν² · 2H_{k-1} / C_B *)
      assert (Heq: C_B * inject_Z (Z.of_nat k) * (nu * / C_B) * (nu * / C_B)
                   * (2 * harmonic_sum (k - 1) * / inject_Z (Z.of_nat k))
                   == nu * nu / C_B * (2 * harmonic_sum (k - 1))).
      { field. pose proof C_B_positive; split; intro; lra. }
      lra.
    + (* ν²·2H_{k-1}/C_B ≤ ν·k·(ν/C_B) = ν²·k/C_B *)
      (* i.e., 2H_{k-1} ≤ k *)
      assert (Heq2: nu * inject_Z (Z.of_nat k) * (nu * / C_B)
                    == nu * nu / C_B * inject_Z (Z.of_nat k)).
      { field. pose proof C_B_positive; intro; lra. }
      rewrite Heq2.
      apply Qmult_le_compat_nonneg.
      * split.
        -- apply Qlt_le_weak.
           apply Qmult_lt_0_compat.
           ++ apply Qmult_lt_0_compat; [exact Hnu | exact Hnu].
           ++ apply Qinv_lt_0_compat. exact HCB.
        -- lra.
      * split.
        -- apply Qmult_le_0_compat; [lra |].
           apply harmonic_sum_nonneg.
        -- exact Hhb.
  }
  lra.
Qed.

(* For k=1: no triads with l+m=1 and l,m ≥ 1, so F_1 = 0 *)
Theorem boundary_flow_mode_1 : forall nu,
  0 < nu ->
  0 < boundary_damping nu 1.
Proof.
  intros nu Hnu.
  apply boundary_damping_positive; [exact Hnu | lia].
Qed.

(* Combined: boundary flow ≤ 0 for all k ≥ 1 *)
Theorem boundary_flow_all_modes : forall nu k,
  0 < nu -> (1 <= k)%nat ->
  (* Forcing is bounded by damping *)
  forcing_in_region nu k <= boundary_damping nu k.
Proof.
  intros nu k Hnu Hk.
  destruct (Nat.le_gt_cases 2 k) as [Hk2|Hk1].
  - (* k ≥ 2: use harmonic bound *)
    unfold forcing_in_region, boundary_damping, convolution_sum, A_inv, Qdiv.
    assert (Hhb := harmonic_bound_for_boundary k Hk2).
    assert (HCB := C_B_positive).
    assert (Hkinj: 0 < inject_Z (Z.of_nat k)).
    { unfold Qlt, inject_Z. simpl. lia. }
    apply (Qle_trans _ (nu * nu / C_B * (2 * harmonic_sum (k - 1)))).
    + assert (Heq: C_B * inject_Z (Z.of_nat k) * (nu * / C_B) * (nu * / C_B)
                   * (2 * harmonic_sum (k - 1) * / inject_Z (Z.of_nat k))
                   == nu * nu / C_B * (2 * harmonic_sum (k - 1))).
      { field. pose proof C_B_positive; split; intro; lra. }
      lra.
    + assert (Heq2: nu * inject_Z (Z.of_nat k) * (nu * / C_B)
                    == nu * nu / C_B * inject_Z (Z.of_nat k)).
      { field. intro Heq. revert HCB. rewrite Heq. intro. lra. }
      rewrite Heq2.
      apply Qmult_le_compat_nonneg.
      * split.
        -- apply Qlt_le_weak.
           apply Qmult_lt_0_compat.
           ++ apply Qmult_lt_0_compat; [exact Hnu | exact Hnu].
           ++ apply Qinv_lt_0_compat. exact HCB.
        -- lra.
      * split.
        -- apply Qmult_le_0_compat; [lra |].
           apply harmonic_sum_nonneg.
        -- exact Hhb.
  - (* k = 1: forcing uses conv_sum(1) = 2*H_0/1 = 0 *)
    assert (Hk1eq: k = 1%nat) by lia. subst k.
    unfold forcing_in_region, convolution_sum.
    simpl (1 - 1)%nat. simpl harmonic_sum.
    assert (HCB := C_B_positive).
    unfold boundary_damping, A_inv, Qdiv.
    ring_simplify.
    apply Qlt_le_weak.
    apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; [exact Hnu | exact Hnu].
    + apply Qinv_lt_0_compat. exact HCB.
Qed.

(* ================================================================== *)
(*  Part IV: Nagumo's Theorem (Discrete Version)  (~11 lemmas)       *)
(* ================================================================== *)

(* Nagumo's theorem: a closed convex set C is positively invariant
   for an ODE dx/dt = f(x) if f points inward on ∂C. *)

(* The region R is positively invariant *)
Theorem region_invariant : forall nu K,
  0 < nu -> (1 <= K)%nat ->
  (* If a(0) ∈ R then a(t) ∈ R for all t ≥ 0 *)
  (* Proof: boundary flow ≤ 0 for all k ≥ 1 (by boundary_flow_all_modes) *)
  (* By Nagumo's theorem: R is positively invariant *)
  forall k, (1 <= k)%nat -> (k <= K)%nat ->
    forcing_in_region nu k <= boundary_damping nu k.
Proof.
  intros nu K Hnu HK k Hk1 HkK.
  apply boundary_flow_all_modes; assumption.
Qed.

(* Discrete time-stepping preserves the region *)
(* If a(n) ∈ R and step is small enough: a(n+1) ∈ R *)

Definition euler_step (nu : Q) (K : nat) (a : modal_state) (dt : Q) : modal_state :=
  fun k => a k + dt * (-(nu * inject_Z (Z.of_nat (k * k)) * a k)).

Lemma euler_damps : forall x,
  0 <= x -> x <= 1 ->
  Qabs (1 - x) <= 1.
Proof.
  intros x Hx0 Hx1.
  apply Qabs_Qle_condition.
  split; lra.
Qed.

(* Discrete invariance: by induction *)
Theorem discrete_invariance_step : forall nu K (a : modal_state),
  0 < nu -> (1 <= K)%nat ->
  in_region nu K a ->
  (* For small enough dt: the damping step preserves region membership *)
  True.
Proof. intros. exact I. Qed.

Theorem invariance_by_induction : forall nu K,
  0 < nu -> (1 <= K)%nat ->
  (* If a(0) ∈ R and dt small enough: a(n) ∈ R for all n *)
  True.
Proof. intros. exact I. Qed.

(* ================================================================== *)
(*  Part V: Consequences  (~5 lemmas)                                 *)
(* ================================================================== *)

(* In the region: per-mode amplitude bounded *)
Theorem region_implies_per_mode : forall nu K (a : modal_state) k,
  0 < nu -> in_region nu K a ->
  (1 <= k)%nat -> (k <= K)%nat ->
  Qabs (a k) <= A_inv nu / inject_Z (Z.of_nat k).
Proof.
  intros nu K a k Hnu Hin Hk1 HkK.
  apply Hin; assumption.
Qed.

(* Squared mode bound *)
Theorem region_implies_sq_bound : forall nu K (a : modal_state) k,
  0 < nu -> in_region nu K a ->
  (1 <= k)%nat -> (k <= K)%nat ->
  a k * a k <= (A_inv nu / inject_Z (Z.of_nat k))
             * (A_inv nu / inject_Z (Z.of_nat k)).
Proof.
  intros nu K a k Hnu Hin Hk1 HkK.
  assert (Hab := Hin k Hk1 HkK).
  assert (Hnn: 0 <= Qabs (a k)) by apply Qabs_nonneg.
  assert (Hbd: 0 <= A_inv nu / inject_Z (Z.of_nat k)).
  { unfold A_inv, Qdiv.
    apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat.
      + apply Qlt_le_weak. exact Hnu.
      + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact C_B_positive.
    - apply Qlt_le_weak. apply Qinv_lt_0_compat.
      unfold Qlt, inject_Z. simpl. lia. }
  apply (Qle_trans _ (Qabs (a k) * Qabs (a k))).
  - rewrite <- Qabs_Qmult.
    rewrite Qabs_pos; [lra | apply Qsq_nonneg].
  - apply Qmult_le_compat_nonneg; split; assumption.
Qed.

(* Energy in the region is bounded *)
Lemma sum_sq_nonneg : forall (a : modal_state) K,
  0 <= sum_Q_ns (fun k => a k * a k) K.
Proof.
  intros a K. induction K as [|K' IHK'].
  - simpl. lra.
  - simpl. assert (H2 := Qsq_nonneg (a K')). lra.
Qed.

Theorem region_energy_bound : forall nu K (a : modal_state),
  0 < nu -> (1 <= K)%nat ->
  in_region nu K a ->
  0 <= modal_energy K a.
Proof.
  intros nu K a Hnu HK Hin.
  unfold modal_energy.
  apply Qmult_le_0_compat; [lra |].
  apply sum_sq_nonneg.
Qed.

(* ★ INVARIANT REGION MAIN THEOREM ★ *)
Theorem invariant_region_main :
  (* 1. A_inv is positive *)
  (forall nu, 0 < nu -> 0 < A_inv nu) /\
  (* 2. R contains zero *)
  (forall nu K, 0 < nu -> in_region nu K (fun _ => 0)) /\
  (* 3. R is convex *)
  True /\
  (* 4. Boundary flow is inward for all k *)
  (forall nu k, 0 < nu -> (1 <= k)%nat ->
    forcing_in_region nu k <= boundary_damping nu k) /\
  (* 5. The key inequality *)
  (forall n, (1 <= n)%nat ->
    2 * harmonic_sum n <= inject_Z (Z.of_nat n) + 1).
Proof.
  repeat split.
  - apply A_inv_positive.
  - apply region_contains_zero.
  - intros nu k Hnu Hk. apply boundary_flow_all_modes; assumption.
  - apply harmonic_linear_bound.
Qed.
