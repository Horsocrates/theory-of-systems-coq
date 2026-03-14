(** * ProcessBounds.v — Process Mass Gap and Convergence Bounds
    Elements: has_process_mass_gap, pmg_cauchy, pmg_positive, pathological_no_pmg
    Roles:    defines the PMG record; bridges PMG to Cauchy condition
    Rules:    PMG guarantees Cauchy via geometric decay rate
    Status:   complete
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESSBOUNDS — Process Mass Gap and Convergence Bounds              *)
(*                                                                            *)
(*  The has_process_mass_gap record captures:                                 *)
(*    PMG1: uniform lower bound (gap is strictly positive)                   *)
(*    PMG2: Cauchy rate via geometric decay                                  *)
(*    PMG3: monotone decreasing (gap narrows with lattice refinement)        *)
(*                                                                            *)
(*  STATUS: 14 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  Part I: The Process Mass Gap Record                                *)
(* ================================================================== *)

(** A process has a mass gap if it has:
    - PMG1: a uniform positive lower bound (the gap doesn't vanish)
    - PMG2: a geometric Cauchy rate (convergence speed)
    - PMG3: monotone decreasing (gap narrows with refinement) *)
Record has_process_mass_gap (R : RealProcess) : Type := mkPMG {
  pmg_delta : Q;
  pmg_rate : Q;
  pmg_const : Q;
  pmg1_positive : 0 < pmg_delta;
  pmg1_bound : forall n, pmg_delta <= R n;
  pmg2_rate_bound : 0 < pmg_rate /\ pmg_rate < 1;
  pmg2_const_pos : 0 < pmg_const;
  pmg2_cauchy_rate : forall m n,
    Qabs (R m - R n) <= pmg_const * Qpow pmg_rate (Nat.min m n);
  pmg3_decreasing : monotone_decreasing R
}.

(* ================================================================== *)
(*  Part II: PMG implies Cauchy and key properties                     *)
(* ================================================================== *)

(** Geometric rate vanishes: C * r^N -> 0 *)
Lemma scaled_qpow_vanish : forall C r eps,
  0 < C -> 0 < r -> r < 1 -> 0 < eps ->
  exists N, C * Qpow r N < eps.
Proof.
  intros C r eps HC Hr Hr1 Heps.
  assert (HepsC : 0 < eps * / C).
  { apply Qmult_lt_0_compat; auto. apply Qinv_lt_0_compat; auto. }
  destruct (Qpow_vanish r (eps * / C) Hr Hr1 HepsC) as [N HN].
  exists N.
  assert (Hnn : 0 <= Qpow r N) by (apply Qpow_nonneg; lra).
  assert (Heq : C * (eps * / C) == eps) by (field; lra).
  apply Qlt_le_trans with (C * (eps * / C)).
  - apply Qmult_lt_l; auto.
  - rewrite Heq. lra.
Qed.

(** PMG implies the process is Cauchy *)
Theorem pmg_implies_cauchy : forall R,
  has_process_mass_gap R -> is_Cauchy R.
Proof.
  intros R [delta r C Hdelta Hbound [Hr Hr1] HC Hrate Hdec].
  apply cauchy_from_bound with (bound := fun k => C * Qpow r k).
  - intros m n. apply Hrate.
  - intros eps Heps.
    destruct (scaled_qpow_vanish C r eps HC Hr Hr1 Heps) as [N HN].
    exists N. intros k Hk.
    apply Qle_lt_trans with (C * Qpow r N).
    + assert (Hpk : Qpow r k <= Qpow r N).
      { clear -Hr Hr1 Hk. induction k as [| k' IH].
        - assert (N = 0%nat) by lia. subst. lra.
        - destruct (Nat.eq_dec (S k') N).
          + subst. lra.
          + assert (Hk' : (N <= k')%nat) by lia.
            specialize (IH Hk').
            assert (Hstep : Qpow r (S k') <= Qpow r k')
              by (apply Qpow_monotone_dec; lra).
            lra. }
      assert (HCnn : 0 <= C) by lra.
      assert (Hpn : 0 <= Qpow r N) by (apply Qpow_nonneg; lra).
      apply Qmult_le_compat_nonneg.
      * split; lra.
      * split; [apply Qpow_nonneg; lra | exact Hpk].
    + exact HN.
Qed.

(** PMG implies uniform positive lower bound *)
Lemma pmg_positive : forall R,
  has_process_mass_gap R -> exists delta, 0 < delta /\ forall n, delta <= R n.
Proof.
  intros R Hpmg.
  exists (pmg_delta R Hpmg).
  split.
  - exact (pmg1_positive R Hpmg).
  - exact (pmg1_bound R Hpmg).
Qed.

(** PMG implies bounded in interval [delta, R 0] *)
Lemma pmg_in_interval : forall R (Hpmg : has_process_mass_gap R),
  in_interval (pmg_delta R Hpmg) (R 0%nat) R.
Proof.
  intros R Hpmg n.
  split.
  - apply (pmg1_bound R Hpmg).
  - apply monotone_decreasing_le.
    + exact (pmg3_decreasing R Hpmg).
    + lia.
Qed.

(** PMG: the initial value is an upper bound *)
Lemma pmg_upper_bound : forall R,
  has_process_mass_gap R -> forall n, R n <= R 0%nat.
Proof.
  intros R Hpmg n.
  apply monotone_decreasing_le.
  - exact (pmg3_decreasing R Hpmg).
  - lia.
Qed.

(** PMG implies process_equiv with any process within rate *)
Lemma pmg_equiv_within_rate : forall R1 R2 r1 r2,
  0 < r1 -> r1 < 1 -> 0 < r2 -> r2 < 1 ->
  (forall n, Qabs (R1 n - R2 n) <= Qpow r1 n + Qpow r2 n) ->
  R1 ~~ R2.
Proof.
  intros R1 R2 r1 r2 Hr1 Hr1' Hr2 Hr2' Hdiff eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Qpow_vanish r1 (eps * (1#2)) Hr1 Hr1' Heps2) as [N1 HN1].
  destruct (Qpow_vanish r2 (eps * (1#2)) Hr2 Hr2' Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  apply Qle_lt_trans with (Qpow r1 n + Qpow r2 n).
  - apply Hdiff.
  - assert (qpow_le_gen : forall r N k, 0 <= r -> r <= 1 -> (N <= k)%nat ->
        Qpow r k <= Qpow r N).
    { intros r0 N0 k0 Hr0 Hr0' Hle0.
      induction k0.
      - assert (N0 = 0%nat) by lia. subst. lra.
      - destruct (Nat.eq_dec N0 (S k0)); [subst; lra |].
        assert (HN0k : (N0 <= k0)%nat) by lia.
        specialize (IHk0 HN0k).
        apply Qle_trans with (Qpow r0 k0); auto.
        apply Qpow_monotone_dec; auto. }
    assert (Hm1 : Qpow r1 n <= Qpow r1 N1) by (apply qpow_le_gen; [lra | lra | lia]).
    assert (Hm2 : Qpow r2 n <= Qpow r2 N2) by (apply qpow_le_gen; [lra | lra | lia]).
    lra.
Qed.

(* ================================================================== *)
(*  Part III: Constructing PMG from components                         *)
(* ================================================================== *)

(** Build PMG from separate proofs *)
Lemma build_pmg : forall R delta r C,
  0 < delta ->
  (forall n, delta <= R n) ->
  0 < r -> r < 1 ->
  0 < C ->
  (forall m n, Qabs (R m - R n) <= C * Qpow r (Nat.min m n)) ->
  monotone_decreasing R ->
  has_process_mass_gap R.
Proof.
  intros R delta r C Hdelta Hbound Hr Hr1 HC Hrate Hdec.
  exact (mkPMG R delta r C Hdelta Hbound (conj Hr Hr1) HC Hrate Hdec).
Qed.

(** Constant processes trivially have PMG (with any rate) *)
Lemma const_pmg : forall q,
  0 < q ->
  has_process_mass_gap (const_process q).
Proof.
  intros q Hq.
  apply (mkPMG (const_process q) q (1#2) 1).
  - exact Hq.
  - intros n. unfold const_process. lra.
  - split; lra.
  - lra.
  - intros m n. unfold const_process.
    assert (Heq : q - q == 0) by ring. rewrite Heq.
    rewrite Qabs_pos.
    + assert (Hpow : 0 < Qpow (1#2) (Nat.min m n)).
      { apply Qpow_pos; lra. }
      lra.
    + lra.
  - intros n. unfold const_process. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Pathological examples                                     *)
(* ================================================================== *)

(** Zero process has no PMG since delta > 0 can't be <= 0 *)
Theorem pathological_no_pmg :
  has_process_mass_gap (const_process 0) -> False.
Proof.
  intros [delta r C Hdelta Hbound _ _ _ _].
  specialize (Hbound 0%nat). unfold const_process in Hbound. lra.
Qed.

(** A process converging to 0 has no PMG *)
Lemma vanishing_no_pmg : forall R,
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> R n < eps) ->
  has_process_mass_gap R -> False.
Proof.
  intros R Hvan [delta r C Hdelta Hbound _ _ _ _].
  destruct (Hvan delta Hdelta) as [N HN].
  specialize (HN N (Nat.le_refl N)).
  specialize (Hbound N). lra.
Qed.

(** PMG is preserved under positive scaling *)
Lemma pmg_scale : forall R c,
  0 < c -> has_process_mass_gap R ->
  has_process_mass_gap (process_scale c R).
Proof.
  intros R c Hc [delta r C Hdelta Hbound [Hr Hr1] HC Hrate Hdec].
  apply (mkPMG (process_scale c R) (c * delta) r (c * C)).
  - apply Qmult_lt_0_compat; auto.
  - intros n. unfold process_scale.
    assert (Hle := Hbound n).
    apply Qmult_le_l; auto.
  - split; auto.
  - apply Qmult_lt_0_compat; auto.
  - intros m n. unfold process_scale.
    assert (Heq : c * R m - c * R n == c * (R m - R n)) by ring.
    rewrite Heq. rewrite Qabs_Qmult.
    assert (Hcabs : Qabs c == c) by (rewrite Qabs_pos; lra).
    rewrite Hcabs.
    assert (Hrate_mn := Hrate m n).
    assert (Hmul : c * Qabs (R m - R n) <= c * (C * Qpow r (Nat.min m n))).
    { apply Qmult_le_l; auto. }
    assert (Hassoc : c * (C * Qpow r (Nat.min m n)) == c * C * Qpow r (Nat.min m n))
      by ring.
    lra.
  - intros n. unfold process_scale.
    specialize (Hdec n).
    assert (Hmul : c * R (S n) <= c * R n).
    { apply Qmult_le_l; auto. }
    lra.
Qed.
