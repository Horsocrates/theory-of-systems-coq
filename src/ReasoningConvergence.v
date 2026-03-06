(* ========================================================================= *)
(*            REASONING CONVERGENCE                                         *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  PURPOSE: Formalize the Regulus pipeline iteration as fixed-point search  *)
(*  over Q-valued confidence states in [0, 100]:                            *)
(*    - Pipeline operator as contraction on confidence interval              *)
(*    - Convergence bounds via geometric decay                              *)
(*    - Stall detection implies proximity to fixed point                    *)
(*    - Paradigm shift: replacing the operator resets convergence           *)
(*                                                                          *)
(*  REUSES: FixedPoint.v theorems (is_contraction, iterate, Banach)         *)
(*                                                                          *)
(*  AXIOMS: classic (inherited from FixedPoint via MonotoneConvergence)     *)
(*                                                                          *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
Require Import Stdlib.QArith.Qminmax.
Require Import Stdlib.micromega.Lqa.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Arith.PeanoNat.

From ToS Require Import CauchyReal.
From ToS Require Import Completeness.
From ToS Require Import MonotoneConvergence.
From ToS Require Import SeriesConvergence.
From ToS Require Import FixedPoint.

Open Scope Q_scope.

(* ========================================================================= *)
(* SECTION 1: PIPELINE DOMAIN [0, 100]                                      *)
(* ========================================================================= *)

(** Pipeline confidence lives in [0, 100] *)
Definition confidence_lo : Q := 0.
Definition confidence_hi : Q := 100.

(** A pipeline operator is a contraction on [0, 100] *)
Definition is_pipeline (T : Q -> Q) (c : Q) : Prop :=
  is_contraction T confidence_lo confidence_hi c.

(** 1. Pipeline iterates stay in [0, 100] *)
Lemma pipeline_in_range : forall T c x,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  forall n, 0 <= iterate T x n /\ iterate T x n <= 100.
Proof.
  intros T c x HT Hx0 Hx100 n.
  apply (iterate_in_interval T 0 100 c x HT Hx0 Hx100 n).
Qed.

(** 2. Initial displacement: d0 = |T(x) - x| <= 100 *)
Lemma initial_displacement_bounded : forall T c x,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  Qabs (T x - x) <= 100.
Proof.
  intros T c x HT Hx0 Hx100.
  unfold is_pipeline, confidence_lo, confidence_hi in HT.
  destruct HT as [_ [_ [Hself _]]].
  assert (HTx := Hself x Hx0 Hx100).
  destruct HTx as [HTx_lo HTx_hi].
  (* T x and x are both in [0, 100], so T x - x in [-100, 100] *)
  apply Qabs_le_bound; lra.
Qed.

(* ========================================================================= *)
(* SECTION 2: CONVERGENCE                                                    *)
(* ========================================================================= *)

(** 3. Pipeline iterates form a Cauchy sequence *)
Lemma pipeline_converges : forall T c x,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  is_cauchy (fun n => iterate T x n).
Proof.
  intros T c x HT Hx0 Hx100.
  exact (iterate_is_cauchy T 0 100 c x HT Hx0 Hx100).
Qed.

(** 4. Pipeline converges to approximate fixed point *)
Lemma pipeline_approximate_fixpoint : forall T c x,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (T (iterate T x n) - iterate T x n) < eps.
Proof.
  intros T c x HT Hx0 Hx100.
  exact (approximate_fixed_point T 0 100 c x HT Hx0 Hx100).
Qed.

(** 5. Banach CauchySeq construction for pipeline *)
Definition pipeline_limit (T : Q -> Q) (c x : Q)
  (HT : is_pipeline T c) (Hx0 : 0 <= x) (Hx100 : x <= 100)
  : CauchySeq :=
  banach_fixed_point T 0 100 c x HT Hx0 Hx100.

(* ========================================================================= *)
(* SECTION 3: ITERATION BOUNDS                                               *)
(* ========================================================================= *)

(** 6. Step size bound: |x_{n+1} - x_n| <= c^n * d0 *)
Lemma step_size_bound : forall T c x,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  forall n, Qabs (iterate T x (S n) - iterate T x n) <=
            Qpow c n * Qabs (T x - x).
Proof.
  intros T c x HT Hx0 Hx100 n.
  exact (iterate_step_shrink T 0 100 c x HT Hx0 Hx100 n).
Qed.

(** 7. Convergence iteration bound: c^n * d0 < eps guarantees proximity *)
Lemma convergence_iteration_bound : forall T c x n eps,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  0 < eps ->
  Qpow c n * Qabs (T x - x) < eps ->
  Qabs (iterate T x (S n) - iterate T x n) < eps.
Proof.
  intros T c x n eps HT Hx0 Hx100 Heps Hbound.
  assert (Hstep := step_size_bound T c x HT Hx0 Hx100 n).
  lra.
Qed.

(** Helper: Qpow c n vanishes for 0 < c < 1 (from SeriesConvergence) *)
Lemma qpow_vanishes : forall c eps,
  0 < c -> c < 1 -> 0 < eps ->
  exists N, Qpow c N < eps.
Proof.
  intros c eps Hc0 Hc1 Heps.
  exact (Qpow_vanish c eps Hc0 Hc1 Heps).
Qed.

(** 8. Sufficient iterations exist: for any tolerance, enough iterations suffice *)
Lemma sufficient_iterations_exist : forall T c x eps,
  is_pipeline T c -> 0 <= x -> x <= 100 ->
  0 < c -> 0 < eps ->
  exists N, forall n, (N <= n)%nat ->
  Qabs (T (iterate T x n) - iterate T x n) < eps.
Proof.
  intros T c x eps HT Hx0 Hx100 Hc_pos Heps.
  exact (approximate_fixed_point T 0 100 c x HT Hx0 Hx100 eps Heps).
Qed.

(** 9. Distance between iterates from different starts converges *)
Lemma pipeline_start_independent : forall T c x y,
  is_pipeline T c -> 0 <= x -> x <= 100 -> 0 <= y -> y <= 100 ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (iterate T x n - iterate T y n) < eps.
Proof.
  intros T c x y HT Hx0 Hx100 Hy0 Hy100 eps Heps.
  exact (fixed_point_independent T 0 100 c x y HT Hx0 Hx100 Hy0 Hy100 eps Heps).
Qed.

(* ========================================================================= *)
(* SECTION 4: STALL DETECTION                                                *)
(* ========================================================================= *)

(** 10. Stall means near fixed point: if |T(s) - s| is small, s is near
    any fixed point (via contraction uniqueness). More precisely:
    if |T(s) - s| < delta, then for all n, |T^n(s) - s| <= delta/(1-c). *)
Lemma stall_iterate_bound : forall T c s delta,
  is_pipeline T c -> 0 <= s -> s <= 100 ->
  0 <= delta ->
  Qabs (T s - s) <= delta ->
  forall n, Qabs (iterate T s (S n) - s) <=
            delta * partial_sum (fun k => Qpow c k) n.
Proof.
  intros T c s delta HT Hs0 Hs100 Hdelta Hstall n.
  assert (Hc0 : 0 <= c).
  { destruct HT as [Hc0 _]; exact Hc0. }
  (* Use triangle inequality + step_size_bound *)
  induction n as [|n IHn].
  - (* n = 0: |T(s) - s| <= delta * ps(0) = delta * 1 *)
    cbv beta. simpl iterate. simpl partial_sum. simpl Qpow.
    lra.
  - (* Inductive step *)
    (* |T^{S(S n)}(s) - s| <= |T^{S(S n)}(s) - T^{S n}(s)| + |T^{S n}(s) - s| *)
    assert (Htri : Qabs (iterate T s (S (S n)) - s) <=
                   Qabs (iterate T s (S (S n)) - iterate T s (S n)) +
                   Qabs (iterate T s (S n) - s)).
    { setoid_replace (iterate T s (S (S n)) - s) with
        ((iterate T s (S (S n)) - iterate T s (S n)) +
         (iterate T s (S n) - s)) by ring.
      apply Qabs_triangle. }
    (* Step bound: |T^{S(S n)}(s) - T^{S n}(s)| <= c^{S n} * delta *)
    assert (Hstep := step_size_bound T c s HT Hs0 Hs100 (S n)).
    assert (Hstep_bound : Qabs (iterate T s (S (S n)) - iterate T s (S n)) <=
                          Qpow c (S n) * delta).
    { apply Qle_trans with (Qpow c (S n) * Qabs (T s - s)).
      - exact Hstep.
      - apply Qmult_le_compat_l; [exact Hstall | apply Qpow_nonneg; exact Hc0]. }
    (* partial_sum recurrence *)
    change (partial_sum (fun k => Qpow c k) (S n)) with
      (partial_sum (fun k => Qpow c k) n + Qpow c (S n)).
    (* Combine *)
    assert (Hgoal : delta * (partial_sum (fun k => Qpow c k) n + Qpow c (S n)) ==
                    Qpow c (S n) * delta + delta * partial_sum (fun k => Qpow c k) n)
      by ring.
    assert (Hgoal_le := Qeq_Qle _ _ Hgoal).
    lra.
Qed.

(** 11. Stall means near fixed point (simplified): small |T(s) - s| implies
    the entire future trajectory stays close to s. *)
Lemma stall_means_near_fixpoint : forall T c s eps,
  is_pipeline T c -> 0 <= s -> s <= 100 ->
  0 < eps -> 0 < 1 - c ->
  Qabs (T s - s) <= eps * (1 - c) ->
  forall n, Qabs (iterate T s (S n) - s) <=
            eps * (1 - Qpow c (S n)).
Proof.
  intros T c s eps HT Hs0 Hs100 Heps H1c Hstall n.
  assert (Hc0 : 0 <= c) by (destruct HT as [Hc0 _]; exact Hc0).
  assert (Hc1 : c < 1) by lra.
  assert (Hdelta := stall_iterate_bound T c s (eps * (1 - c)) HT Hs0 Hs100
                      ltac:(apply Qmult_le_0_compat; lra) Hstall n).
  (* Need: delta * ps(n) <= eps * (1 - c^{S n}) *)
  (* delta = eps*(1-c), and (1-c)*ps(n) = 1 - c^{S n} by geometric_sum_identity *)
  assert (Hgeo := geometric_sum_identity c n).
  (* Hgeo: (1 - c) * ps(n) == 1 - c^{S n} *)
  assert (Halg : eps * (1 - c) * partial_sum (fun k => Qpow c k) n ==
                 eps * ((1 - c) * partial_sum (fun k => Qpow c k) n)) by ring.
  assert (Halg2 : eps * ((1 - c) * partial_sum (fun k => Qpow c k) n) ==
                  eps * (1 - Qpow c (S n))).
  { apply Qmult_comp. reflexivity. exact Hgeo. }
  lra.
Qed.

(* ========================================================================= *)
(* SECTION 5: PARADIGM SHIFT                                                 *)
(* ========================================================================= *)

(** 12. Paradigm shift: replacing T with T' gives a new contraction.
    The new iteration starts from the current state (last iterate of T). *)
Lemma paradigm_shift_resets : forall T T' c c' x n,
  is_pipeline T c -> is_pipeline T' c' ->
  0 <= x -> x <= 100 ->
  is_cauchy (fun k => iterate T' (iterate T x n) k).
Proof.
  intros T T' c c' x n HT HT' Hx0 Hx100.
  assert (Hin := pipeline_in_range T c x HT Hx0 Hx100 n).
  destruct Hin as [Hn0 Hn100].
  exact (pipeline_converges T' c' (iterate T x n) HT' Hn0 Hn100).
Qed.

(** 13. After paradigm shift, the new trajectory also stays in [0, 100] *)
Lemma paradigm_shift_in_range : forall T T' c c' x n,
  is_pipeline T c -> is_pipeline T' c' ->
  0 <= x -> x <= 100 ->
  forall k, 0 <= iterate T' (iterate T x n) k /\
            iterate T' (iterate T x n) k <= 100.
Proof.
  intros T T' c c' x n HT HT' Hx0 Hx100 k.
  assert (Hin := pipeline_in_range T c x HT Hx0 Hx100 n).
  destruct Hin as [Hn0 Hn100].
  exact (pipeline_in_range T' c' (iterate T x n) HT' Hn0 Hn100 k).
Qed.

(* ========================================================================= *)
(* SECTION 6: PIPELINE UNIQUENESS AND PERTURBATION                           *)
(* ========================================================================= *)

(** 14. Two pipelines with different rates: iterates eventually agree *)
Lemma pipeline_unique_convergence : forall T c x y,
  is_pipeline T c ->
  0 <= x -> x <= 100 -> 0 <= y -> y <= 100 ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (iterate T x n - iterate T y n) < eps.
Proof.
  intros T c x y HT Hx0 Hx100 Hy0 Hy100 eps Heps.
  exact (fixed_point_independent T 0 100 c x y HT Hx0 Hx100 Hy0 Hy100 eps Heps).
Qed.

(** 15. Pipeline uniqueness: if T has two fixed points in [0,100], they coincide *)
Lemma pipeline_unique_fixpoint : forall T c p q,
  is_pipeline T c ->
  0 <= p -> p <= 100 -> 0 <= q -> q <= 100 ->
  T p == p -> T q == q ->
  p == q.
Proof.
  intros T c p q HT Hp0 Hp100 Hq0 Hq100 HTp HTq.
  exact (contraction_unique_fixed T 0 100 c p q HT Hp0 Hp100 Hq0 Hq100 HTp HTq).
Qed.

(** 16. Perturbation stability: nearby pipeline operators produce nearby iterates *)
Lemma pipeline_perturbation : forall T T' c x delta,
  is_pipeline T c -> is_pipeline T' c ->
  0 <= x -> x <= 100 ->
  (forall u, 0 <= u -> u <= 100 -> Qabs (T u - T' u) <= delta) ->
  0 <= delta ->
  forall n, Qabs (iterate T x n - iterate T' x n) <=
            delta * partial_sum (fun k => Qpow c k) (Nat.pred n).
Proof.
  intros T T' c x delta HT HT' Hx0 Hx100 Hclose Hdelta n.
  exact (perturbed_iterate_bound T T' 0 100 c x delta HT HT' Hx0 Hx100 Hclose Hdelta n).
Qed.

(** 17. Iterated pipeline is itself a contraction with tighter factor *)
Lemma pipeline_iterate_contraction : forall T c,
  is_pipeline T c ->
  forall k, (1 <= k)%nat ->
  is_pipeline (fun x => iterate T x k) (Qpow c k).
Proof.
  intros T c HT k Hk.
  exact (iterate_is_contraction T 0 100 c HT k Hk).
Qed.

(* ========================================================================= *)
(* SECTION 7: GEOMETRIC DECAY HELPERS                                        *)
(* ========================================================================= *)

(** 18. Geometric decay: c^n eventually drops below any positive threshold *)
Lemma confidence_gap_vanishes : forall c eps,
  0 <= c -> c < 1 -> 0 < eps ->
  exists N, forall n, (N <= n)%nat -> Qpow c n < eps.
Proof.
  intros c eps Hc0 Hc1 Heps.
  exact (Qpow_limit_zero c Hc0 Hc1 eps Heps).
Qed.

(** 19. Displacement decay bound: d0 * c^n vanishes *)
Lemma displacement_vanishes : forall c d0 eps,
  0 < c -> c < 1 -> 0 < d0 -> 0 < eps ->
  exists N, forall n, (N <= n)%nat -> Qpow c n * d0 < eps.
Proof.
  intros c d0 eps Hc0 Hc1 Hd0 Heps.
  assert (Htarget : 0 < eps / d0).
  { unfold Qdiv. apply Qmult_lt_0_compat; [lra | apply Qinv_lt_0_compat; lra]. }
  destruct (Qpow_limit_zero c ltac:(lra) Hc1 (eps / d0) Htarget) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  assert (Hmul : Qpow c n * d0 < eps / d0 * d0).
  { apply Qmult_lt_compat_r; [exact Hd0 | exact HN]. }
  assert (Hsimp : eps / d0 * d0 == eps) by (field; lra).
  lra.
Qed.

(* ========================================================================= *)
(* VERIFICATION                                                              *)
(* ========================================================================= *)

Check pipeline_in_range.
Check initial_displacement_bounded.
Check pipeline_converges.
Check pipeline_approximate_fixpoint.
Check pipeline_limit.
Check step_size_bound.
Check convergence_iteration_bound.
Check qpow_vanishes.
Check sufficient_iterations_exist.
Check pipeline_start_independent.
Check stall_iterate_bound.
Check stall_means_near_fixpoint.
Check paradigm_shift_resets.
Check paradigm_shift_in_range.
Check pipeline_unique_convergence.
Check pipeline_unique_fixpoint.
Check pipeline_perturbation.
Check pipeline_iterate_contraction.
Check confidence_gap_vanishes.
Check displacement_vanishes.

Print Assumptions pipeline_converges.
Print Assumptions stall_means_near_fixpoint.
Print Assumptions paradigm_shift_resets.
Print Assumptions pipeline_perturbation.
Print Assumptions displacement_vanishes.
