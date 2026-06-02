(** * ProcessBestApproximation.v — The Fourier partial sum is the unique best
      L²-approximation (Part VII, Batch 1 / proposal A)

    Elements: coefficients aₖ, cₖ=⟨eₖ,f⟩; basis coords eₖ(m); finite sums
    Roles:    cₖ = projection coordinate; P_K = best approximation; Σ(aₖ−cₖ)² = penalty
    Rules:    residual ⟂ span(e₀…e_{K−1}); ‖f−Σaₖeₖ‖² = ‖f−P_K‖² + Σ_{k<K}(aₖ−cₖ)²;
              hence ≥ ‖f−P_K‖², with equality iff aₖ=cₖ (unique minimiser)

    Closes the §3.3 hedge of chapter 7.1: among ALL linear combinations Σ aₖ eₖ of a
    finite orthonormal system, the Fourier coefficients cₖ=⟨eₖ,f⟩ give the unique
    minimiser of the L²-error. Proved over ℚ from the residual-norm identity
    (ProcessL2BesselGeneral.resid_norm) and a bilinear expansion; uniqueness from
    "a finite sum of squares is zero iff every term is zero"
    (ProcessL2Parseval.q_sum_sq_zero). 0 axioms.

    GPT-split (review of the Part VII plan): A0 = residual orthogonal to the span +
    Pythagorean split (local, easy); A = best-approximation identity; uniqueness as a
    SEPARATE theorem via q_sum_sq_zero.

    HONEST FRONTIER: the INFINITE expansion / completed orthonormal basis remains a
    role-limit (Part VI / chapter 7.4 boundary); here everything is finite over ℚ.

    ============ E/R/R разбор ============
      Rules (L5): остаток ⟂ span; ‖f−Σaₖeₖ‖²=‖f−P_K‖²+Σ(aₖ−cₖ)²; минимум ⟺ aₖ=cₖ.
      Roles (L4): cₖ=⟨eₖ,f⟩ — координата; P_K — наилучшее приближение; Σ(aₖ−cₖ)² — штраф.
      Elements  : рациональные aₖ, cₖ, координаты eₖ(m), конечные суммы (L1+P4).
    ДИАГНОСТИКА: точное тождество над ℚ (0 акс); единственность — через «Σ квадратов=0 ⟹
    каждый=0»; бесконечное разложение / завершённый базис — роль-предел (граница).

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_ext, q_sum_zero *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)
From ToS Require Import process.ProcessL2BesselGeneral. (* seq_inner_sym, seq_inner_sub_r, inner_proj_swap, resid_norm, q_sum_ext_bounded *)
From ToS Require Import process.ProcessL2Parseval.      (* q_sum_sq_zero *)
From ToS Require Import process.ProcessPositionMomentum. (* q_sum_delta *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Bilinear expansion of a squared difference (no ON needed).            *)
(*    ‖g1 − g2‖² = ‖g1‖² − 2⟨g1,g2⟩ + ‖g2‖²                              *)
(* ===================================================================== *)

Lemma seq_inner_expand_diff : forall (g1 g2 : nat -> Q) (M : nat),
  seq_inner (fun m => g1 m - g2 m) (fun m => g1 m - g2 m) M
  == seq_inner g1 g1 M - 2 * seq_inner g1 g2 M + seq_inner g2 g2 M.
Proof.
  intros g1 g2 M.
  rewrite (seq_inner_sub_r (fun m => g1 m - g2 m) g1 g2 M).
  rewrite (seq_inner_sym (fun m => g1 m - g2 m) g1 M).
  rewrite (seq_inner_sub_r g1 g1 g2 M).
  rewrite (seq_inner_sym (fun m => g1 m - g2 m) g2 M).
  rewrite (seq_inner_sub_r g2 g1 g2 M).
  rewrite (seq_inner_sym g2 g1 M).
  ring.
Qed.

Section ON.

Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

(** General projection coordinate: ⟨e_j, Σ_{k<K} coefₖ eₖ⟩ = coef_j for j<K. *)
Lemma proj_coord : forall (coef : nat -> Q) (j K : nat), (j < K)%nat ->
  seq_inner (e j) (fun m => q_sum (fun k => coef k * e k m) K) N == coef j.
Proof.
  intros coef j K Hj.
  rewrite (inner_proj_swap e coef (e j) K N).
  transitivity (q_sum (fun k => (if (j =? k)%nat then 1 else 0) * coef k) K).
  { apply q_sum_ext. intro k. rewrite (Hon j k). ring. }
  rewrite (q_sum_delta 1 coef j K Hj). ring.
Qed.

(* ---------- A0: residual orthogonal to the span ---------- *)

(** ⟨e_j, f − P_K⟩ = 0 for every already-projected direction j<K. *)
Lemma resid_ortho : forall (j K : nat), (j < K)%nat ->
  seq_inner (e j) (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0.
Proof.
  intros j K Hj.
  rewrite (seq_inner_sub_r (e j) f
             (fun m => q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  rewrite (proj_coord (fun k => seq_inner (e k) f N) j K Hj).
  ring.
Qed.

(* ---------- ingredients of the general residual norm ---------- *)

(** ⟨f, Σ aₖ eₖ⟩ = Σ aₖ cₖ,  cₖ=⟨eₖ,f⟩. *)
Lemma inner_f_comb : forall (a : nat -> Q) (K : nat),
  seq_inner f (fun m => q_sum (fun k => a k * e k m) K) N
  == q_sum (fun k => a k * seq_inner (e k) f N) K.
Proof.
  intros a K.
  rewrite (inner_proj_swap e a f K N).
  apply q_sum_ext. intro k. rewrite (seq_inner_sym f (e k) N). reflexivity.
Qed.

(** ‖Σ aₖ eₖ‖² = Σ aₖ²  (orthonormality collapses the double sum). *)
Lemma norm_comb : forall (a : nat -> Q) (K : nat),
  seq_inner (fun m => q_sum (fun k => a k * e k m) K)
            (fun m => q_sum (fun k => a k * e k m) K) N
  == q_sum (fun k => a k * a k) K.
Proof.
  intros a K.
  rewrite (inner_proj_swap e a (fun m => q_sum (fun k => a k * e k m) K) K N).
  apply q_sum_ext_bounded. intros k Hk.
  rewrite (seq_inner_sym (fun m => q_sum (fun j => a j * e j m) K) (e k) N).
  rewrite (proj_coord a k K Hk). ring.
Qed.

(** General residual norm: ‖f − Σ aₖ eₖ‖² = ‖f‖² − 2 Σ aₖ cₖ + Σ aₖ². *)
Lemma gen_resid_norm : forall (a : nat -> Q) (K : nat),
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner f f N
     - 2 * q_sum (fun k => a k * seq_inner (e k) f N) K
     + q_sum (fun k => a k * a k) K.
Proof.
  intros a K.
  rewrite (seq_inner_expand_diff f (fun m => q_sum (fun k => a k * e k m) K) N).
  rewrite (inner_f_comb a K).
  rewrite (norm_comb a K).
  ring.
Qed.

(* ---------- A: best approximation ---------- *)

(** Best-approximation identity: the error of ANY coefficients a exceeds the error
    of the Fourier coefficients c by exactly Σ(aₖ−cₖ)². *)
Theorem best_approx_eq : forall (a : nat -> Q) (K : nat),
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
               (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
     + q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K.
Proof.
  intros a K.
  rewrite (gen_resid_norm a K).
  rewrite (resid_norm e N Hon f K).
  assert (Hdiff :
    q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K
    == q_sum (fun k => a k * a k) K
       - 2 * q_sum (fun k => a k * seq_inner (e k) f N) K
       + q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K).
  { exact (seq_inner_expand_diff a (fun k => seq_inner (e k) f N) K). }
  rewrite Hdiff. ring.
Qed.

(** Hence the Fourier partial sum is a minimiser: error(c) ≤ error(a). *)
Corollary best_approx_ge : forall (a : nat -> Q) (K : nat),
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof.
  intros a K.
  rewrite (best_approx_eq a K).
  assert (Hnn :
    0 <= q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K).
  { apply q_sum_nonneg. intro k. apply q_sq_nonneg. }
  lra.
Qed.

(** Uniqueness: the minimiser is attained EXACTLY at the Fourier coefficients. *)
Theorem best_approx_unique : forall (a : nat -> Q) (K : nat),
  (seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
             (fun m => f m - q_sum (fun k => a k * e k m) K) N
   == seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N)
  <-> (forall k, (k < K)%nat -> a k == seq_inner (e k) f N).
Proof.
  intros a K. split.
  - intro Heq.
    pose proof (best_approx_eq a K) as Hba.
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0)
      by lra.
    intros k Hk.
    pose proof (q_sum_sq_zero (fun k => a k - seq_inner (e k) f N) K Hz k Hk) as Hk0.
    cbn beta in Hk0. lra.
  - intro Hall.
    rewrite (best_approx_eq a K).
    assert (Hz :
      q_sum (fun k => (a k - seq_inner (e k) f N) * (a k - seq_inner (e k) f N)) K == 0).
    { transitivity (q_sum (fun _ : nat => 0) K).
      - apply q_sum_ext_bounded. intros k Hk. rewrite (Hall k Hk). ring.
      - apply q_sum_zero. }
    lra.
Qed.

End ON.

Print Assumptions best_approx_eq.
Print Assumptions best_approx_unique.
