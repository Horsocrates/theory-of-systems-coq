(** * ProcessL2Orthonormal.v -- Orthonormal systems with a satisfiable premise, Lagrange's identity, the Cauchy condition of the limit, as a ToS System

    Elements: vectors with N rational coordinates ([nat -> Q] read below N);
              finite sums [q_sum]; the coefficients <e_k, f>; the stages of a
              sequence of vectors [F n].
    Roles:    [seq_inner a b N]   -- the pairing (geometry);
              orthonormal system  -- the first K0 vectors of e are pairwise
                                     orthogonal and of norm 1 on N coordinates;
              projection / residual of f on the first K directions;
              [l2_limit F i]      -- the i-th coordinate of the limit: the
                                     process n |-> F n i;
              [dist_to_limit F N n] -- the squared distance from F n to the
                                     limit, a process in the stage of the limit.
    Rules:    residual identity for arbitrary coefficients; Bessel; best
              approximation; Parseval as a finite criterion of completeness;
              Lagrange's identity (the Cauchy-Schwarz gap is a sum of
              squares); a square-Cauchy sequence of rationals is Cauchy.

    Proved (no axioms):
      - [on_all_indices_unsat]: orthonormality "for all indices i, j" on N
        coordinates is impossible (at most N orthonormal vectors);
      - under orthonormality of the first K0 vectors, for K <= K0:
        [gen_resid], [resid_norm_b], [bessel_b], [best_approx_b],
        [energy_split_b], [parseval_iff_resid_zero_b],
        [parseval_iff_complete_b], [proj_ortho_b];
      - the premise is satisfiable: the standard basis ([std_basis_on],
        [bessel_std], [parseval_std_all]) and a rotated rational basis
        ([rot_orthonormal], [parseval_rot]);
      - [lagrange_identity], [cs_gap_is_sum_of_squares],
        [cauchy_schwarz_via_lagrange];
      - [l1_sq_le_N_l2_sq], [l2_polarization];
      - [resid_ortho_one], [best_approx_one];
      - [sq_cauchy_is_Cauchy], [l2_limit_coord_is_Cauchy],
        [riesz_fischer_process_form].

    P4 diagnostic: all sums are finite (N coordinates, K directions). The
      orthonormality premise is stated for the vectors that are actually
      used; a completed orthonormal basis and the sum over all coordinates
      are not elements. The limit of a Cauchy sequence is built coordinate
      by coordinate as a process; no choice is made.

    NOT claimed:
      - the infinite-dimensional l2 / L2 and a complete orthonormal basis;
      - a construction of orthonormal systems (Gram-Schmidt needs square
        roots, which are processes here);
      - the root metric d = sqrt(d^2);
      - Riesz-Fischer beyond a fixed truncation N.

    STATUS: 36 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa List.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessL2Triangle.
From ToS Require Import process.ProcessL2Bessel.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessL2RieszFischer.
From ToS Require Import process.ProcessDCT.

Open Scope Q_scope.

(* ===================================================================== *)
(*  0. Auxiliary facts                                                  *)
(* ===================================================================== *)

(** The m-th vector of the standard basis. *)
Definition delta (m : nat) : nat -> Q := fun i => if Nat.eqb i m then 1 else 0.

Lemma q_sum_zero_bounded : forall (g : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> g i == 0) -> q_sum g N == 0.
Proof.
  intros g N H. transitivity (q_sum (fun _ : nat => 0) N).
  - apply q_sum_ext_bounded. exact H.
  - apply q_sum_zero.
Qed.

Lemma q_sum_le_bounded : forall (g h : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> g i <= h i) -> q_sum g N <= q_sum h N.
Proof.
  intros g h N. induction N as [|k IH]; intro H; cbn [q_sum].
  - lra.
  - assert (H1 : q_sum g k <= q_sum h k) by (apply IH; intros i Hi; apply H; lia).
    assert (H2 : g k <= h k) by (apply H; lia).
    lra.
Qed.

(** <a, delta_m> = a_m for m < N. *)
Lemma seq_inner_delta : forall (a : nat -> Q) (N m : nat),
  (m < N)%nat -> seq_inner a (delta m) N == a m.
Proof.
  intros a N m. unfold seq_inner, delta. induction N as [|k IH]; intro Hm.
  - lia.
  - cbn [q_sum]. destruct (Nat.eqb k m) eqn:E.
    + apply Nat.eqb_eq in E. subst k.
      rewrite (q_sum_zero_bounded (fun i => a i * (if Nat.eqb i m then 1 else 0)) m).
      * ring.
      * intros i Hi.
        assert (Hne : Nat.eqb i m = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne. ring.
    + apply Nat.eqb_neq in E. rewrite IH by lia. ring.
Qed.

Lemma seq_inner_scale_r : forall (h g : nat -> Q) (c : Q) (N : nat),
  seq_inner h (fun m => c * g m) N == c * seq_inner h g N.
Proof.
  intros h g c N. unfold seq_inner.
  transitivity (q_sum (fun i => c * (h i * g i)) N).
  - apply q_sum_ext. intro i. ring.
  - apply q_sum_scale.
Qed.

Lemma seq_inner_self_zero_of_coords : forall (g : nat -> Q) (N : nat),
  (forall i, (i < N)%nat -> g i == 0) -> seq_inner g g N == 0.
Proof.
  intros g N H. unfold seq_inner. apply q_sum_zero_bounded.
  intros i Hi. rewrite (H i Hi). ring.
Qed.

(* ===================================================================== *)
(*  1. Orthonormality "for all indices" is unsatisfiable                *)
(* ===================================================================== *)

(** The premise of ProcessL2BesselGeneral.v and ProcessL2Parseval.v --
    <e_i, e_j> = [i = j] for ALL natural i, j on N coordinates -- holds for
    no family e and no N: there are at most N orthonormal vectors with N
    coordinates. *)
Theorem on_all_indices_unsat : forall (e : nat -> nat -> Q) (N : nat),
  ~ (forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0)).
Proof.
  intros e N Hon.
  assert (Hb : forall m, (m < N)%nat ->
            q_sum (fun k => e k m * e k m) (S N) <= 1).
  { intros m Hm.
    pose proof (bessel_general e N Hon (delta m) (S N)) as H.
    assert (E1 : q_sum (fun k => seq_inner (e k) (delta m) N
                                 * seq_inner (e k) (delta m) N) (S N)
                 == q_sum (fun k => e k m * e k m) (S N)).
    { apply q_sum_ext. intro k. rewrite (seq_inner_delta (e k) N m Hm). reflexivity. }
    assert (E2 : seq_inner (delta m) (delta m) N == 1).
    { rewrite (seq_inner_delta (delta m) N m Hm). unfold delta.
      rewrite Nat.eqb_refl. reflexivity. }
    rewrite E1, E2 in H. exact H. }
  assert (Hsum : q_sum (fun m => q_sum (fun k => e k m * e k m) (S N)) N
                 <= q_sum (fun _ : nat => 1) N).
  { apply q_sum_le_bounded. exact Hb. }
  assert (Hswap : q_sum (fun m => q_sum (fun k => e k m * e k m) (S N)) N
                  == q_sum (fun k => q_sum (fun m => e k m * e k m) N) (S N)).
  { exact (q_sum_swap (fun m k => e k m * e k m) N (S N)). }
  assert (Hone : q_sum (fun k => q_sum (fun m => e k m * e k m) N) (S N)
                 == q_sum (fun _ : nat => 1) (S N)).
  { apply q_sum_ext. intro k. pose proof (Hon k k) as Hk.
    rewrite Nat.eqb_refl in Hk. unfold seq_inner in Hk. exact Hk. }
  assert (Hs : q_sum (fun _ : nat => 1) (S N) == q_sum (fun _ : nat => 1) N + 1)
    by (cbn [q_sum]; reflexivity).
  rewrite Hswap, Hone, Hs in Hsum. lra.
Qed.

(** The standard basis does not satisfy it: already <e_N, e_N>_N = 0. *)
Lemma std_basis_fails_all_indices : forall N : nat,
  seq_inner (delta N) (delta N) N == 0.
Proof.
  intro N. apply seq_inner_self_zero_of_coords. intros i Hi. unfold delta.
  assert (Hne : Nat.eqb i N = false) by (apply Nat.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

(* ===================================================================== *)
(*  2. The same theorems under a satisfiable premise                    *)
(* ===================================================================== *)

Lemma q_sum_neg_sq : forall (c : nat -> Q) (K : nat),
  q_sum (fun k => c k * c k - 2 * c k * c k) K == - q_sum (fun k => c k * c k) K.
Proof.
  intros c K. induction K as [|K IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

Section ONB.

(** The first K0 vectors of e are orthonormal on N coordinates. *)
Variable e : nat -> nat -> Q.
Variable N K0 : nat.
Hypothesis Hon : forall i j, (i < K0)%nat -> (j < K0)%nat ->
  seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).

(** The vector number K is orthogonal to the combinations of the first K. *)
Lemma proj_ortho_b : forall (coef : nat -> Q) (K : nat), (K < K0)%nat ->
  seq_inner (e K) (fun m => q_sum (fun k => coef k * e k m) K) N == 0.
Proof.
  intros coef K HK.
  rewrite (inner_proj_swap e coef (e K) K N).
  apply q_sum_zero_bounded. intros k Hk.
  rewrite (Hon K k HK ltac:(lia)).
  assert (Hneq : Nat.eqb K k = false) by (apply Nat.eqb_neq; lia).
  rewrite Hneq. ring.
Qed.

Variable f : nat -> Q.

(** General residual identity for ARBITRARY coefficients a:
    ||f - Sum_{k<K} a_k e_k||^2 = ||f||^2 + Sum_{k<K} (a_k^2 - 2 a_k <e_k,f>). *)
Lemma gen_resid : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
            (fun m => f m - q_sum (fun k => a k * e k m) K) N
  == seq_inner f f N + q_sum (fun k => a k * a k - 2 * a k * seq_inner (e k) f N) K.
Proof.
  intros a K. induction K as [|K IH]; intro HK.
  - transitivity (seq_inner f f N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + cbn [q_sum]; ring.
  - transitivity
      (seq_inner (fun m => (f m - q_sum (fun k => a k * e k m) K) - a K * e K m)
                 (fun m => (f m - q_sum (fun k => a k * e k m) K) - a K * e K m) N).
    + apply seq_inner_ext; intro m; cbn [q_sum]; ring.
    + rewrite (seq_inner_resid
                 (fun m => f m - q_sum (fun k => a k * e k m) K) (e K) (a K) N).
      rewrite (IH ltac:(lia)).
      rewrite (seq_inner_sub_r (e K) f (fun m => q_sum (fun k => a k * e k m) K) N).
      rewrite (proj_ortho_b a K ltac:(lia)).
      rewrite (Hon K K ltac:(lia) ltac:(lia)), Nat.eqb_refl.
      cbn [q_sum]. ring.
Qed.

(** The residual identity (a_k = <e_k, f>). *)
Lemma resid_norm_b : forall K, (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner f f N - q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K.
Proof.
  intros K HK.
  pose proof (gen_resid (fun k => seq_inner (e k) f N) K HK) as H. cbv beta in H.
  pose proof (q_sum_neg_sq (fun k => seq_inner (e k) f N) K) as H2. cbv beta in H2.
  rewrite H, H2. ring.
Qed.

(** Bessel's inequality for K <= K0 orthonormal vectors. *)
Theorem bessel_b : forall K, (K <= K0)%nat ->
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K <= seq_inner f f N.
Proof.
  intros K HK. pose proof (resid_norm_b K HK) as Hrn.
  assert (Hnn : 0 <= seq_inner
                       (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                       (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N).
  { unfold seq_inner. apply q_sum_nonneg. intro i. apply q_sq_nonneg. }
  rewrite Hrn in Hnn. lra.
Qed.

(** Best approximation: the projection with the coefficients <e_k, f> has
    the least residual among all combinations Sum_{k<K} a_k e_k. *)
Theorem best_approx_b : forall (a : nat -> Q) (K : nat), (K <= K0)%nat ->
  seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
            (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  <= seq_inner (fun m => f m - q_sum (fun k => a k * e k m) K)
               (fun m => f m - q_sum (fun k => a k * e k m) K) N.
Proof.
  intros a K HK.
  pose proof (gen_resid a K HK) as Ha.
  pose proof (gen_resid (fun k => seq_inner (e k) f N) K HK) as Hc. cbv beta in Hc.
  rewrite Ha, Hc.
  assert (Hle : q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N
                               - 2 * seq_inner (e k) f N * seq_inner (e k) f N) K
                <= q_sum (fun k => a k * a k - 2 * a k * seq_inner (e k) f N) K).
  { apply q_sum_le. intro k. set (c := seq_inner (e k) f N).
    assert (Hsq : 0 <= (a k - c) * (a k - c)) by apply q_sq_nonneg.
    nra. }
  lra.
Qed.

(** Energy split: Sum c_k^2 + ||r_K||^2 = ||f||^2. *)
Lemma energy_split_b : forall K, (K <= K0)%nat ->
  q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K
  + seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
              (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N
  == seq_inner f f N.
Proof.
  intros K HK. rewrite (resid_norm_b K HK). ring.
Qed.

(** Parseval's equality holds exactly when the residual vanishes. *)
Lemma parseval_iff_resid_zero_b : forall K, (K <= K0)%nat ->
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K == seq_inner f f N)
  <-> (seq_inner (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                 (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0).
Proof.
  intros K HK. pose proof (resid_norm_b K HK) as Hrn. split; intro H; lra.
Qed.

(** Parseval as a finite criterion of completeness: the equality holds
    exactly when the expansion restores every coordinate m < N. *)
Theorem parseval_iff_complete_b : forall K, (K <= K0)%nat ->
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K == seq_inner f f N)
  <-> (forall m, (m < N)%nat ->
         q_sum (fun k => seq_inner (e k) f N * e k m) K == f m).
Proof.
  intros K HK. pose proof (resid_norm_b K HK) as Hrn. split.
  - intros Hp m Hm.
    assert (Hz : seq_inner
                   (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                   (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0)
      by lra.
    pose proof (q_sum_sq_zero
                  (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                  N Hz m Hm) as Hgm.
    cbv beta in Hgm. lra.
  - intros Hc.
    assert (Hz : seq_inner
                   (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K)
                   (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K) N == 0).
    { apply seq_inner_self_zero_of_coords. intros i Hi. cbv beta.
      rewrite (Hc i Hi). ring. }
    lra.
Qed.

End ONB.

(** The premise is satisfiable: the standard basis, K0 = N. *)
Lemma std_basis_on : forall (N i j : nat), (i < N)%nat -> (j < N)%nat ->
  seq_inner (delta i) (delta j) N == (if Nat.eqb i j then 1 else 0).
Proof.
  intros N i j Hi Hj. rewrite (seq_inner_delta (delta i) N j Hj). unfold delta.
  rewrite Nat.eqb_sym. reflexivity.
Qed.

Theorem bessel_std : forall (f : nat -> Q) (N K : nat), (K <= N)%nat ->
  q_sum (fun k => seq_inner (delta k) f N * seq_inner (delta k) f N) K <= seq_inner f f N.
Proof.
  intros f N K HK. exact (bessel_b delta N N (std_basis_on N) f K HK).
Qed.

(** Parseval's equality is attained on the standard basis for every N and f. *)
Theorem parseval_std_all : forall (f : nat -> Q) (N : nat),
  q_sum (fun k => seq_inner (delta k) f N * seq_inner (delta k) f N) N == seq_inner f f N.
Proof.
  intros f N.
  apply (proj2 (parseval_iff_complete_b delta N N (std_basis_on N) f N (le_n N))).
  intros m Hm.
  transitivity (q_sum (fun k => f k * delta m k) N).
  - apply q_sum_ext_bounded. intros k Hk.
    rewrite (seq_inner_sym (delta k) f N), (seq_inner_delta f N k Hk).
    unfold delta. rewrite (Nat.eqb_sym m k). reflexivity.
  - exact (seq_inner_delta f N m Hm).
Qed.

(** A second example: the basis (3/5, 4/5), (-4/5, 3/5) -- a rational
    rotation of the standard basis of two coordinates. *)
Definition rot (k m : nat) : Q :=
  match k, m with
  | O, O => 3 # 5
  | O, S O => 4 # 5
  | S O, O => - (4 # 5)
  | S O, S O => 3 # 5
  | _, _ => 0
  end.

Example rot_orthonormal : forall i j, (i < 2)%nat -> (j < 2)%nat ->
  seq_inner (rot i) (rot j) 2%nat == (if Nat.eqb i j then 1 else 0).
Proof.
  intros i j Hi Hj.
  assert (Ei : i = 0%nat \/ i = 1%nat) by lia.
  assert (Ej : j = 0%nat \/ j = 1%nat) by lia.
  destruct Ei as [-> | ->]; destruct Ej as [-> | ->]; vm_compute; reflexivity.
Qed.

Example bessel_rot : forall (f : nat -> Q) (K : nat), (K <= 2)%nat ->
  q_sum (fun k => seq_inner (rot k) f 2%nat * seq_inner (rot k) f 2%nat) K
  <= seq_inner f f 2%nat.
Proof.
  intros f K HK. exact (bessel_b rot 2%nat 2%nat rot_orthonormal f K HK).
Qed.

Example parseval_rot : forall f : nat -> Q,
  q_sum (fun k => seq_inner (rot k) f 2%nat * seq_inner (rot k) f 2%nat) 2%nat
  == seq_inner f f 2%nat.
Proof.
  intro f. unfold seq_inner. cbn [q_sum rot]. ring.
Qed.

(* ===================================================================== *)
(*  3. Lagrange's identity                                              *)
(* ===================================================================== *)

Lemma q_sum_lin3 : forall (a b : nat -> Q) (A B C : Q) (M : nat),
  q_sum (fun j => b j * b j * A - 2 * a j * b j * C + a j * a j * B) M
  == q_sum (fun i => b i * b i) M * A - 2 * q_sum (fun i => a i * b i) M * C
     + q_sum (fun i => a i * a i) M * B.
Proof.
  intros a b A B C M. induction M as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

(** Sum_{i,j} (a_i b_j - a_j b_i)^2 = 2 (||a||^2 ||b||^2 - <a,b>^2). *)
Theorem lagrange_identity : forall (a b : nat -> Q) (N : nat),
  q_sum (fun j => q_sum (fun i => (a i * b j - a j * b i) * (a i * b j - a j * b i)) N) N
  == 2 * (q_sum (fun i => a i * a i) N * q_sum (fun i => b i * b i) N
          - q_sum (fun i => a i * b i) N * q_sum (fun i => a i * b i) N).
Proof.
  intros a b N.
  transitivity (q_sum (fun j => b j * b j * q_sum (fun i => a i * a i) N
                               - 2 * a j * b j * q_sum (fun i => a i * b i) N
                               + a j * a j * q_sum (fun i => b i * b i) N) N).
  - apply q_sum_ext. intro j. apply (sos_identity a b (a j) (b j) N).
  - rewrite q_sum_lin3. ring.
Qed.

(** The Cauchy-Schwarz gap is half a sum of squares:
    ||a||^2 ||b||^2 - <a,b>^2 = 1/2 Sum_{i,j} (a_i b_j - a_j b_i)^2. *)
Corollary cs_gap_is_sum_of_squares : forall (a b : nat -> Q) (N : nat),
  q_sum (fun i => a i * a i) N * q_sum (fun i => b i * b i) N
  - q_sum (fun i => a i * b i) N * q_sum (fun i => a i * b i) N
  == (1 # 2) * q_sum (fun j => q_sum (fun i => (a i * b j - a j * b i)
                                              * (a i * b j - a j * b i)) N) N.
Proof.
  intros a b N. rewrite lagrange_identity. ring.
Qed.

(** Cauchy-Schwarz through Lagrange's identity: the gap is a sum of squares. *)
Corollary cauchy_schwarz_via_lagrange : forall (a b : nat -> Q) (N : nat),
  q_sum (fun i => a i * b i) N * q_sum (fun i => a i * b i) N
  <= q_sum (fun i => a i * a i) N * q_sum (fun i => b i * b i) N.
Proof.
  intros a b N.
  pose proof (cs_gap_is_sum_of_squares a b N) as Hgap.
  assert (Hnn : 0 <= q_sum (fun j => q_sum (fun i => (a i * b j - a j * b i)
                                                    * (a i * b j - a j * b i)) N) N).
  { apply q_sum_nonneg. intro j. apply q_sum_nonneg. intro i. apply q_sq_nonneg. }
  set (S := q_sum (fun j => q_sum (fun i => (a i * b j - a j * b i)
                                            * (a i * b j - a j * b i)) N) N) in *.
  lra.
Qed.

(* ===================================================================== *)
(*  4. L1 and L2 on N points; polarization                              *)
(* ===================================================================== *)

Lemma q_sum_ones : forall N : nat, q_sum (fun _ : nat => 1) N == inject_Z (Z.of_nat N).
Proof.
  induction N as [|k IH]; cbn [q_sum].
  - reflexivity.
  - rewrite IH. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity.
Qed.

(** (Sum |f_i|)^2 <= N * Sum f_i^2: Cauchy-Schwarz with the second argument 1. *)
Theorem l1_sq_le_N_l2_sq : forall (f : nat -> Q) (N : nat),
  q_sum (fun i => Qabs (f i)) N * q_sum (fun i => Qabs (f i)) N
  <= q_sum (fun i => f i * f i) N * inject_Z (Z.of_nat N).
Proof.
  intros f N.
  pose proof (q_sum_cauchy_schwarz (fun i => Qabs (f i)) (fun _ => 1) N) as H.
  cbv beta in H.
  assert (E1 : q_sum (fun i => Qabs (f i) * 1) N == q_sum (fun i => Qabs (f i)) N)
    by (apply q_sum_ext; intro i; ring).
  assert (E2 : q_sum (fun i => Qabs (f i) * Qabs (f i)) N == q_sum (fun i => f i * f i) N).
  { apply q_sum_ext. intro i. rewrite <- Qabs_Qmult. apply Qabs_pos. apply q_sq_nonneg. }
  assert (E3 : q_sum (fun _ : nat => 1 * 1) N == inject_Z (Z.of_nat N)).
  { rewrite <- q_sum_ones. apply q_sum_ext. intro i. ring. }
  rewrite E1, E2, E3 in H. exact H.
Qed.

(** Polarization: the pairing is recovered from the norms. *)
Theorem l2_polarization : forall f g pts w N,
  l2_inner f g pts w N
  == (1 # 2) * (l2_inner (fun x => f x + g x) (fun x => f x + g x) pts w N
                - l2_inner f f pts w N - l2_inner g g pts w N).
Proof.
  intros f g pts w N. rewrite l2_inner_expand. ring.
Qed.

(* ===================================================================== *)
(*  5. One direction: the residual is orthogonal; best approximation    *)
(* ===================================================================== *)

Theorem resid_ortho_one : forall (e f : nat -> Q) (N : nat),
  seq_inner e e N == 1 ->
  seq_inner e (fun m => f m - seq_inner e f N * e m) N == 0.
Proof.
  intros e f N Hu.
  rewrite (seq_inner_sub_r e f (fun m => seq_inner e f N * e m) N).
  rewrite (seq_inner_scale_r e e (seq_inner e f N) N).
  rewrite Hu. ring.
Qed.

Theorem best_approx_one : forall (e f : nat -> Q) (c : Q) (N : nat),
  seq_inner e e N == 1 ->
  seq_inner (fun m => f m - seq_inner e f N * e m)
            (fun m => f m - seq_inner e f N * e m) N
  <= seq_inner (fun m => f m - c * e m) (fun m => f m - c * e m) N.
Proof.
  intros e f c N Hu.
  rewrite (seq_inner_resid f e (seq_inner e f N) N).
  rewrite (seq_inner_resid f e c N). rewrite Hu.
  set (p := seq_inner e f N).
  assert (Hsq : 0 <= (c - p) * (c - p)) by apply q_sq_nonneg.
  nra.
Qed.

(* ===================================================================== *)
(*  6. Riesz-Fischer at a fixed truncation, in process form             *)
(* ===================================================================== *)

(** The square form of the Cauchy condition gives [is_Cauchy]. *)
Lemma sq_cauchy_is_Cauchy : forall (x : nat -> Q),
  (forall eps, eps > 0 -> exists M, forall m n, (M <= m)%nat -> (M <= n)%nat ->
      (x m - x n) * (x m - x n) <= eps) ->
  is_Cauchy x.
Proof.
  intros x H eps Heps.
  set (h := (1 # 2) * eps).
  assert (Hh : 0 < h) by (unfold h; lra).
  assert (Hhh : h * h > 0) by (apply Qmult_lt_0_compat; exact Hh).
  destruct (H (h * h) Hhh) as [M HM].
  exists M. intros m n Hm Hn. specialize (HM m n Hm Hn).
  set (d := x m - x n) in *.
  destruct (Qlt_le_dec (Qabs d) eps) as [Hlt | Hge]; [ exact Hlt | exfalso ].
  assert (Habs : Qabs d * Qabs d == d * d).
  { rewrite <- Qabs_Qmult. apply Qabs_pos. apply q_sq_nonneg. }
  assert (Hd0 : 0 <= Qabs d) by apply Qabs_nonneg.
  assert (H1 : eps * eps <= Qabs d * Qabs d) by nra.
  assert (H2 : h * h == (1 # 4) * (eps * eps)) by (unfold h; ring).
  assert (H3 : 0 < eps * eps) by (apply Qmult_lt_0_compat; exact Heps).
  rewrite Habs in H1. rewrite H2 in HM. lra.
Qed.

(** Every coordinate of the limit built in ProcessL2RieszFischer.v is a
    Cauchy process. *)
Theorem l2_limit_coord_is_Cauchy : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N -> forall i, (i < N)%nat -> is_Cauchy (l2_limit F i).
Proof.
  intros F N HC i Hi. apply sq_cauchy_is_Cauchy.
  exact (l2_limit_is_cauchy_real F N HC i Hi).
Qed.

Lemma q_sum_split3 : forall (x y z : nat -> Q) (N : nat),
  q_sum (fun i => (x i - z i) * (x i - z i)) N
  == q_sum (fun i => (x i - y i) * (x i - y i)) N
     + 2 * q_sum (fun i => (x i - y i) * (y i - z i)) N
     + q_sum (fun i => (y i - z i) * (y i - z i)) N.
Proof.
  intros x y z N. induction N as [|k IH]; cbn [q_sum]; [ ring | rewrite IH; ring ].
Qed.

(** The squared distance from F n to the stage s of the limit. *)
Definition dist_to_limit (F : nat -> nat -> Q) (N n : nat) : nat -> Q :=
  fun s => seq_inner (fun i => F n i - l2_limit F i s)
                     (fun i => F n i - l2_limit F i s) N.

Lemma dist_to_limit_sq_cauchy : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N -> forall n : nat,
  forall eps, eps > 0 -> exists M, forall s t, (M <= s)%nat -> (M <= t)%nat ->
    (dist_to_limit F N n s - dist_to_limit F N n t)
    * (dist_to_limit F N n s - dist_to_limit F N n t) <= eps.
Proof.
  intros F N HC n eps Heps. unfold dist_to_limit, l2_limit, seq_inner.
  destruct (HC 1 ltac:(reflexivity)) as [M1 HM1].
  set (A := q_sum (fun i => (F n i - F M1 i) * (F n i - F M1 i)) N).
  assert (HA : 0 <= A) by (unfold A; apply q_sum_nonneg; intro i; apply q_sq_nonneg).
  set (B := 2 * A + 2).
  assert (HB : 0 <= B) by (unfold B; lra).
  set (c := 8 * B + 2 + eps).
  assert (Hc : 0 < c) by (unfold c; lra).
  set (dl := eps * / c).
  assert (Hdc : dl * c == eps) by (unfold dl; field; lra).
  assert (Hdl : 0 < dl).
  { unfold dl. apply Qmult_lt_0_compat; [ exact Heps | apply Qinv_lt_0_compat; exact Hc ]. }
  assert (Hdl1 : dl <= 1).
  { destruct (Qlt_le_dec 1 dl) as [Hgt | Hle]; [ exfalso | exact Hle ].
    assert (Hx : 1 * c < dl * c) by (apply Qmult_lt_compat_r; assumption).
    unfold c in Hx, Hdc. lra. }
  destruct (HC dl Hdl) as [M2 HM2].
  exists (Nat.max M1 M2). intros s t Hs Ht.
  set (Ds := q_sum (fun i => (F n i - F s i) * (F n i - F s i)) N).
  set (Dt := q_sum (fun i => (F n i - F t i) * (F n i - F t i)) N).
  pose (P := q_sum (fun i => (F n i - F t i) * (F t i - F s i)) N).
  pose (W := q_sum (fun i => (F t i - F s i) * (F t i - F s i)) N).
  assert (Hsplit : Ds == Dt + 2 * P + W)
    by (unfold Ds, Dt, P, W; apply (q_sum_split3 (F n) (F t) (F s) N)).
  assert (Hcs : P * P <= Dt * W)
    by (unfold P, Dt, W;
        apply (q_sum_cauchy_schwarz (fun i => F n i - F t i) (fun i => F t i - F s i) N)).
  assert (HW0 : 0 <= W) by (unfold W; apply q_sum_nonneg; intro i; apply q_sq_nonneg).
  assert (HDt0 : 0 <= Dt) by (unfold Dt; apply q_sum_nonneg; intro i; apply q_sq_nonneg).
  assert (HW : W <= dl).
  { pose proof (HM2 t s ltac:(lia) ltac:(lia)) as H. unfold seq_inner in H. exact H. }
  assert (HDt : Dt <= B).
  { pose proof (l2_dist_sq_triangle (F n) (F M1) (F t) N) as Htri.
    unfold l2_dist_sq in Htri.
    pose proof (HM1 M1 t ltac:(lia) ltac:(lia)) as H1. unfold seq_inner in H1.
    unfold Dt, B, A. lra. }
  assert (E : (Ds - Dt) * (Ds - Dt) == 4 * (P * P) + 4 * (P * W) + W * W)
    by (rewrite Hsplit; ring).
  assert (Hq : 0 <= (2 * P - W) * (2 * P - W)) by apply q_sq_nonneg.
  assert (Hq' : (2 * P - W) * (2 * P - W) == 4 * (P * P) - 4 * (P * W) + W * W) by ring.
  rewrite Hq' in Hq.
  assert (H1 : Dt * W <= B * dl).
  { apply Qle_trans with (B * W).
    - apply Qmult_le_compat_r; assumption.
    - rewrite (Qmult_comm B W), (Qmult_comm B dl). apply Qmult_le_compat_r; assumption. }
  assert (H2 : W * W <= dl).
  { apply Qle_trans with (dl * W).
    - apply Qmult_le_compat_r; assumption.
    - apply Qle_trans with (dl * 1).
      + rewrite (Qmult_comm dl W), (Qmult_comm dl 1).
        apply Qmult_le_compat_r; [ lra | lra ].
      + lra. }
  assert (H3 : 8 * (B * dl) + 2 * dl + dl * eps == eps)
    by (rewrite <- Hdc at 2; unfold c; ring).
  assert (H4 : 0 <= dl * eps) by (apply Qmult_le_0_compat; lra).
  rewrite E. lra.
Qed.

(** Riesz-Fischer at a fixed N in three parts: (1) the coordinates of the
    limit are Cauchy processes; (2) the distance from F n to the limit is
    a Cauchy process; (3) this distance tends to zero. *)
Theorem riesz_fischer_process_form : forall (F : nat -> nat -> Q) (N : nat),
  L2CauchySq F N ->
  (forall i, (i < N)%nat -> is_Cauchy (l2_limit F i))
  /\ (forall n, is_Cauchy (dist_to_limit F N n))
  /\ (forall eps, eps > 0 -> exists M, forall n, (M <= n)%nat ->
        exists S, forall s, (S <= s)%nat -> dist_to_limit F N n s <= eps).
Proof.
  intros F N HC. split; [ | split ].
  - intros i Hi. exact (l2_limit_coord_is_Cauchy F N HC i Hi).
  - intro n. apply sq_cauchy_is_Cauchy. exact (dist_to_limit_sq_cauchy F N HC n).
  - intros eps Heps. destruct (l2_riesz_fischer F N HC eps Heps) as [M HM].
    exists M. intros n Hn. exists M. intros s Hs. unfold dist_to_limit.
    exact (HM n s Hn Hs).
Qed.

