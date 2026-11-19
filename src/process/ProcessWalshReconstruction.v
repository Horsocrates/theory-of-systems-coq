(** * ProcessWalshReconstruction.v -- Compression by the first K Walsh coefficients: the reconstructed signal and its error, as a ToS System

    Elements: a signal f on N = 2^k coordinates (rational values); its raw
              Walsh spectrum Hf (finite rational sums); the number K of
              coefficients kept; finite sums.
    Roles:    [spec_trunc c K]  -- the spectrum cut to its first K entries;
              [walsh_rec k K f] -- the signal rebuilt from the first K raw
                                   coefficients: f_K = (1/N) H (cut spectrum);
              the squared error ||f - f_K||^2 on N coordinates;
              [captured]        -- the energy captured by the first K
                                   coefficients (ProcessFourierCompression.v).
    Rules:    H(Hf) = N f and Plancherel ||Hd||^2 = N ||d||^2 give
              N * ||f - f_K||^2 = Sum_{K <= i < N} (Hf)_i^2; hence the error
              does not grow with K and vanishes exactly when the dropped
              coefficients vanish.

    Proved (no axioms):
      - [walsh_rec_partial_sum]: f_K is the K-term partial sum of the Walsh
        expansion;
      - [walsh_compression_error]: N * ||f - f_K||^2 is the sum of squares of
        the dropped coefficients; [walsh_tail_eq]: that sum equals
        N * ||f||^2 minus the captured energy (an equality, by Plancherel);
        [walsh_compression_error_energy]; [walsh_compression_error_mono];
      - [walsh_bandlimited_lossless]: if the coefficients from K on vanish,
        f_K = f on all N coordinates; [walsh_lossless_iff]: and only then;
      - the normalised scale, when a rational s with s^2 = N exists:
        [walsh_normalized_error_is_tail], [walsh_4j_error_is_tail];
      - [walsh_convolution_inverse], [convolution_via_fwht]: the dyadic
        convolution is recovered as (1/N) H ((Hf) . (Hg)), also through the
        fast transform.

    P4 diagnostic: every object is a finite rational sum on N = 2^k
      coordinates. The raw scale needs no square root: the factor N is kept
      on the left-hand side. The normalised scale is stated only under the
      premise s^2 = N for a rational s, satisfiable exactly for even k.

    NOT claimed:
      - the best K-term compression (the K largest coefficients): it needs a
        layer of comparison and sorting;
      - compression for systems other than Walsh; continuous or complex
        convolution;
      - any statement about the cost of the algorithms.

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessSelfAdjointSpectral.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessL2Parseval.
From ToS Require Import process.ProcessWalshHadamard.
From ToS Require Import process.ProcessWalshCharacter.
From ToS Require Import process.ProcessFourierON.
From ToS Require Import process.ProcessFourierCompression.
From ToS Require Import process.ProcessWalshCompaction.
From ToS Require Import process.ProcessFastWalsh.
From ToS Require Import process.ProcessWalshConvolution.
From ToS Require Import process.ProcessWalshConvolutionGeneral.
From ToS Require process.ProcessL2Orthonormal.
From ToS Require Import process.ProcessOrthonormalFourier.
From ToS Require Import process.ProcessOrthogonalWalsh.

Open Scope Q_scope.

(** N = 2^k as a rational number. *)
Local Notation Nq k := (inject_Z (Z.of_nat (pow2 k))).

(* ===================================================================== *)
(*  1. Auxiliary: dependence on the first N values only                 *)
(* ===================================================================== *)

Lemma op_apply_ext_bounded : forall (T : nat -> nat -> Q) (v w : nat -> Q) (N i : nat),
  (forall j, (j < N)%nat -> v j == w j) -> op_apply T v N i == op_apply T w N i.
Proof.
  intros T v w N i H. unfold op_apply. apply q_sum_ext_bounded.
  intros j Hj. rewrite (H j Hj). reflexivity.
Qed.

Lemma op_apply_sub : forall (T : nat -> nat -> Q) (v w : nat -> Q) (N i : nat),
  op_apply T (fun j => v j - w j) N i == op_apply T v N i - op_apply T w N i.
Proof.
  intros T v w N i. unfold op_apply.
  transitivity (q_sum (fun j => T i j * v j + (- (1)) * (T i j * w j)) N).
  - apply q_sum_ext. intro j. ring.
  - rewrite (q_sum_plus (fun j => T i j * v j) (fun j => (- (1)) * (T i j * w j)) N).
    rewrite (q_sum_scale (- (1)) (fun j => T i j * w j) N). ring.
Qed.

Lemma seq_inner_ext_bounded : forall (a a' b b' : nat -> Q) (N : nat),
  (forall m, (m < N)%nat -> a m == a' m) -> (forall m, (m < N)%nat -> b m == b' m) ->
  seq_inner a b N == seq_inner a' b' N.
Proof.
  intros a a' b b' N Ha Hb. unfold seq_inner. apply q_sum_ext_bounded.
  intros m Hm. rewrite (Ha m Hm), (Hb m Hm). reflexivity.
Qed.

(* ===================================================================== *)
(*  2. The signal rebuilt from the first K coefficients                 *)
(* ===================================================================== *)

(** The spectrum cut to its first K coefficients. *)
Definition spec_trunc (c : nat -> Q) (K : nat) : nat -> Q :=
  fun i => if Nat.ltb i K then c i else 0.

(** The signal rebuilt from the first K raw Walsh coefficients:
    f_K = (1/N) H (cut spectrum). *)
Definition walsh_rec (k K : nat) (f : nat -> Q) : nat -> Q :=
  fun m => op_apply (had k) (spec_trunc (op_apply (had k) f (pow2 k)) K) (pow2 k) m / Nq k.

(** The same as the K-term partial sum of the Walsh expansion:
    f_K(m) = (1/N) Sum_{i<K} (Hf)_i w_i(m). *)
Lemma walsh_rec_partial_sum : forall k f K m, (K <= pow2 k)%nat ->
  walsh_rec k K f m
  == q_sum (fun i => op_apply (had k) f (pow2 k) i * had k i m) K / Nq k.
Proof.
  intros k f K m HK. unfold walsh_rec.
  apply Qmult_comp; [ | reflexivity ].
  change (op_apply (had k) (spec_trunc (op_apply (had k) f (pow2 k)) K) (pow2 k) m)
    with (q_sum (fun j => had k m j * spec_trunc (op_apply (had k) f (pow2 k)) K j) (pow2 k)).
  transitivity (q_sum (fun j => had k m j * spec_trunc (op_apply (had k) f (pow2 k)) K j)
                      (K + (pow2 k - K))).
  { replace (K + (pow2 k - K))%nat with (pow2 k) by lia. reflexivity. }
  rewrite q_sum_split. cbn beta.
  assert (H2 : q_sum (fun i => had k m (K + i)%nat
                               * spec_trunc (op_apply (had k) f (pow2 k)) K (K + i)%nat)
                     (pow2 k - K) == 0).
  { transitivity (q_sum (fun _ : nat => 0) (pow2 k - K)%nat).
    - apply q_sum_ext. intro i. unfold spec_trunc.
      assert (E : Nat.ltb (K + i) K = false) by (apply Nat.ltb_ge; lia).
      rewrite E. ring.
    - apply q_sum_zero. }
  rewrite H2.
  assert (H1 : q_sum (fun j => had k m j * spec_trunc (op_apply (had k) f (pow2 k)) K j) K
               == q_sum (fun i => op_apply (had k) f (pow2 k) i * had k i m) K).
  { apply q_sum_ext_bounded. intros i Hi. unfold spec_trunc.
    assert (E : Nat.ltb i K = true) by (apply Nat.ltb_lt; exact Hi).
    rewrite E. rewrite (had_symmetric k m i). ring. }
  rewrite H1. ring.
Qed.

(* ===================================================================== *)
(*  3. The error of reconstruction is the dropped energy                *)
(* ===================================================================== *)

(** The energy of the dropped part of a spectrum is the tail of the sum of squares. *)
Lemma dropped_energy : forall (c : nat -> Q) (K N : nat), (K <= N)%nat ->
  seq_inner (fun i => c i - spec_trunc c K i) (fun i => c i - spec_trunc c K i) N
  == q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)%nat.
Proof.
  intros c K N HK. unfold seq_inner.
  transitivity (q_sum (fun i => (c i - spec_trunc c K i) * (c i - spec_trunc c K i)) (K + (N - K))).
  { replace (K + (N - K))%nat with N by lia. reflexivity. }
  rewrite q_sum_split. cbn beta.
  assert (H1 : q_sum (fun i => (c i - spec_trunc c K i) * (c i - spec_trunc c K i)) K == 0).
  { transitivity (q_sum (fun _ : nat => 0) K).
    - apply q_sum_ext_bounded. intros i Hi. unfold spec_trunc.
      assert (E : Nat.ltb i K = true) by (apply Nat.ltb_lt; exact Hi).
      rewrite E. ring.
    - apply q_sum_zero. }
  assert (H2 : q_sum (fun i => (c (K + i)%nat - spec_trunc c K (K + i)%nat)
                               * (c (K + i)%nat - spec_trunc c K (K + i)%nat)) (N - K)
               == q_sum (fun i => c (K + i)%nat * c (K + i)%nat) (N - K)).
  { apply q_sum_ext. intro i. unfold spec_trunc.
    assert (E : Nat.ltb (K + i) K = false) by (apply Nat.ltb_ge; lia).
    rewrite E. ring. }
  rewrite H1, H2. ring.
Qed.

(** The residual f - f_K is (1/N) H (dropped part of the spectrum). *)
Lemma walsh_resid_as_transform : forall k f K m, (m < pow2 k)%nat ->
  f m - walsh_rec k K f m
  == op_apply (had k)
       (fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i)
       (pow2 k) m / Nq k.
Proof.
  intros k f K m Hm. unfold walsh_rec.
  rewrite (op_apply_sub (had k) (op_apply (had k) f (pow2 k))
                        (spec_trunc (op_apply (had k) f (pow2 k)) K) (pow2 k) m).
  rewrite (walsh_HH k f m Hm).
  field. apply pow2_Q_neq0.
Qed.

(** N * ||f - f_K||^2 = the sum of squares of the dropped coefficients. *)
Theorem walsh_compression_error : forall k f K, (K <= pow2 k)%nat ->
  Nq k * seq_inner (fun m => f m - walsh_rec k K f m)
                   (fun m => f m - walsh_rec k K f m) (pow2 k)
  == q_sum (fun i => op_apply (had k) f (pow2 k) (K + i)%nat
                     * op_apply (had k) f (pow2 k) (K + i)%nat) (pow2 k - K)%nat.
Proof.
  intros k f K HK.
  pose proof (pow2_Q_neq0 k) as Hnz.
  assert (Hd := dropped_energy (op_apply (had k) f (pow2 k)) K (pow2 k) HK).
  assert (Hp := parseval_walsh k
     (fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i)).
  set (d := fun i => op_apply (had k) f (pow2 k) i - spec_trunc (op_apply (had k) f (pow2 k)) K i) in *.
  transitivity (Nq k * seq_inner (fun m => op_apply (had k) d (pow2 k) m / Nq k)
                                 (fun m => op_apply (had k) d (pow2 k) m / Nq k) (pow2 k)).
  { apply Qmult_comp; [ reflexivity | ].
    apply seq_inner_ext_bounded; intros m Hm; exact (walsh_resid_as_transform k f K m Hm). }
  transitivity (Nq k * ((1 / (Nq k * Nq k))
                        * seq_inner (op_apply (had k) d (pow2 k))
                                    (op_apply (had k) d (pow2 k)) (pow2 k))).
  { apply Qmult_comp; [ reflexivity | ].
    unfold seq_inner.
    rewrite <- (q_sum_scale (1 / (Nq k * Nq k))
                  (fun i => op_apply (had k) d (pow2 k) i * op_apply (had k) d (pow2 k) i)
                  (pow2 k)).
    apply q_sum_ext. intro i. field. exact Hnz. }
  rewrite Hp, Hd. field. exact Hnz.
Qed.

(** The tail equals N * ||f||^2 minus the captured energy: an equality, by Plancherel. *)
Theorem walsh_tail_eq : forall k f K, (K <= pow2 k)%nat ->
  q_sum (fun i => op_apply (had k) f (pow2 k) (K + i)%nat
                  * op_apply (had k) f (pow2 k) (K + i)%nat) (pow2 k - K)%nat
  == Nq k * seq_inner f f (pow2 k) - captured (op_apply (had k) f (pow2 k)) K.
Proof.
  intros k f K HK.
  pose proof (truncation_error_eq (op_apply (had k) f (pow2 k)) K (pow2 k) HK) as Hs.
  unfold captured in Hs at 1.
  change (q_sum (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) f (pow2 k) i)
                (pow2 k))
    with (seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k)) in Hs.
  rewrite (parseval_walsh k f) in Hs. lra.
Qed.

Corollary walsh_compression_error_energy : forall k f K, (K <= pow2 k)%nat ->
  Nq k * seq_inner (fun m => f m - walsh_rec k K f m)
                   (fun m => f m - walsh_rec k K f m) (pow2 k)
  == Nq k * seq_inner f f (pow2 k) - captured (op_apply (had k) f (pow2 k)) K.
Proof.
  intros k f K HK. rewrite (walsh_compression_error k f K HK).
  exact (walsh_tail_eq k f K HK).
Qed.

(** The error does not grow when coefficients are added. *)
Corollary walsh_compression_error_mono : forall k f K K',
  (K <= K')%nat -> (K' <= pow2 k)%nat ->
  seq_inner (fun m => f m - walsh_rec k K' f m) (fun m => f m - walsh_rec k K' f m) (pow2 k)
  <= seq_inner (fun m => f m - walsh_rec k K f m) (fun m => f m - walsh_rec k K f m) (pow2 k).
Proof.
  intros k f K K' HKK HK'.
  apply (proj1 (Qmult_le_l _ _ (Nq k) (pow2_Q_pos k))).
  rewrite (walsh_compression_error_energy k f K' HK').
  rewrite (walsh_compression_error_energy k f K ltac:(lia)).
  pose proof (captured_mono (op_apply (had k) f (pow2 k)) K K' HKK) as Hm. lra.
Qed.

(* ===================================================================== *)
(*  4. A band-limited signal is recovered without loss                  *)
(* ===================================================================== *)

Theorem walsh_bandlimited_lossless : forall k f K,
  (forall i, (K <= i < pow2 k)%nat -> op_apply (had k) f (pow2 k) i == 0) ->
  forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m.
Proof.
  intros k f K Hz m Hm. unfold walsh_rec.
  rewrite (op_apply_ext_bounded (had k) (spec_trunc (op_apply (had k) f (pow2 k)) K)
                                (op_apply (had k) f (pow2 k)) (pow2 k) m).
  - rewrite (walsh_HH k f m Hm). field. apply pow2_Q_neq0.
  - intros j Hj. unfold spec_trunc. destruct (Nat.ltb j K) eqn:E.
    + reflexivity.
    + apply Nat.ltb_ge in E. symmetry. apply Hz. lia.
Qed.

(** And only a band-limited signal is. *)
Theorem walsh_lossless_iff : forall k f K, (K <= pow2 k)%nat ->
  (forall m, (m < pow2 k)%nat -> walsh_rec k K f m == f m)
  <-> (forall i, (K <= i < pow2 k)%nat -> op_apply (had k) f (pow2 k) i == 0).
Proof.
  intros k f K HK. split.
  - intros Hrec i Hi.
    assert (Hz : seq_inner (fun m => f m - walsh_rec k K f m)
                           (fun m => f m - walsh_rec k K f m) (pow2 k) == 0).
    { apply ProcessL2Orthonormal.seq_inner_self_zero_of_coords.
      intros m Hm. cbv beta. rewrite (Hrec m Hm). ring. }
    pose proof (walsh_compression_error k f K HK) as He. rewrite Hz in He.
    assert (Ht : q_sum (fun j => op_apply (had k) f (pow2 k) (K + j)%nat
                                 * op_apply (had k) f (pow2 k) (K + j)%nat) (pow2 k - K)%nat == 0).
    { rewrite <- He. ring. }
    pose proof (q_sum_sq_zero (fun j => op_apply (had k) f (pow2 k) (K + j)%nat)
                              (pow2 k - K)%nat Ht (i - K)%nat ltac:(lia)) as Hi0.
    cbv beta in Hi0. replace (K + (i - K))%nat with i in Hi0 by lia. exact Hi0.
  - intros Hz. exact (walsh_bandlimited_lossless k f K Hz).
Qed.

(* ===================================================================== *)
(*  5. The normalised scale, when s^2 = N for a rational s              *)
(* ===================================================================== *)

(** For the normalised Walsh system (rows H_i / s, s^2 = N) the error of the
    K-term partial sum is the sum of squares of the dropped normalised
    coefficients: the formula ||f||^2 = kept + dropped read as a statement
    about the error. *)
Corollary walsh_normalized_error_is_tail : forall (k : nat) (s : Q),
  s * s == inject_Z (Z.of_nat (pow2 k)) ->
  forall (f : nat -> Q) (K : nat), (K <= pow2 k)%nat ->
  ferr (walsh_n k s) f (pow2 k) K
  == q_sum (fun i => seq_inner (walsh_n k s (K + i)%nat) f (pow2 k)
                     * seq_inner (walsh_n k s (K + i)%nat) f (pow2 k)) (pow2 k - K)%nat.
Proof.
  intros k s Hs f K HK.
  apply (fourier_error_is_tail_b (walsh_n k s) (pow2 k) (pow2 k)
           (walsh_normalized_on k s Hs) f K HK).
  unfold captured. exact (walsh_normalized_parseval k s Hs f).
Qed.

(** The premise holds for every N = 4^j with s = 2^j. *)
Example walsh_4j_error_is_tail : forall (j : nat) (f : nat -> Q) (K : nat),
  (K <= pow2 (2 * j))%nat ->
  ferr (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j)))) f (pow2 (2 * j)) K
  == q_sum (fun i => seq_inner (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) (K + i)%nat) f (pow2 (2 * j))
                     * seq_inner (walsh_n (2 * j) (inject_Z (Z.of_nat (pow2 j))) (K + i)%nat) f (pow2 (2 * j)))
           (pow2 (2 * j) - K)%nat.
Proof.
  intros j f K HK.
  exact (walsh_normalized_error_is_tail (2 * j) (inject_Z (Z.of_nat (pow2 j)))
           (walsh_even_norm_exists j) f K HK).
Qed.

(* ===================================================================== *)
(*  6. Convolution through the transform                                *)
(* ===================================================================== *)

(** N (f * g) = H ((Hf) . (Hg)): the inverse step of the convolution theorem. *)
Theorem walsh_convolution_inverse : forall k f g n, (n < pow2 k)%nat ->
  Nq k * dconv f g (pow2 k) n
  == op_apply (had k)
       (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) g (pow2 k) i) (pow2 k) n.
Proof.
  intros k f g n Hn.
  rewrite <- (walsh_HH k (dconv f g (pow2 k)) n Hn).
  apply op_apply_ext_bounded. intros i Hi. exact (walsh_convolution k f g i Hi).
Qed.

(** The same through the fast transform. *)
Theorem convolution_via_fwht : forall k f g n, (n < pow2 k)%nat ->
  dconv f g (pow2 k) n == fwht k (fun i => fwht k f i * fwht k g i) n / Nq k.
Proof.
  intros k f g n Hn.
  rewrite (fwht_correct k (fun i => fwht k f i * fwht k g i) n Hn).
  rewrite (op_apply_ext_bounded (had k) (fun i => fwht k f i * fwht k g i)
             (fun i => op_apply (had k) f (pow2 k) i * op_apply (had k) g (pow2 k) i)
             (pow2 k) n).
  - rewrite <- (walsh_convolution_inverse k f g n Hn). field. apply pow2_Q_neq0.
  - intros i Hi. rewrite (fwht_correct k f i Hi), (fwht_correct k g i Hi). reflexivity.
Qed.

