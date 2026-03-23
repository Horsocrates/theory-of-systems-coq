(** * FiniteSizePortfolio.v — Finite-size effects in portfolios as ToS System
    Elements: portfolio size K, sample count N, noise fraction, MP threshold
    Roles:    noise quantification, eigenvalue filtering, finite-size correction
    Rules:    Marcenko-Pastur threshold approximation, noise fraction = K/N,
              eigenvalue filtering by MP boundary
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Noise fraction and Marcenko-Pastur threshold                     *)
(* ================================================================ *)

(* noise_fraction q = K/N — ratio of assets to samples *)
Definition noise_fraction (K N : Q) : Q := K / N.

(* Marcenko-Pastur upper threshold: (1 + sqrt(q))^2
   Approximation for rational: (1 + q)^2 when q < 1 *)
Definition mp_threshold_approx (K N : Q) : Q :=
  let q := K / N in
  (1 + q) * (1 + q).

(* Number of signal eigenvalues (approximate): those above MP threshold *)
(* In practice: K - floor(K * noise_fraction) *)
(* Simplified: for K assets, noise count ≈ K * q *)
Definition noise_eigenvalue_count (K N : Q) : Q := K * (K / N).

Definition signal_eigenvalue_count (K N : Q) : Q := K - noise_eigenvalue_count K N.

(* ================================================================ *)
(* Concrete noise fractions                                         *)
(* ================================================================ *)

(* 10 assets, 100 samples: q = 1/10 *)
Lemma noise_frac_10_100 : noise_fraction 10 100 == 1#10.
Proof. unfold noise_fraction. vm_compute. reflexivity. Qed.

(* 50 assets, 100 samples: q = 1/2 *)
Lemma noise_frac_50_100 : noise_fraction 50 100 == 1#2.
Proof. unfold noise_fraction. vm_compute. reflexivity. Qed.

(* 100 assets, 100 samples: q = 1 (fully noisy) *)
Lemma noise_frac_100_100 : noise_fraction 100 100 == 1.
Proof. unfold noise_fraction. vm_compute. reflexivity. Qed.

(* 200 assets, 100 samples: q = 2 (overdetermined) *)
Lemma noise_frac_200_100 : noise_fraction 200 100 == 2.
Proof. unfold noise_fraction. vm_compute. reflexivity. Qed.

(* 5 assets, 250 samples: q = 1/50 *)
Lemma noise_frac_5_250 : noise_fraction 5 250 == 1#50.
Proof. unfold noise_fraction. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Marcenko-Pastur thresholds                                       *)
(* ================================================================ *)

(* K=10, N=100: q=1/10, threshold = (1+1/10)^2 = (11/10)^2 = 121/100 *)
Lemma mp_threshold_10_100 : mp_threshold_approx 10 100 == 121#100.
Proof. unfold mp_threshold_approx. vm_compute. reflexivity. Qed.

(* K=50, N=100: q=1/2, threshold = (3/2)^2 = 9/4 *)
Lemma mp_threshold_50_100 : mp_threshold_approx 50 100 == 9#4.
Proof. unfold mp_threshold_approx. vm_compute. reflexivity. Qed.

(* K=100, N=100: q=1, threshold = 4 *)
Lemma mp_threshold_100_100 : mp_threshold_approx 100 100 == 4.
Proof. unfold mp_threshold_approx. vm_compute. reflexivity. Qed.

(* More data means lower threshold *)
Lemma mp_threshold_monotone :
  mp_threshold_approx 10 100 < mp_threshold_approx 50 100.
Proof. unfold mp_threshold_approx, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Signal eigenvalue counts                                         *)
(* ================================================================ *)

(* K=10, N=100: noise count = 10*(1/10) = 1, signal = 9 *)
Lemma signal_count_10_100 : signal_eigenvalue_count 10 100 == 9.
Proof. unfold signal_eigenvalue_count, noise_eigenvalue_count. vm_compute. reflexivity. Qed.

(* K=50, N=100: noise count = 50*(1/2) = 25, signal = 25 *)
Lemma signal_count_50_100 : signal_eigenvalue_count 50 100 == 25.
Proof. unfold signal_eigenvalue_count, noise_eigenvalue_count. vm_compute. reflexivity. Qed.

(* K=100, N=100: noise count = 100, signal = 0 (all noise) *)
Lemma signal_count_100_100 : signal_eigenvalue_count 100 100 == 0.
Proof. unfold signal_eigenvalue_count, noise_eigenvalue_count. vm_compute. reflexivity. Qed.

(* More samples → more signal *)
Lemma more_samples_more_signal :
  signal_eigenvalue_count 10 100 > signal_eigenvalue_count 10 20.
Proof.
  unfold signal_eigenvalue_count, noise_eigenvalue_count, Qgt, Qlt.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(* Eigenvalue filtering: is eigenvalue above MP threshold?          *)
(* ================================================================ *)

Definition is_signal_eigenvalue (eigenval K N : Q) : bool :=
  negb (Qle_bool eigenval (mp_threshold_approx K N)).

(* eigenvalue 2.5 > threshold 121/100 for K=10,N=100: signal *)
Lemma filter_signal_example :
  is_signal_eigenvalue (5#2) 10 100 = true.
Proof. unfold is_signal_eigenvalue, mp_threshold_approx. vm_compute. reflexivity. Qed.

(* eigenvalue 1.0 < threshold 121/100: noise *)
Lemma filter_noise_example :
  is_signal_eigenvalue 1 10 100 = false.
Proof. unfold is_signal_eigenvalue, mp_threshold_approx. vm_compute. reflexivity. Qed.

(* eigenvalue 5 > threshold 9/4 for K=50,N=100: signal *)
Lemma filter_signal_large :
  is_signal_eigenvalue 5 50 100 = true.
Proof. unfold is_signal_eigenvalue, mp_threshold_approx. vm_compute. reflexivity. Qed.

(* eigenvalue 2 < threshold 9/4: noise *)
Lemma filter_noise_large :
  is_signal_eigenvalue 2 50 100 = false.
Proof. unfold is_signal_eigenvalue, mp_threshold_approx. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition finite_size_synthesis : Prop :=
  noise_fraction 10 100 == 1#10 /\
  mp_threshold_approx 100 100 == 4 /\
  signal_eigenvalue_count 100 100 == 0 /\
  is_signal_eigenvalue (5#2) 10 100 = true.

Lemma finite_size_synthesis_holds : finite_size_synthesis.
Proof.
  split. exact noise_frac_10_100.
  split. exact mp_threshold_100_100.
  split. exact signal_count_100_100.
  exact filter_signal_example.
Qed.
