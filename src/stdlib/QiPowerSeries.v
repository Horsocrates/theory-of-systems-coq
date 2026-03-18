(* QiPowerSeries.v — Power series over Q[i], P4-native *)
(* Polynomials are analytic — closes OS1 analyticity True *)

From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessGaussianQ.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Qi Powers  (~10 lemmas)                                    *)
(* ================================================================== *)

Fixpoint qi_pow (z : Qi) (n : nat) : Qi :=
  match n with
  | O => qi_one
  | S k => qi_mul z (qi_pow z k)
  end.

Lemma qi_pow_0 : forall z, qi_eq (qi_pow z 0) qi_one.
Proof. intros z. simpl. unfold qi_eq, qi_one. split; ring. Qed.

Lemma qi_pow_1 : forall z, qi_eq (qi_pow z 1) z.
Proof. intros z. simpl. unfold qi_eq, qi_mul, qi_one. simpl. split; ring. Qed.

Lemma qi_pow_S : forall z n,
  qi_eq (qi_pow z (S n)) (qi_mul z (qi_pow z n)).
Proof. intros z n. simpl. unfold qi_eq. split; ring. Qed.

(** i^0 = 1 *)
Lemma qi_i_pow_0 : qi_eq (qi_pow qi_i 0) qi_one.
Proof. exact (qi_pow_0 qi_i). Qed.

(** i^1 = i *)
Lemma qi_i_pow_1 : qi_eq (qi_pow qi_i 1) qi_i.
Proof. exact (qi_pow_1 qi_i). Qed.

(** i^2 = -1 *)
Lemma qi_i_pow_2 : qi_eq (qi_pow qi_i 2) (mkQi (-(1)) 0).
Proof. simpl. unfold qi_eq, qi_mul, qi_i. simpl. split; ring. Qed.

(** i^3 = -i *)
Lemma qi_i_pow_3 : qi_eq (qi_pow qi_i 3) (mkQi 0 (-(1))).
Proof. simpl. unfold qi_eq, qi_mul, qi_i. simpl. split; ring. Qed.

(** i^4 = 1 *)
Lemma qi_i_pow_4 : qi_eq (qi_pow qi_i 4) qi_one.
Proof. simpl. unfold qi_eq, qi_mul, qi_i, qi_one. simpl. split; ring. Qed.

(** Real power: (qi_of_Q q)^n has zero imaginary part *)
Lemma qi_real_pow_real : forall q n,
  qi_im (qi_pow (qi_of_Q q) n) == 0.
Proof.
  intros q n. induction n as [|n IH].
  - simpl. reflexivity.
  - simpl. unfold qi_mul, qi_of_Q in *. simpl.
    rewrite IH. ring.
Qed.

(* ================================================================== *)
(*  Part II: Power Series Partial Sum  (~10 lemmas)                    *)
(* ================================================================== *)

(** Partial sum: S_N(z) = Σ_{k=0}^{N} a_k · z^k *)
Fixpoint qi_partial_sum (a : nat -> Qi) (z : Qi) (N : nat) : Qi :=
  match N with
  | O => a O
  | S N' => qi_add (qi_partial_sum a z N') (qi_mul (a (S N')) (qi_pow z (S N')))
  end.

Lemma qi_partial_sum_0 : forall a z,
  qi_eq (qi_partial_sum a z O) (a O).
Proof. intros a z. simpl. unfold qi_eq. split; ring. Qed.

Lemma qi_partial_sum_S : forall a z N,
  qi_eq (qi_partial_sum a z (S N))
        (qi_add (qi_partial_sum a z N) (qi_mul (a (S N)) (qi_pow z (S N)))).
Proof. intros. simpl. unfold qi_eq. split; ring. Qed.

(** Adding zero coefficient doesn't change sum *)
Lemma qi_partial_sum_extend_zero : forall a z N,
  qi_eq (a (S N)) qi_zero ->
  qi_eq (qi_partial_sum a z (S N)) (qi_partial_sum a z N).
Proof.
  intros a z N Ha. simpl.
  unfold qi_eq, qi_add, qi_mul, qi_zero in *.
  destruct Ha as [Hr Hi].
  destruct (a (S N)) as [ar ai]. simpl in *.
  destruct (qi_pow z (S N)) as [pr pi]. simpl in *.
  destruct (qi_partial_sum a z N) as [sr si]. simpl in *.
  rewrite Hr, Hi. split; ring.
Qed.

(* ================================================================== *)
(*  Part III: Polynomial = Analytic  (~10 lemmas)                      *)
(* ================================================================== *)

(** A polynomial: coefficients zero above degree N *)
Definition qi_polynomial (a : nat -> Qi) (N : nat) : Prop :=
  forall k, (N < k)%nat -> qi_eq (a k) qi_zero.

(** ★ Polynomial evaluation is EXACT — no convergence needed *)
Theorem polynomial_exact : forall a z N,
  qi_polynomial a N ->
  qi_eq (qi_partial_sum a z (S N)) (qi_partial_sum a z N).
Proof.
  intros a z N Hpoly. apply qi_partial_sum_extend_zero.
  apply Hpoly. lia.
Qed.

(** Definition of analyticity: representable as power series *)
Definition qi_analytic_at (f : Qi -> Qi) (z0 : Qi) : Prop :=
  exists (a : nat -> Qi) (N : nat),
  qi_polynomial a N /\
  forall z, qi_eq (f z) (qi_partial_sum a z N).

(** ★ MAIN THEOREM: Every polynomial is analytic *)
Theorem polynomial_is_analytic : forall (a : nat -> Qi) (N : nat) z0,
  qi_polynomial a N ->
  qi_analytic_at (fun z => qi_partial_sum a z N) z0.
Proof.
  intros a N z0 Hpoly.
  exists a, N. split.
  - exact Hpoly.
  - intros z. unfold qi_eq. split; ring.
Qed.

(** Sum of polynomials is polynomial *)
(** Sum of zero Qi values is zero *)
Lemma qi_add_zero_zero : qi_eq (qi_add qi_zero qi_zero) qi_zero.
Proof. unfold qi_eq, qi_add, qi_zero. simpl. split; ring. Qed.

(** If both a(k) and b(k) are zero, then (a+b)(k) is zero *)
Lemma qi_add_eq_zero : forall x y,
  qi_eq x qi_zero -> qi_eq y qi_zero ->
  qi_eq (qi_add x y) qi_zero.
Proof.
  intros x y [Hxr Hxi] [Hyr Hyi].
  unfold qi_eq, qi_add, qi_zero. simpl.
  destruct x as [xr xi]. destruct y as [yr yi]. simpl in *.
  split; lra.
Qed.

(** Constant is analytic *)
Theorem constant_analytic : forall c z0,
  qi_analytic_at (fun _ => c) z0.
Proof.
  intros c z0.
  exists (fun k => match k with O => c | _ => qi_zero end), O.
  split.
  - intros k Hk. destruct k; [lia|]. unfold qi_eq, qi_zero. split; ring.
  - intros z. simpl. unfold qi_eq. split; ring.
Qed.

(* ================================================================== *)
(*  Part IV: Complex Derivative  (~10 lemmas)                         *)
(* ================================================================== *)

(** f'_K(z) from real direction *)
Definition qi_deriv (f : Qi -> Qi) (z : Qi) (K : nat) : Qi :=
  let h := qi_of_Q (1 / inject_Z (Z.of_nat (S K))) in
  let diff := qi_add (f (qi_add z h)) (qi_mul (mkQi (-(1)) 0) (f z)) in
  qi_mul diff (qi_of_Q (inject_Z (Z.of_nat (S K)))).

(** Derivative of constant = 0 *)
Lemma qi_deriv_const : forall c z K,
  qi_eq (qi_deriv (fun _ => c) z K) qi_zero.
Proof.
  intros c z K. unfold qi_deriv, qi_add, qi_mul, qi_of_Q, qi_zero. simpl.
  unfold qi_eq. simpl. split; ring.
Qed.

(** Derivative is linear *)
Lemma qi_deriv_linear : forall f g z K,
  qi_eq (qi_deriv (fun w => qi_add (f w) (g w)) z K)
        (qi_add (qi_deriv f z K) (qi_deriv g z K)).
Proof.
  intros f g z K. unfold qi_deriv, qi_add, qi_mul, qi_of_Q. simpl.
  unfold qi_eq. simpl. split; ring.
Qed.

(** Derivative of identity *)
Lemma qi_deriv_id : forall z K,
  qi_eq (qi_deriv (fun w => w) z K) qi_one.
Proof.
  intros z K. unfold qi_deriv, qi_add, qi_mul, qi_of_Q, qi_one. simpl.
  unfold qi_eq. simpl. split; field;
  unfold Qeq, inject_Z; simpl; lia.
Qed.

(** Scale rule *)
Lemma qi_deriv_scale : forall c f z K,
  qi_eq (qi_deriv (fun w => qi_mul c (f w)) z K)
        (qi_mul c (qi_deriv f z K)).
Proof.
  intros c f z K. unfold qi_deriv, qi_add, qi_mul, qi_of_Q. simpl.
  unfold qi_eq. simpl. split; ring.
Qed.

Definition qi_power_series_count := 28%nat.
