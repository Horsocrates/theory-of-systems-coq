(* ========================================================================= *)
(*        GRID FUNCTIONS — Finite-Dimensional Function Spaces                 *)
(*                                                                            *)
(*  Functions on a periodic grid of N points: f : nat → Q.                  *)
(*  These represent velocity fields at finite resolution.                      *)
(*                                                                            *)
(*  Norms: L² = Σ|f(i)|², H¹ = L² + Σ|Df(i)|²                             *)
(*  Inner product: ⟨f,g⟩ = Σ f(i)·g(i)                                    *)
(*  (We omit 1/N factor — just use raw sums for cleaner Q proofs)           *)
(*                                                                            *)
(*  STATUS: ~40 Qed, 0 Admitted                                              *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ========================================================================= *)
(*  PART I: Summation                                                         *)
(* ========================================================================= *)

(** Summation of f(0) + f(1) + ... + f(n-1) *)
Fixpoint sum_Q_ns (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => sum_Q_ns f k + f k
  end.

Lemma sum_ns_0 : forall f, sum_Q_ns f 0 == 0.
Proof. intros. reflexivity. Qed.

Lemma sum_ns_S : forall f n, sum_Q_ns f (S n) == sum_Q_ns f n + f n.
Proof. intros. reflexivity. Qed.

Lemma sum_ns_1 : forall f, sum_Q_ns f 1 == f 0%nat.
Proof. intros. simpl. lra. Qed.

Lemma sum_ns_zero_fn : forall n, sum_Q_ns (fun _ => 0) n == 0.
Proof.
  intros. induction n as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma sum_ns_add : forall f g n,
  sum_Q_ns (fun i => f i + g i) n == sum_Q_ns f n + sum_Q_ns g n.
Proof.
  intros f g n. induction n as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma sum_ns_scale : forall c f n,
  sum_Q_ns (fun i => c * f i) n == c * sum_Q_ns f n.
Proof.
  intros c f n. induction n as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma sum_ns_neg : forall f n,
  sum_Q_ns (fun i => - f i) n == - sum_Q_ns f n.
Proof.
  intros f n. induction n as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma sum_ns_nonneg : forall f n,
  (forall i, (i < n)%nat -> 0 <= f i) ->
  0 <= sum_Q_ns f n.
Proof.
  intros f n H. induction n as [|n IH]; simpl; [lra |].
  assert (Hf : 0 <= f n) by (apply H; lia).
  assert (Hs : 0 <= sum_Q_ns f n) by (apply IH; intros; apply H; lia).
  lra.
Qed.

Lemma Qsq_nonneg : forall x, 0 <= x * x.
Proof.
  intros x. destruct (Qlt_le_dec x 0) as [Hn|Hp].
  - assert (H1 : 0 <= -x) by lra.
    assert (H2 : (-x) * (-x) == x * x) by lra.
    rewrite <- H2. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma Qsq_eq_0 : forall x, x * x == 0 -> x == 0.
Proof.
  intros x H.
  destruct (Qlt_le_dec x 0) as [Hn|Hp].
  - assert (0 < (-x) * (-x)) by (apply Qmult_lt_0_compat; lra).
    assert ((-x) * (-x) == x * x) by ring. lra.
  - destruct (Qlt_le_dec 0 x) as [Hpos|Hle0].
    + assert (0 < x * x) by (apply Qmult_lt_0_compat; lra). lra.
    + lra.
Qed.

Lemma sum_ns_sq_nonneg : forall f n,
  0 <= sum_Q_ns (fun i => f i * f i) n.
Proof.
  intros. apply sum_ns_nonneg. intros. apply Qsq_nonneg.
Qed.

Lemma sum_ns_ext : forall f g n,
  (forall i, (i < n)%nat -> f i == g i) ->
  sum_Q_ns f n == sum_Q_ns g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl; [lra |].
  rewrite IH by (intros; apply H; lia).
  rewrite (H n ltac:(lia)). lra.
Qed.

Lemma sum_ns_le : forall f g n,
  (forall i, (i < n)%nat -> f i <= g i) ->
  sum_Q_ns f n <= sum_Q_ns g n.
Proof.
  intros f g n H. induction n as [|n IH]; simpl; [lra |].
  assert (Hfg := H n ltac:(lia)).
  assert (HIH : sum_Q_ns f n <= sum_Q_ns g n) by (apply IH; intros; apply H; lia).
  lra.
Qed.

Lemma sum_ns_telescope : forall (f : nat -> Q) N,
  (0 < N)%nat ->
  sum_Q_ns (fun i => f (S i) - f i) N == f N - f 0%nat.
Proof.
  intros f N HN. induction N as [|n IH]; [lia |].
  destruct n as [|n']; [simpl; lra |].
  simpl sum_Q_ns. rewrite (IH ltac:(lia)). lra.
Qed.

(* ========================================================================= *)
(*  PART II: Grid Functions                                                   *)
(* ========================================================================= *)

Definition grid_fn := nat -> Q.
Definition gf_zero : grid_fn := fun _ => 0.
Definition gf_const (c : Q) : grid_fn := fun _ => c.
Definition gf_add (f g : grid_fn) : grid_fn := fun i => f i + g i.
Definition gf_scale (c : Q) (f : grid_fn) : grid_fn := fun i => c * f i.
Definition gf_sub (f g : grid_fn) : grid_fn := fun i => f i - g i.
Definition gf_mul (f g : grid_fn) : grid_fn := fun i => f i * g i.

Lemma gf_add_comm : forall (f g : grid_fn) i,
  gf_add f g i == gf_add g f i.
Proof. intros. unfold gf_add. lra. Qed.

Lemma gf_add_assoc : forall (f g h : grid_fn) i,
  gf_add (gf_add f g) h i == gf_add f (gf_add g h) i.
Proof. intros. unfold gf_add. lra. Qed.

Lemma gf_add_zero_l : forall (f : grid_fn) i,
  gf_add gf_zero f i == f i.
Proof. intros. unfold gf_add, gf_zero. lra. Qed.

Lemma gf_add_zero_r : forall (f : grid_fn) i,
  gf_add f gf_zero i == f i.
Proof. intros. unfold gf_add, gf_zero. lra. Qed.

Lemma gf_scale_zero : forall (f : grid_fn) i,
  gf_scale 0 f i == 0.
Proof. intros. unfold gf_scale. lra. Qed.

Lemma gf_scale_one : forall (f : grid_fn) i,
  gf_scale 1 f i == f i.
Proof. intros. unfold gf_scale. lra. Qed.

Lemma gf_scale_assoc : forall a b (f : grid_fn) i,
  gf_scale a (gf_scale b f) i == gf_scale (a * b) f i.
Proof. intros. unfold gf_scale. lra. Qed.

Lemma gf_scale_add_distr : forall c (f g : grid_fn) i,
  gf_scale c (gf_add f g) i == gf_add (gf_scale c f) (gf_scale c g) i.
Proof. intros. unfold gf_scale, gf_add. lra. Qed.

Lemma gf_sub_self : forall (f : grid_fn) i,
  gf_sub f f i == 0.
Proof. intros. unfold gf_sub. lra. Qed.

Lemma gf_scale_neg : forall (f : grid_fn) i,
  gf_scale (-1) f i == - f i.
Proof. intros. unfold gf_scale. lra. Qed.

(* ========================================================================= *)
(*  PART III: Inner Product and Norms (without 1/N)                          *)
(* ========================================================================= *)

(** Raw inner product: ⟨f,g⟩_raw = Σ f(i)·g(i) *)
Definition gf_inner (N : nat) (f g : grid_fn) : Q :=
  sum_Q_ns (fun i => f i * g i) N.

(** L² norm squared: ‖f‖² = ⟨f,f⟩ *)
Definition gf_norm_sq (N : nat) (f : grid_fn) : Q :=
  gf_inner N f f.

Lemma gf_inner_sym : forall N (f g : grid_fn),
  gf_inner N f g == gf_inner N g f.
Proof.
  intros. unfold gf_inner.
  apply sum_ns_ext. intros. lra.
Qed.

Lemma gf_norm_sq_nonneg : forall N (f : grid_fn),
  0 <= gf_norm_sq N f.
Proof.
  intros. unfold gf_norm_sq, gf_inner. apply sum_ns_sq_nonneg.
Qed.

Lemma gf_norm_sq_zero : forall N,
  gf_norm_sq N gf_zero == 0.
Proof.
  intros. unfold gf_norm_sq, gf_inner, gf_zero.
  induction N as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma gf_inner_scale_l : forall N c (f g : grid_fn),
  gf_inner N (gf_scale c f) g == c * gf_inner N f g.
Proof.
  intros. unfold gf_inner, gf_scale.
  rewrite <- sum_ns_scale.
  apply sum_ns_ext. intros. lra.
Qed.

Lemma gf_inner_scale_r : forall N c (f g : grid_fn),
  gf_inner N f (gf_scale c g) == c * gf_inner N f g.
Proof.
  intros. rewrite gf_inner_sym. rewrite gf_inner_scale_l.
  rewrite gf_inner_sym. reflexivity.
Qed.

Lemma gf_inner_add_l : forall N (f1 f2 g : grid_fn),
  gf_inner N (gf_add f1 f2) g == gf_inner N f1 g + gf_inner N f2 g.
Proof.
  intros. unfold gf_inner, gf_add.
  rewrite <- sum_ns_add.
  apply sum_ns_ext. intros. lra.
Qed.

Lemma gf_inner_add_r : forall N (f g1 g2 : grid_fn),
  gf_inner N f (gf_add g1 g2) == gf_inner N f g1 + gf_inner N f g2.
Proof.
  intros. rewrite gf_inner_sym. rewrite gf_inner_add_l.
  rewrite (gf_inner_sym N g1 f). rewrite (gf_inner_sym N g2 f). reflexivity.
Qed.

Lemma gf_inner_zero_l : forall N (f : grid_fn),
  gf_inner N gf_zero f == 0.
Proof.
  intros. unfold gf_inner, gf_zero.
  induction N as [|n IH]; simpl; [lra | rewrite IH; lra].
Qed.

Lemma gf_inner_zero_r : forall N (f : grid_fn),
  gf_inner N f gf_zero == 0.
Proof.
  intros. rewrite gf_inner_sym. exact (gf_inner_zero_l N f).
Qed.

(** Triangle inequality: ‖f+g‖² ≤ 2(‖f‖² + ‖g‖²) *)
Theorem triangle_sq : forall N (f g : grid_fn),
  gf_norm_sq N (gf_add f g) <= 2 * (gf_norm_sq N f + gf_norm_sq N g).
Proof.
  intros N f g. unfold gf_norm_sq, gf_inner, gf_add.
  induction N as [|n IH].
  - simpl. lra.
  - simpl sum_Q_ns.
    assert (Hpt : 0 <= (f n - g n) * (f n - g n)) by (apply Qsq_nonneg).
    lra.
Qed.

(** Norm of sum expansion *)
Lemma norm_sq_expand : forall N (f g : grid_fn),
  gf_norm_sq N (gf_add f g) ==
  gf_norm_sq N f + 2 * gf_inner N f g + gf_norm_sq N g.
Proof.
  intros. unfold gf_norm_sq, gf_inner, gf_add.
  induction N as [|n IH]; simpl; [lra |].
  rewrite IH. lra.
Qed.

(** Norm of scale *)
Lemma norm_sq_scale : forall N c (f : grid_fn),
  gf_norm_sq N (gf_scale c f) == c * c * gf_norm_sq N f.
Proof.
  intros. unfold gf_norm_sq, gf_inner, gf_scale.
  rewrite <- sum_ns_scale.
  apply sum_ns_ext. intros. lra.
Qed.

(* ========================================================================= *)
(*  PART IV: Concrete Examples                                                *)
(* ========================================================================= *)

Lemma norm_const : forall N c,
  gf_norm_sq N (gf_const c) == inject_Z (Z.of_nat N) * (c * c).
Proof.
  intros. unfold gf_norm_sq, gf_inner, gf_const.
  induction N as [|n IH].
  - simpl. unfold Qeq. simpl. lia.
  - simpl sum_Q_ns. rewrite IH.
    rewrite Nat2Z.inj_succ. unfold Z.succ.
    unfold Qeq, inject_Z, Qplus, Qmult. simpl. lia.
Qed.

Lemma inner_N1 : forall (f g : grid_fn),
  gf_inner 1 f g == f 0%nat * g 0%nat.
Proof. intros. unfold gf_inner. simpl. lra. Qed.

Lemma inner_N2 : forall (f g : grid_fn),
  gf_inner 2 f g == f 0%nat * g 0%nat + f 1%nat * g 1%nat.
Proof. intros. unfold gf_inner. simpl. lra. Qed.

Lemma norm_N1 : forall (f : grid_fn),
  gf_norm_sq 1 f == f 0%nat * f 0%nat.
Proof. intros. unfold gf_norm_sq. exact (inner_N1 f f). Qed.

Lemma gf_scale_zero_fn : forall c i,
  gf_scale c gf_zero i == 0.
Proof. intros. unfold gf_scale, gf_zero. lra. Qed.

(* ========================================================================= *)
(*  PART V: Cauchy-Schwarz                                                   *)
(* ========================================================================= *)

(** Cauchy-Schwarz: ⟨f,g⟩² ≤ ‖f‖²·‖g‖² *)
Theorem cauchy_schwarz_sq : forall N (f g : grid_fn),
  gf_inner N f g * gf_inner N f g <= gf_norm_sq N f * gf_norm_sq N g.
Proof.
  intros N f g. unfold gf_norm_sq, gf_inner.
  induction N as [|n IH].
  - simpl. lra.
  - simpl sum_Q_ns.
    set (S := sum_Q_ns (fun i => f i * g i) n) in *.
    set (Sf := sum_Q_ns (fun i => f i * f i) n) in *.
    set (Sg := sum_Q_ns (fun i => g i * g i) n) in *.
    set (a := f n) in *.
    set (b := g n) in *.
    assert (HIH : S * S <= Sf * Sg) by exact IH.
    assert (HSf : 0 <= Sf) by (subst Sf; apply sum_ns_sq_nonneg).
    assert (HSg : 0 <= Sg) by (subst Sg; apply sum_ns_sq_nonneg).
    (* Case split on Sg *)
    destruct (Qlt_le_dec 0 Sg) as [HSg_pos|HSg_zero].
    + (* Sg > 0: identity Sg*(a^2*Sg - 2Sab + Sf*b^2) = (aSg-bS)^2 + b^2(SfSg-S^2) *)
      assert (Hid : Sg * (a*a*Sg - 2*S*a*b + Sf*b*b) ==
                     (a*Sg - b*S)*(a*Sg - b*S) + b*b*(Sf*Sg - S*S)) by ring.
      assert (Hrhs : 0 <= (a*Sg - b*S)*(a*Sg - b*S) + b*b*(Sf*Sg - S*S)).
      { assert (0 <= (a*Sg - b*S)*(a*Sg - b*S)) by apply Qsq_nonneg.
        assert (0 <= b*b*(Sf*Sg - S*S)).
        { apply Qmult_le_0_compat. apply Qsq_nonneg. lra. }
        lra. }
      assert (Hprod : 0 <= Sg * (a*a*Sg - 2*S*a*b + Sf*b*b)) by lra.
      (* Sg > 0 and Sg * cross >= 0 implies cross >= 0 *)
      destruct (Qlt_le_dec (a*a*Sg - 2*S*a*b + Sf*b*b) 0) as [Hneg|Hcross].
      * exfalso.
        assert (0 < Sg * (-(a*a*Sg - 2*S*a*b + Sf*b*b))).
        { apply Qmult_lt_0_compat; lra. }
        lra.
      * lra.
    + (* Sg <= 0, so Sg == 0, hence S == 0 *)
      assert (HSg0 : Sg == 0) by lra.
      assert (HS0 : S == 0).
      { apply Qsq_eq_0. assert (0 <= S * S) by apply Qsq_nonneg.
        assert (Hle : S * S <= Sf * 0).
        { rewrite <- HSg0. exact HIH. }
        assert (Sf * 0 == 0) by ring. lra. }
      assert (Ha2 : 0 <= a * a) by apply Qsq_nonneg.
      assert (Hb2 : 0 <= b * b) by apply Qsq_nonneg.
      assert (Hsfb2 : 0 <= Sf * (b * b)) by (apply Qmult_le_0_compat; lra).
      assert (H1 : (S + a * b) * (S + a * b) == a * b * (a * b)).
      { rewrite HS0. ring. }
      assert (H2 : (Sf + a * a) * (Sg + b * b) == Sf * (b * b) + a * a * (b * b)).
      { rewrite HSg0. ring. }
      assert (H3 : a * b * (a * b) == a * a * (b * b)) by ring.
      rewrite H1, H2, H3. lra.
Qed.

(* ========================================================================= *)
(*  PART VI: Summary                                                          *)
(* ========================================================================= *)

Theorem grid_function_main :
  (forall N, gf_norm_sq N gf_zero == 0) /\
  (forall N f, 0 <= gf_norm_sq N f) /\
  (forall N f g, gf_inner N f g == gf_inner N g f) /\
  (forall N f g, gf_inner N f g * gf_inner N f g <=
                 gf_norm_sq N f * gf_norm_sq N g).
Proof.
  split; [exact gf_norm_sq_zero |].
  split; [exact gf_norm_sq_nonneg |].
  split; [exact gf_inner_sym |].
  exact cauchy_schwarz_sq.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  ~38 Qed, 0 Admitted                                                       *)
(* ========================================================================= *)
