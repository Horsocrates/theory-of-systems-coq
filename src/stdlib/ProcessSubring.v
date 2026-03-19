(* ProcessSubring.v — Cauchy subring and ideals *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Cauchy processes closed under ring ops                     *)
(* ================================================================== *)

Lemma cauchy_neg_is_cauchy : forall f,
  is_Cauchy f -> is_Cauchy (process_neg f).
Proof.
  intros f Hf eps Heps.
  destruct (Hf eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  unfold process_neg.
  assert (Heq : - f m - - f n == -(f m - f n)) by ring.
  rewrite Heq. rewrite Qabs_opp. exact (HN m n Hm Hn).
Qed.

Lemma const_is_cauchy : forall q, is_Cauchy (const_process q).
Proof.
  intros q eps Heps. exists 0%nat. intros m n _ _.
  unfold const_process.
  assert (Heq : q - q == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

Lemma zero_is_cauchy : is_Cauchy process_zero.
Proof. apply const_is_cauchy. Qed.

Lemma one_is_cauchy : is_Cauchy process_one.
Proof. apply const_is_cauchy. Qed.

(* ================================================================== *)
(*  Part II: Vanishing Ideal                                           *)
(* ================================================================== *)

Definition process_vanishing (f : RealProcess) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
  Qabs (f n) < eps.

Lemma zero_vanishes : process_vanishing process_zero.
Proof.
  intros eps Heps. exists 0%nat. intros n _.
  unfold process_zero, const_process.
  rewrite Qabs_pos; lra.
Qed.

Lemma vanishing_neg : forall f,
  process_vanishing f -> process_vanishing (process_neg f).
Proof.
  intros f Hf eps Heps.
  destruct (Hf eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold process_neg. rewrite Qabs_opp. exact (HN n Hn).
Qed.

Lemma const_nonzero_not_vanishing : forall q,
  ~ (q == 0) -> ~ process_vanishing (const_process q).
Proof.
  intros q Hne Hv.
  assert (Hqpos : 0 < Qabs q).
  { destruct (Q_dec q 0) as [[Hlt|Hgt]|Heqq].
    - rewrite Qabs_neg; lra.
    - rewrite Qabs_pos; lra.
    - exfalso. apply Hne. exact Heqq. }
  destruct (Hv (Qabs q) Hqpos) as [N HN].
  specialize (HN N (le_n N)).
  unfold const_process in HN. lra.
Qed.

(** Process real equivalence: f ~ g iff f-g vanishes *)
Definition process_real_equiv (f g : RealProcess) : Prop :=
  process_vanishing (process_sub f g).

Lemma process_real_equiv_refl : forall f, process_real_equiv f f.
Proof.
  intros f eps Heps. exists 0%nat. intros n _.
  unfold process_sub, process_add, process_neg.
  assert (Heq : f n + - f n == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

Lemma process_real_equiv_sym : forall f g,
  process_real_equiv f g -> process_real_equiv g f.
Proof.
  intros f g Hfg eps Heps.
  destruct (Hfg eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold process_sub, process_add, process_neg in *.
  assert (Heq : g n + - f n == -(f n + - g n)) by ring.
  rewrite Heq. rewrite Qabs_opp. exact (HN n Hn).
Qed.

(** ★ Constants are distinguished: p != q -> const(p) !~ const(q) *)
Theorem Q_embeds_in_quotient : forall p q : Q,
  ~ (p == q) -> ~ process_real_equiv (const_process p) (const_process q).
Proof.
  intros p q Hne Heq.
  apply const_nonzero_not_vanishing with (p - q).
  - intros H. apply Hne. lra.
  - intros eps Heps. destruct (Heq eps Heps) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    unfold process_sub, process_add, process_neg, const_process in *.
    exact HN.
Qed.

Definition process_subring_count := 12%nat.
