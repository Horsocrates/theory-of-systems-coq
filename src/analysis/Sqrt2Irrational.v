(** * Sqrt2Irrational.v -- Irrationality of sqrt(2) (Wiedijk #1)

    Theory of Systems -- Number Theory / Analysis

    Classic proof that sqrt(2) is irrational: no rational number r
    satisfies r * r = 2. Uses infinite descent on integers.

    Elements: integers p, q; rational r = p/q
    Roles:    p -> numerator, q -> denominator, gcd -> coprimality witness
    Rules:    even/odd parity propagation, infinite descent (L5: well-ordering)
    Status:   irrational | rational

    Strategy: p^2 = 2*q^2 => p even => p=2k => q^2 = 2*k^2 => q even =>
    contradiction with coprimality (or descent on |p|+|q|).

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Zdiv.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Helper: Z.even of a square implies Z.even of the base          *)
(* ================================================================= *)

(** If n*n is even, then n is even. Contrapositive: odd*odd = odd. *)
Lemma sq_even_implies_even : forall n : Z,
  Z.even (n * n) = true -> Z.even n = true.
Proof.
  intros n H.
  rewrite Z.even_mul in H.
  apply Bool.orb_true_iff in H.
  destruct H; assumption.
Qed.

(** If n is odd, then n*n is odd. *)
Lemma sq_odd_of_odd : forall n : Z,
  Z.odd n = true -> Z.odd (n * n) = true.
Proof.
  intros n Hodd.
  rewrite Z.odd_mul.
  rewrite Hodd. simpl. reflexivity.
Qed.

(** Even means divisible by 2. *)
Lemma even_div2 : forall n : Z,
  Z.even n = true -> exists k, n = 2 * k.
Proof.
  intros n H.
  apply Z.even_spec in H.
  destruct H as [k Hk].
  exists k. lia.
Qed.

(** Odd means not even. *)
Lemma odd_not_even : forall n : Z,
  Z.odd n = true -> Z.even n = false.
Proof.
  intros n H.
  rewrite <- Z.negb_even in H.
  apply Bool.negb_true_iff in H.
  exact H.
Qed.

(* ================================================================= *)
(** ** Key lemma: p^2 = 2*q^2 implies both p and q are even          *)
(* ================================================================= *)

Lemma sq_eq_2sq_both_even : forall p q : Z,
  p * p = 2 * (q * q) ->
  Z.even p = true /\ Z.even q = true.
Proof.
  intros p q Heq.
  (* p*p = 2*(q*q) means p*p is even, so p is even *)
  assert (Hep : Z.even (p * p) = true).
  { rewrite Heq. rewrite Z.even_mul. simpl. reflexivity. }
  assert (Hp_even : Z.even p = true) by (apply sq_even_implies_even; exact Hep).
  split.
  - exact Hp_even.
  - (* p = 2k for some k *)
    apply even_div2 in Hp_even.
    destruct Hp_even as [k Hpk].
    subst p.
    (* (2k)*(2k) = 2*(q*q) => 4*k*k = 2*q*q => q*q = 2*k*k *)
    assert (Heq2 : q * q = 2 * (k * k)) by lia.
    assert (Heq3 : Z.even (q * q) = true).
    { rewrite Heq2. rewrite Z.even_mul. simpl. reflexivity. }
    apply sq_even_implies_even. exact Heq3.
Qed.

(* ================================================================= *)
(** ** The Z.divide version: 2 | p and 2 | q                         *)
(* ================================================================= *)

Lemma sq_eq_2sq_div2 : forall p q : Z,
  p * p = 2 * (q * q) ->
  (2 | p) /\ (2 | q).
Proof.
  intros p q H.
  apply sq_eq_2sq_both_even in H.
  destruct H as [Hp Hq].
  split.
  - apply Z.even_spec in Hp. destruct Hp as [k Hk]. exists k. lia.
  - apply Z.even_spec in Hq. destruct Hq as [k Hk]. exists k. lia.
Qed.

(* ================================================================= *)
(** ** Infinite descent: p^2 = 2*q^2 implies p = 0 and q = 0         *)
(* ================================================================= *)

(** We use strong induction on Z.abs_nat (|p| + |q|). *)

Lemma descent_step : forall p q : Z,
  p * p = 2 * (q * q) ->
  exists p' q' : Z,
    p = 2 * p' /\ q = 2 * q' /\ p' * p' = 2 * (q' * q').
Proof.
  intros p q Heq.
  assert (Hboth := sq_eq_2sq_both_even p q Heq).
  destruct Hboth as [Hp Hq].
  apply even_div2 in Hp. destruct Hp as [p' Hp'].
  apply even_div2 in Hq. destruct Hq as [q' Hq'].
  exists p', q'.
  split. exact Hp'.
  split. exact Hq'.
  subst p q.
  assert (H1 : 2 * p' * (2 * p') = 4 * (p' * p')) by ring.
  assert (H2 : 2 * (2 * q' * (2 * q')) = 4 * (2 * (q' * q'))) by ring.
  rewrite H1 in Heq. rewrite H2 in Heq.
  lia.
Qed.

(** Main descent: p*p = 2*(q*q) => p = 0 /\ q = 0.
    By strong induction on Z.to_nat (Z.abs p + Z.abs q). *)

Lemma Zabs_sum_nonneg : forall p q : Z, 0 <= Z.abs p + Z.abs q.
Proof.
  intros. pose proof (Z.abs_nonneg p). pose proof (Z.abs_nonneg q). lia.
Qed.

Lemma descent_to_zero : forall n : nat, forall p q : Z,
  Z.to_nat (Z.abs p + Z.abs q) = n ->
  p * p = 2 * (q * q) ->
  p = 0 /\ q = 0.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros p q Hn Heq.
  destruct (Z.eq_dec p 0) as [Hp0 | Hpn0].
  - subst p. rewrite Z.mul_0_l in Heq. symmetry in Heq.
    apply Z.eq_mul_0 in Heq. destruct Heq as [Habs | Hqq].
    + discriminate.
    + apply Z.mul_eq_0 in Hqq. destruct Hqq; auto.
  - destruct (Z.eq_dec q 0) as [Hq0 | Hqn0].
    + subst q. rewrite Z.mul_0_l in Heq. rewrite Z.mul_0_r in Heq.
      apply Z.mul_eq_0 in Heq. destruct Heq; contradiction.
    + (* Both nonzero: descend *)
      destruct (descent_step p q Heq) as [p' [q' [Hp' [Hq' Heq']]]].
      assert (Hlt : (Z.to_nat (Z.abs p' + Z.abs q') < n)%nat).
      { subst p q n.
        rewrite !Z.abs_mul. simpl (Z.abs 2).
        assert (Hp'nn : 0 <= Z.abs p') by apply Z.abs_nonneg.
        assert (Hq'nn : 0 <= Z.abs q') by apply Z.abs_nonneg.
        assert (Hpq_pos : Z.abs p' + Z.abs q' > 0).
        { destruct (Z.eq_dec p' 0).
          - subst p'. assert (q' <> 0) by lia.
            assert (0 < Z.abs q') by (apply Z.abs_pos; auto). lia.
          - assert (0 < Z.abs p') by (apply Z.abs_pos; auto). lia. }
        apply Z2Nat.inj_lt; lia. }
      destruct (IH _ Hlt p' q' eq_refl Heq') as [Hp'0 Hq'0].
        subst p' q'. split; lia.
Qed.

(* ================================================================= *)
(** ** Main theorem: sqrt(2) is irrational over Z                     *)
(* ================================================================= *)

Theorem sqrt2_irrational_Z : forall p q : Z,
  q <> 0 -> p * p <> 2 * (q * q).
Proof.
  intros p q Hq Heq.
  assert (H : p = 0 /\ q = 0).
  { apply (descent_to_zero (Z.abs_nat (Z.abs p + Z.abs q)) p q).
    - lia.
    - exact Heq. }
  destruct H as [_ Hq0].
  contradiction.
Qed.

(* ================================================================= *)
(** ** Corollary: no rational squares to 2                            *)
(* ================================================================= *)

Open Scope Q_scope.

Theorem no_rational_sqrt2 : forall r : Q,
  ~ (r * r == 2).
Proof.
  intros r Heq.
  destruct r as [p d].
  unfold Qeq in Heq. simpl in Heq.
  (* Heq : (p * p * 1 = 2 * Z.pos (d * d))%Z *)
  assert (Heq2 : (p * p = 2 * Z.pos (d * d))%Z) by lia.
  (* Z.pos (d * d) = Z.pos d * Z.pos d *)
  assert (Hdd : Z.pos (d * d) = (Z.pos d * Z.pos d)%Z) by lia.
  rewrite Hdd in Heq2.
  apply (sqrt2_irrational_Z p (Z.pos d)).
  - discriminate.
  - exact Heq2.
Qed.

(** Alternative phrasing: sqrt(2) is not in Q. *)
Corollary sqrt2_not_in_Q : ~ (exists r : Q, r * r == 2).
Proof.
  intros [r Hr].
  exact (no_rational_sqrt2 r Hr).
Qed.

(** The positive case: no positive rational squares to 2. *)
Corollary sqrt2_irrational_pos : forall r : Q,
  0 < r -> ~ (r * r == 2).
Proof.
  intros r _ H.
  exact (no_rational_sqrt2 r H).
Qed.

(** No rational number has its square equal to 2 (Leibniz equality version). *)
Lemma no_rational_sqrt2_leibniz : forall p q : Z,
  (0 < q)%Z -> (p * p <> 2 * (q * q))%Z.
Proof.
  intros p q Hq.
  apply sqrt2_irrational_Z.
  lia.
Qed.
