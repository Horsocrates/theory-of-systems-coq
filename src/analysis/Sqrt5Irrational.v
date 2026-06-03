(** * Sqrt5Irrational.v — Irrationality of sqrt(5): no rational squares to 5.

    Theory of Systems — Number Theory / Analysis.  Sibling of
    `analysis/Sqrt2Irrational.v` and `analysis/Sqrt3Irrational.v`, needed by the
    ℚ-kinematics direction ④ (`stdlib/CrystallographicRestriction.v`): an order-5
    rational rotation of SO(3) would have trace 1+2cos72° with 2cos72°=(√5−1)/2,
    which is NOT rational — so the pentagon/icosahedron symmetry (order 5) is
    excluded over ℚ.  √5 is to ④ what √2,√3 are to ① (the new role-limit).

    Elements: integers p, q; rational r = p/q.
    Roles:    the √5-PROCESS — a non-terminating ℚ-process, never an Element.
    Rules:    5 is prime ⟹ 5 | n² ⟹ 5 | n (prime_mult); infinite descent on
              |p|+|q| (L5: well-ordering).

    Strategy: p² = 5·q² ⟹ 5|p ⟹ p=5p' ⟹ q² = 5·p'² ⟹ 5|q ⟹ q=5q' ⟹
    p'² = 5·q'² with (p',q') strictly smaller ⟹ descent ⟹ p=q=0.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Znumtheory.

Open Scope Z_scope.

(* ================================================================= *)
(** ** 5 is prime, and 5 | n² ⟹ 5 | n                                *)
(* ================================================================= *)

Lemma prime_5 : prime 5.
Proof.
  apply prime_intro; [ lia | ].
  intros n Hn.
  assert (Hcase : n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  destruct Hcase as [H1 | [H2 | [H3 | H4]]]; subst n;
    apply Zgcd_1_rel_prime; reflexivity.
Qed.

Lemma five_div_sq : forall n : Z, (5 | n * n) -> (5 | n).
Proof.
  intros n H.
  apply prime_mult in H.
  - destruct H; assumption.
  - exact prime_5.
Qed.

(* ================================================================= *)
(** ** p² = 5·q² ⟹ 5 | p and 5 | q                                   *)
(* ================================================================= *)

Lemma sq_eq_5sq_div5 : forall p q : Z,
  p * p = 5 * (q * q) -> (5 | p) /\ (5 | q).
Proof.
  intros p q Heq.
  assert (Hp : (5 | p)).
  { apply five_div_sq. exists (q * q). lia. }
  destruct Hp as [k Hk].   (* p = k * 5 *)
  split.
  - exists k. exact Hk.
  - apply five_div_sq.
    exists (k * k).
    assert (H25 : p * p = 25 * (k * k)) by (rewrite Hk; ring).
    lia.
Qed.

(* ================================================================= *)
(** ** Descent step: divide both p and q by 5                        *)
(* ================================================================= *)

Lemma descent_step_5 : forall p q : Z,
  p * p = 5 * (q * q) ->
  exists p' q' : Z,
    p = 5 * p' /\ q = 5 * q' /\ p' * p' = 5 * (q' * q').
Proof.
  intros p q Heq.
  destruct (sq_eq_5sq_div5 p q Heq) as [Hp Hq].
  destruct Hp as [p' Hp'].
  destruct Hq as [q' Hq'].
  exists p', q'.
  split. lia.
  split. lia.
  assert (H1 : p * p = 25 * (p' * p')) by (rewrite Hp'; ring).
  assert (H2 : q * q = 25 * (q' * q')) by (rewrite Hq'; ring).
  lia.
Qed.

(* ================================================================= *)
(** ** Infinite descent: p² = 5·q² ⟹ p = 0 and q = 0                 *)
(* ================================================================= *)

Lemma descent_to_zero_5 : forall n : nat, forall p q : Z,
  Z.to_nat (Z.abs p + Z.abs q) = n ->
  p * p = 5 * (q * q) ->
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
    + destruct (descent_step_5 p q Heq) as [p' [q' [Hp' [Hq' Heq']]]].
      assert (Hlt : (Z.to_nat (Z.abs p' + Z.abs q') < n)%nat).
      { subst p q n.
        rewrite !Z.abs_mul. simpl (Z.abs 5).
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
(** ** Main theorem: sqrt(5) is irrational over Z                     *)
(* ================================================================= *)

Theorem sqrt5_irrational_Z : forall p q : Z,
  q <> 0 -> p * p <> 5 * (q * q).
Proof.
  intros p q Hq Heq.
  assert (H : p = 0 /\ q = 0).
  { apply (descent_to_zero_5 (Z.to_nat (Z.abs p + Z.abs q)) p q).
    - reflexivity.
    - exact Heq. }
  destruct H as [_ Hq0].
  contradiction.
Qed.

(* ================================================================= *)
(** ** Corollary: no rational squares to 5                            *)
(* ================================================================= *)

Open Scope Q_scope.

Theorem no_rational_sqrt5 : forall r : Q,
  ~ (r * r == 5).
Proof.
  intros r Heq.
  destruct r as [p d].
  unfold Qeq in Heq. simpl in Heq.
  assert (Heq2 : (p * p = 5 * Z.pos (d * d))%Z) by lia.
  assert (Hdd : Z.pos (d * d) = (Z.pos d * Z.pos d)%Z) by lia.
  rewrite Hdd in Heq2.
  apply (sqrt5_irrational_Z p (Z.pos d)).
  - discriminate.
  - exact Heq2.
Qed.

(** sqrt(5) is not in Q. *)
Corollary sqrt5_not_in_Q : ~ (exists r : Q, r * r == 5).
Proof.
  intros [r Hr].
  exact (no_rational_sqrt5 r Hr).
Qed.
