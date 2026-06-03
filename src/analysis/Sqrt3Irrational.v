(** * Sqrt3Irrational.v — Irrationality of sqrt(3): no rational squares to 3.

    Theory of Systems — Number Theory / Analysis.  Sibling of
    `analysis/Sqrt2Irrational.v` (Wiedijk #1), needed by the ℚ-kinematics
    capstone (`stdlib/CliffordCapstone.v`): the 60°/120° rational-cosine points
    a = ±1/2 have sine ±√3/2, which is NOT rational — so they are NOT rational
    points on the unit circle, and the only finite-order rational points are Z₄.

    Elements: integers p, q; rational r = p/q.
    Roles:    the √3-PROCESS — a non-terminating ℚ-process (approximants), never
              an Element.  "no_rational_sqrt3" is NOT "proof of a defect"; it is
              the proof that this process never TERMINATES in an Element (its
              correct P4-status), consistent with the cluster's reading of
              irrationals as non-terminating processes.
    Rules:    3 is prime ⟹ 3 | n² ⟹ 3 | n (prime_mult); infinite descent on
              |p|+|q| (L5: well-ordering).

    Strategy: p² = 3·q² ⟹ 3|p ⟹ p=3p' ⟹ q² = 3·p'² ⟹ 3|q ⟹ q=3q' ⟹
    p'² = 3·q'² with (p',q') strictly smaller ⟹ descent ⟹ p=q=0.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Znumtheory.

Open Scope Z_scope.

(* ================================================================= *)
(** ** 3 is prime, and 3 | n² ⟹ 3 | n                                *)
(* ================================================================= *)

Lemma prime_3 : prime 3.
Proof.
  apply prime_intro; [ lia | ].
  intros n Hn.
  assert (Hcase : n = 1 \/ n = 2) by lia.
  destruct Hcase as [H1 | H2]; subst n;
    apply Zgcd_1_rel_prime; reflexivity.
Qed.

(** If 3 divides n*n then 3 divides n (3 is prime). *)
Lemma three_div_sq : forall n : Z, (3 | n * n) -> (3 | n).
Proof.
  intros n H.
  apply prime_mult in H.
  - destruct H; assumption.
  - exact prime_3.
Qed.

(* ================================================================= *)
(** ** p² = 3·q² ⟹ 3 | p and 3 | q                                   *)
(* ================================================================= *)

Lemma sq_eq_3sq_div3 : forall p q : Z,
  p * p = 3 * (q * q) -> (3 | p) /\ (3 | q).
Proof.
  intros p q Heq.
  assert (Hp : (3 | p)).
  { apply three_div_sq. exists (q * q). lia. }
  destruct Hp as [k Hk].   (* p = k * 3 *)
  split.
  - exists k. exact Hk.
  - apply three_div_sq.
    exists (k * k).
    (* goal: q * q = (k * k) * 3 *)
    assert (H9 : p * p = 9 * (k * k)) by (rewrite Hk; ring).
    lia.
Qed.

(* ================================================================= *)
(** ** Descent step: divide both p and q by 3                        *)
(* ================================================================= *)

Lemma descent_step_3 : forall p q : Z,
  p * p = 3 * (q * q) ->
  exists p' q' : Z,
    p = 3 * p' /\ q = 3 * q' /\ p' * p' = 3 * (q' * q').
Proof.
  intros p q Heq.
  destruct (sq_eq_3sq_div3 p q Heq) as [Hp Hq].
  destruct Hp as [p' Hp'].   (* p = p' * 3 *)
  destruct Hq as [q' Hq'].   (* q = q' * 3 *)
  exists p', q'.
  split. lia.
  split. lia.
  assert (H1 : p * p = 9 * (p' * p')) by (rewrite Hp'; ring).
  assert (H2 : q * q = 9 * (q' * q')) by (rewrite Hq'; ring).
  lia.
Qed.

(* ================================================================= *)
(** ** Infinite descent: p² = 3·q² ⟹ p = 0 and q = 0                 *)
(* ================================================================= *)

Lemma descent_to_zero_3 : forall n : nat, forall p q : Z,
  Z.to_nat (Z.abs p + Z.abs q) = n ->
  p * p = 3 * (q * q) ->
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
      destruct (descent_step_3 p q Heq) as [p' [q' [Hp' [Hq' Heq']]]].
      assert (Hlt : (Z.to_nat (Z.abs p' + Z.abs q') < n)%nat).
      { subst p q n.
        rewrite !Z.abs_mul. simpl (Z.abs 3).
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
(** ** Main theorem: sqrt(3) is irrational over Z                     *)
(* ================================================================= *)

Theorem sqrt3_irrational_Z : forall p q : Z,
  q <> 0 -> p * p <> 3 * (q * q).
Proof.
  intros p q Hq Heq.
  assert (H : p = 0 /\ q = 0).
  { apply (descent_to_zero_3 (Z.to_nat (Z.abs p + Z.abs q)) p q).
    - reflexivity.
    - exact Heq. }
  destruct H as [_ Hq0].
  contradiction.
Qed.

(* ================================================================= *)
(** ** Corollary: no rational squares to 3                            *)
(* ================================================================= *)

Open Scope Q_scope.

Theorem no_rational_sqrt3 : forall r : Q,
  ~ (r * r == 3).
Proof.
  intros r Heq.
  destruct r as [p d].
  unfold Qeq in Heq. simpl in Heq.
  (* Heq : (p * p * 1 = 3 * Z.pos (d * d))%Z *)
  assert (Heq2 : (p * p = 3 * Z.pos (d * d))%Z) by lia.
  assert (Hdd : Z.pos (d * d) = (Z.pos d * Z.pos d)%Z) by lia.
  rewrite Hdd in Heq2.
  apply (sqrt3_irrational_Z p (Z.pos d)).
  - discriminate.
  - exact Heq2.
Qed.

(** sqrt(3) is not in Q. *)
Corollary sqrt3_not_in_Q : ~ (exists r : Q, r * r == 3).
Proof.
  intros [r Hr].
  exact (no_rational_sqrt3 r Hr).
Qed.
