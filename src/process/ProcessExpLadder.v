(** * ProcessExpLadder.v -- The ladder (1 + s/n)^n: bounds, growth and the Cauchy property with an explicit modulus, as a ToS System

    Elements: the rational stages [exp1_process N] = (1 + 1/(N+1))^(N+1) and
              [expt_process s N] = (1 + s/(N+1))^(N+1) (both defined in
              ProcessExpProcess.v); natural stage numbers.
    Roles:    the stage number N -- role-resolution; the bound 3 and the bound
              (1 - s/(k0+1))^(-(k0+1)) -- role-ceiling, one for all stages;
              the gap 3/(N0+1) -- role-modulus (how close any two stages
              beyond N0 are); e and e^s -- role-limits.
    Rules:    Bernoulli's inequality for x >= -1 and its dual
              (1+x)^n (1 - n x) <= 1; the tangent bound
              x^m (x - (m+1)(x-y)) <= y^(m+1) for 0 <= y <= x.

    Proved (no axioms):
      - [exp1_upper]: (1 + 1/n)^n < 3 at every stage (via
        (1+h)^k < 1 + k h + (k h)^2 for k h <= 1; no binomial theorem);
      - [exp1_increasing]: the e-ladder strictly increases at every stage;
      - [exp1_ladder]: 2 <= stage N < stage N+1 < 3;
      - [exp1_modulus]: beyond N0 any two stages differ by less than
        3/(N0+1); [exp1_is_Cauchy]: the e-ladder is a Cauchy process;
      - [expt_lower], [expt_upper], [expt_monotone], [expt_bounded]: for
        s >= 0 the e^s-ladder is bounded below by 1 + s, does not decrease,
        and is bounded above by one number for all stages;
      - [expt_modulus], [expt_process_is_Cauchy]: for s >= 0 the e^s-ladder
        is a Cauchy process, with an explicit modulus.

    P4 diagnostic: every statement is about finite rational stages. The
      Cauchy property is a property of the process (an explicit stage number
      for every eps); no completed limit is built.

    NOT claimed:
      - a rational number that is the limit of the ladder (the number e as a
        completed object), or its irrationality;
      - the e^s-ladder for s < 0;
      - the functional equation e^(s+t) = e^s e^t, or any statement about a
        derivative.

    STATUS: 44 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessExpProcess.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. Helpers: naturals in Q, the local power qpow                      *)
(* ===================================================================== *)

Lemma inj_S : forall n : nat,
  inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1.
Proof.
  intro n. rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity.
Qed.

Lemma inj_nonneg : forall n : nat, 0 <= inject_Z (Z.of_nat n).
Proof. intro n. change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. Qed.

Lemma inj_pos : forall n : nat, (0 < n)%nat -> 0 < inject_Z (Z.of_nat n).
Proof. intros n Hn. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. Qed.

Lemma inj_le : forall m n : nat, (m <= n)%nat ->
  inject_Z (Z.of_nat m) <= inject_Z (Z.of_nat n).
Proof. intros m n H. rewrite <- Zle_Qle. lia. Qed.

(* Replicated from ProcessODEStability.v (left multiplication is monotone) *)
Lemma qmul_le_l : forall x y z, 0 <= x -> y <= z -> x * y <= x * z.
Proof.
  intros x y z Hx Hyz. rewrite (Qmult_comm x y), (Qmult_comm x z).
  apply Qmult_le_compat_r; assumption.
Qed.

(** A sequence that does not decrease step by step does not decrease. *)
Lemma inc_le_nat : forall (d : nat -> Q),
  (forall n, d n <= d (S n)) ->
  forall m n, (m <= n)%nat -> d m <= d n.
Proof.
  intros d Hinc m n Hmn. induction Hmn as [|n Hmn IH].
  - apply Qle_refl.
  - eapply Qle_trans; [ exact IH | apply Hinc ].
Qed.

(* Replicated from MonotoneConvergence.v (nat_archimedean) *)
Lemma ladder_archimedean : forall (gap eps : Q),
  0 < eps -> exists K : nat, gap < inject_Z (Z.of_nat K) * eps.
Proof.
  intros [gn gd] [en ed] Heps.
  unfold Qlt in Heps. simpl in Heps.
  assert (Hen : (en > 0)%Z) by lia.
  set (denom := (en * Z.pos gd)%Z).
  assert (Hdenom : (denom > 0)%Z) by (unfold denom; lia).
  set (numer := (gn * Z.pos ed)%Z).
  set (K := (Z.max 0 (numer / denom) + 1)%Z).
  assert (HK_pos : (K > 0)%Z) by (unfold K; lia).
  exists (Z.to_nat K).
  unfold Qlt, Qmult, inject_Z. simpl.
  rewrite Z2Nat.id by lia.
  assert (Hle : (denom * (numer / denom) <= numer)%Z)
    by (apply Z.mul_div_le; lia).
  assert (HK_ge : (K >= numer / denom + 1)%Z) by (unfold K; lia).
  assert (HK_denom : (K * denom > numer)%Z).
  { assert (Hmod := Z.div_mod numer denom ltac:(lia)).
    assert (Hmod_bound := Z.mod_pos_bound numer denom ltac:(lia)).
    nia. }
  unfold numer, denom in HK_denom. nia.
Qed.

Lemma qpow_wd : forall a b n, a == b -> qpow a n == qpow b n.
Proof.
  intros a b n E. induction n as [|n IH]; cbn [qpow]; [ reflexivity | ].
  rewrite IH, E. reflexivity.
Qed.

Lemma qpow_one : forall n, qpow 1 n == 1.
Proof. induction n as [|n IH]; cbn [qpow]; [ reflexivity | rewrite IH; ring ]. Qed.

Lemma qpow_nonneg_base : forall b n, 0 <= b -> 0 <= qpow b n.
Proof.
  intros b n Hb. induction n as [|n IH]; cbn [qpow]; [ lra | ].
  apply Qmult_le_0_compat; assumption.
Qed.

Lemma qpow_pos : forall b n, 0 < b -> 0 < qpow b n.
Proof.
  intros b n Hb. induction n as [|n IH]; cbn [qpow]; [ reflexivity | ].
  apply Qmult_lt_0_compat; assumption.
Qed.

Lemma qpow_add : forall b m n, qpow b (m + n) == qpow b m * qpow b n.
Proof.
  intros b m n. induction m as [|m IH].
  - cbn [qpow Nat.add]. ring.
  - cbn [qpow Nat.add]. rewrite IH. ring.
Qed.

Lemma qpow_mul : forall b a c, qpow b (a * c) == qpow (qpow b a) c.
Proof.
  intros b a c. induction c as [|c IH].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, qpow_add, IH. cbn [qpow]. ring.
Qed.

Lemma qpow_mult : forall (a c : Q) (n : nat), qpow (a * c) n == qpow a n * qpow c n.
Proof.
  intros a c n. induction n as [|n IH].
  - cbn [qpow]. ring.
  - cbn [qpow]. rewrite IH. ring.
Qed.

Lemma qpow_mult_distr : forall a b n, qpow a n * qpow b n == qpow (a * b) n.
Proof. intros a b n. rewrite qpow_mult. reflexivity. Qed.

Lemma qpow_le_base : forall a b n, 0 <= a -> a <= b -> qpow a n <= qpow b n.
Proof.
  intros a b n Ha Hab. induction n as [|n IH]; cbn [qpow]; [ apply Qle_refl | ].
  apply Qle_trans with (a * qpow b n).
  - apply qmul_le_l; assumption.
  - apply Qmult_le_compat_r; [ exact Hab | apply qpow_nonneg_base; lra ].
Qed.

Lemma Qsq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. destruct (Qlt_le_dec x 0) as [Hn | Hp].
  - assert (He : x * x == (- x) * (- x)) by ring.
    rewrite He. apply Qmult_le_0_compat; lra.
  - apply Qmult_le_0_compat; exact Hp.
Qed.

Lemma Qsq_pos : forall x : Q, ~ x == 0 -> 0 < x * x.
Proof.
  intros x Hx. destruct (Qlt_le_dec x 0) as [Hn | Hp].
  - assert (He : x * x == (- x) * (- x)) by ring.
    rewrite He. apply Qmult_lt_0_compat; lra.
  - assert (Hpp : 0 < x).
    { apply Qle_lteq in Hp. destruct Hp as [Hlt | Heq]; [ exact Hlt | ].
      exfalso. apply Hx. symmetry. exact Heq. }
    apply Qmult_lt_0_compat; exact Hpp.
Qed.

(* ===================================================================== *)
(*  2. Bernoulli's inequality for x >= -1, its dual and the tangent      *)
(*     bound                                                              *)
(* ===================================================================== *)

(** Bernoulli's inequality for x >= -1 (ProcessExpProcess.v has it for
    x >= 0 only). *)
Lemma bernoulli_ge_m1 : forall (x : Q) (n : nat),
  -1 <= x -> 1 + inject_Z (Z.of_nat n) * x <= qpow (1 + x) n.
Proof.
  intros x n Hx. induction n as [|k IH].
  - cbn [qpow]. change (inject_Z (Z.of_nat 0)) with 0.
    assert (He : 1 + 0 * x == 1) by ring. rewrite He. apply Qle_refl.
  - cbn [qpow]. rewrite (inj_S k).
    pose proof (inj_nonneg k) as Hm.
    set (m := inject_Z (Z.of_nat k)) in *.
    assert (H1x : 0 <= 1 + x) by lra.
    assert (Hstep : (1 + x) * (1 + m * x) <= (1 + x) * qpow (1 + x) k).
    { rewrite (Qmult_comm (1 + x) (1 + m * x)), (Qmult_comm (1 + x) (qpow (1 + x) k)).
      apply Qmult_le_compat_r; [ exact IH | exact H1x ]. }
    assert (Hsq : 0 <= m * (x * x)).
    { apply Qmult_le_0_compat; [ exact Hm | apply Qsq_nonneg ]. }
    assert (He : (1 + x) * (1 + m * x) == 1 + (m + 1) * x + m * (x * x)) by ring.
    lra.
Qed.

(** The strict form: exponent at least two, x <> 0. *)
Lemma bernoulli_strict : forall (x : Q) (n : nat),
  -1 <= x -> ~ x == 0 ->
  1 + inject_Z (Z.of_nat (S (S n))) * x < qpow (1 + x) (S (S n)).
Proof.
  intros x n Hx Hne.
  pose proof (bernoulli_ge_m1 x (S n) Hx) as HB.
  change (qpow (1 + x) (S (S n))) with ((1 + x) * qpow (1 + x) (S n)).
  rewrite (inj_S (S n)).
  pose proof (inj_pos (S n) ltac:(lia)) as Hm.
  set (m := inject_Z (Z.of_nat (S n))) in *.
  assert (H1x : 0 <= 1 + x) by lra.
  assert (Hstep : (1 + x) * (1 + m * x) <= (1 + x) * qpow (1 + x) (S n)).
  { rewrite (Qmult_comm (1 + x) (1 + m * x)), (Qmult_comm (1 + x) (qpow (1 + x) (S n))).
    apply Qmult_le_compat_r; [ exact HB | exact H1x ]. }
  assert (Hsq : 0 < m * (x * x)).
  { apply Qmult_lt_0_compat; [ exact Hm | apply Qsq_pos; exact Hne ]. }
  assert (He : (1 + x) * (1 + m * x) == 1 + (m + 1) * x + m * (x * x)) by ring.
  lra.
Qed.

(** The bound dual to Bernoulli's inequality. *)
Lemma qpow_bernoulli_upper : forall x n, 0 <= x ->
  qpow (1 + x) n * (1 - inject_Z (Z.of_nat n) * x) <= 1.
Proof.
  intros x n Hx. induction n as [|n IH].
  - cbn [qpow]. change (inject_Z (Z.of_nat 0)) with 0.
    assert (E : 1 * (1 - 0 * x) == 1) by ring. rewrite E. apply Qle_refl.
  - cbn [qpow].
    assert (HS : inject_Z (Z.of_nat (S n)) == inject_Z (Z.of_nat n) + 1).
    { rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity. }
    rewrite HS.
    assert (Hm : 0 <= inject_Z (Z.of_nat n)).
    { change 0 with (inject_Z 0). rewrite <- Zle_Qle. lia. }
    set (m := inject_Z (Z.of_nat n)) in *.
    assert (Hp : 0 <= qpow (1 + x) n) by (apply qpow_nonneg_base; lra).
    set (P := qpow (1 + x) n) in *.
    assert (E : (1 + x) * P * (1 - (m + 1) * x)
                == P * (1 - m * x) - P * ((m + 1) * x * x)) by ring.
    rewrite E.
    assert (Hq : 0 <= P * ((m + 1) * x * x)).
    { apply Qmult_le_0_compat; [ exact Hp | ].
      apply Qmult_le_0_compat; [ apply Qmult_le_0_compat; lra | exact Hx ]. }
    lra.
Qed.

(** The power is bounded by a number that does not depend on the exponent:
    if n x <= s < 1 then (1 + x)^n <= 1/(1 - s). *)
Corollary qpow_uniform_bound : forall x n s,
  0 <= x -> inject_Z (Z.of_nat n) * x <= s -> s < 1 ->
  qpow (1 + x) n <= 1 / (1 - s).
Proof.
  intros x n s Hx Hs Hs1.
  pose proof (qpow_bernoulli_upper x n Hx) as Hb.
  assert (Hp : 0 <= qpow (1 + x) n) by (apply qpow_nonneg_base; lra).
  set (P := qpow (1 + x) n) in *.
  assert (H1 : P * (1 - s) <= 1).
  { apply Qle_trans with (P * (1 - inject_Z (Z.of_nat n) * x)); [ | exact Hb ].
    apply qmul_le_l; [ exact Hp | lra ]. }
  apply Qle_shift_div_l; [ lra | exact H1 ].
Qed.

(** The tangent bound from below (at x = 1 it is Bernoulli's inequality for
    the base 1 - t, 0 <= t <= 1). *)
Lemma qpow_lower_tangent : forall x y m, 0 <= y -> y <= x ->
  qpow x m * (x - (inject_Z (Z.of_nat m) + 1) * (x - y)) <= qpow y (S m).
Proof.
  intros x y m Hy Hyx. induction m as [|m IH].
  - cbn [qpow]. change (inject_Z (Z.of_nat 0)) with 0.
    assert (E : 1 * (x - (0 + 1) * (x - y)) == y * 1) by ring.
    rewrite E. apply Qle_refl.
  - rewrite inj_S.
    pose proof (inj_nonneg m) as Hmq.
    set (mq := inject_Z (Z.of_nat m)) in *.
    assert (Hx : 0 <= x) by lra.
    assert (Hp : 0 <= qpow x m) by (apply qpow_nonneg_base; exact Hx).
    change (qpow y (S (S m))) with (y * qpow y (S m)).
    change (qpow x (S m)) with (x * qpow x m).
    apply Qle_trans with (y * (qpow x m * (x - (mq + 1) * (x - y)))).
    + set (P := qpow x m) in *.
      assert (E : y * (P * (x - (mq + 1) * (x - y)))
                  - x * P * (x - (mq + 1 + 1) * (x - y))
                  == P * ((mq + 1) * ((x - y) * (x - y)))) by ring.
      assert (Hq : 0 <= P * ((mq + 1) * ((x - y) * (x - y)))).
      { apply Qmult_le_0_compat; [ exact Hp | ].
        apply Qmult_le_0_compat; [ lra | ].
        apply Qmult_le_0_compat; lra. }
      lra.
    + apply qmul_le_l; [ exact Hy | exact IH ].
Qed.

(** (1+h)^k < 1 + k h + (k h)^2 for k >= 1, h > 0, k h <= 1. *)
Lemma quad_step : forall h m P : Q,
  0 < h -> 0 <= m -> m * h <= 1 ->
  P < 1 + m * h + (m * h) * (m * h) ->
  (1 + h) * P < 1 + (m + 1) * h + ((m + 1) * h) * ((m + 1) * h).
Proof.
  intros h m P Hh Hm Hmh HP.
  assert (H1 : (1 + h) * P < (1 + h) * (1 + m * h + (m * h) * (m * h))).
  { apply Qmult_lt_l; [ lra | exact HP ]. }
  assert (Hd : 1 + (m + 1) * h + ((m + 1) * h) * ((m + 1) * h)
               - (1 + h) * (1 + m * h + (m * h) * (m * h))
               == h * h * (1 + m * (1 - m * h))) by ring.
  assert (Hnn : 0 <= h * h * (1 + m * (1 - m * h))).
  { apply Qmult_le_0_compat.
    - apply Qmult_le_0_compat; lra.
    - assert (0 <= m * (1 - m * h)) by (apply Qmult_le_0_compat; lra). lra. }
  lra.
Qed.

Lemma qpow_quad_strict : forall (h : Q) (k : nat),
  0 < h ->
  inject_Z (Z.of_nat (S k)) * h <= 1 ->
  qpow (1 + h) (S k) <
  1 + inject_Z (Z.of_nat (S k)) * h
    + (inject_Z (Z.of_nat (S k)) * h) * (inject_Z (Z.of_nat (S k)) * h).
Proof.
  intros h k Hh. induction k as [|k IH]; intro Hb.
  - cbn [qpow]. change (inject_Z (Z.of_nat 1)) with 1.
    assert (Hhh : 0 < h * h) by (apply Qmult_lt_0_compat; exact Hh).
    assert (He : 1 + 1 * h + 1 * h * (1 * h) - (1 + h) * 1 == h * h) by ring.
    lra.
  - pose proof (inj_S (S k)) as Hs.
    pose proof (inj_nonneg (S k)) as Hm.
    assert (Hmh : inject_Z (Z.of_nat (S k)) * h <= 1).
    { rewrite Hs in Hb.
      assert (Hx : (inject_Z (Z.of_nat (S k)) + 1) * h
                   == inject_Z (Z.of_nat (S k)) * h + h) by ring.
      rewrite Hx in Hb. lra. }
    specialize (IH Hmh).
    change (qpow (1 + h) (S (S k))) with ((1 + h) * qpow (1 + h) (S k)).
    rewrite Hs.
    apply quad_step; assumption.
Qed.

(* ===================================================================== *)
(*  3. The e^s-ladder (1 + s/n)^n for s >= 0: bounds and growth          *)
(* ===================================================================== *)

Lemma expt_at_one : forall k, expt_process 1 k = exp1_process k.
Proof. reflexivity. Qed.

Lemma expt_at_zero : forall k, expt_process 0 k == 1.
Proof.
  intro k. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  assert (E : 1 + 0 / inject_Z (Z.of_nat (S k)) == 1) by (field; lra).
  rewrite (qpow_wd _ _ (S k) E). apply qpow_one.
Qed.

Lemma expt_nonneg : forall s k, 0 <= s -> 0 <= expt_process s k.
Proof.
  intros s k Hs. unfold expt_process. apply qpow_nonneg_base.
  pose proof (exp1_pos_denom k) as Hd.
  assert (0 <= s / inject_Z (Z.of_nat (S k))).
  { apply Qle_shift_div_l; [ exact Hd | ].
    assert (E0 : 0 * inject_Z (Z.of_nat (S k)) == 0) by ring. rewrite E0. exact Hs. }
  lra.
Qed.

(** The bound from below (Bernoulli): 1 + s <= (1 + s/n)^n. *)
Lemma expt_lower : forall s k, 0 <= s -> 1 + s <= expt_process s k.
Proof.
  intros s k Hs. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hx : 0 <= s / d).
  { apply Qle_shift_div_l; [ exact Hd | ].
    assert (E : 0 * d == 0) by ring. rewrite E. exact Hs. }
  pose proof (bernoulli_nonneg (s / d) (S k) Hx) as HB. fold d in HB.
  assert (E : 1 + d * (s / d) == 1 + s) by (field; lra).
  rewrite E in HB. exact HB.
Qed.

(** The bound from above for 0 <= s < 1, one for all stages. *)
Lemma expt_upper : forall s k, 0 <= s -> s < 1 -> expt_process s k <= 1 / (1 - s).
Proof.
  intros s k Hs Hs1. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (Hx : 0 <= s / d).
  { apply Qle_shift_div_l; [ exact Hd | ].
    assert (E : 0 * d == 0) by ring. rewrite E. exact Hs. }
  apply (qpow_uniform_bound (s / d) (S k) s Hx); [ | exact Hs1 ].
  fold d. assert (E : d * (s / d) == s) by (field; lra). rewrite E. apply Qle_refl.
Qed.

(** The ladder does not decrease: (1 + s/n)^n <= (1 + s/(n+1))^(n+1), s >= 0. *)
Lemma expt_monotone : forall s k, 0 <= s -> expt_process s k <= expt_process s (S k).
Proof.
  intros s k Hs. unfold expt_process.
  pose proof (exp1_pos_denom k) as Hd.
  assert (Eb : qpow (1 + s / inject_Z (Z.of_nat (S (S k)))) (S (S k))
               == qpow (1 + s / (inject_Z (Z.of_nat (S k)) + 1)) (S (S k))).
  { apply qpow_wd. rewrite (inj_S (S k)). reflexivity. }
  rewrite Eb.
  set (d := inject_Z (Z.of_nat (S k))) in *.
  assert (E2 : s / d - s / (d + 1) == s / (d * (d + 1))) by (field; lra).
  assert (Hdd : 0 < d * (d + 1)) by (apply Qmult_lt_0_compat; lra).
  assert (H2 : 0 <= s / (d * (d + 1))).
  { apply Qle_shift_div_l; [ exact Hdd | ].
    assert (E0 : 0 * (d * (d + 1)) == 0) by ring. rewrite E0. exact Hs. }
  assert (H3 : 0 <= s / (d + 1)).
  { apply Qle_shift_div_l; [ lra | ].
    assert (E0 : 0 * (d + 1) == 0) by ring. rewrite E0. exact Hs. }
  set (x := 1 + s / d). set (y := 1 + s / (d + 1)).
  assert (Hy : 0 <= y) by (unfold y; lra).
  assert (Hyx : y <= x) by (unfold x, y; lra).
  pose proof (qpow_lower_tangent x y (S k) Hy Hyx) as HT. fold d in HT.
  assert (E : x - (d + 1) * (x - y) == 1) by (unfold x, y; field; lra).
  rewrite E in HT.
  assert (E1 : qpow x (S k) * 1 == qpow x (S k)) by ring.
  rewrite E1 in HT. exact HT.
Qed.

Lemma expt_monotone_le : forall s m n, 0 <= s -> (m <= n)%nat ->
  expt_process s m <= expt_process s n.
Proof.
  intros s m n Hs Hmn.
  apply (inc_le_nat (expt_process s)); [ | exact Hmn ].
  intro j. apply expt_monotone; exact Hs.
Qed.

(** Every stage (1 + s/m)^m times (1 - s/n)^n is at most one (n > s): the
    stages are bounded above by the number (1 - s/n)^(-n). *)
Lemma expt_times_companion : forall s m k, 0 <= s -> s < inject_Z (Z.of_nat (S k)) ->
  expt_process s m * qpow (1 - s / inject_Z (Z.of_nat (S k))) (S k) <= 1.
Proof.
  intros s m k Hs Hsk.
  pose proof (exp1_pos_denom k) as Hdk. pose proof (exp1_pos_denom m) as Hdm.
  set (dk := inject_Z (Z.of_nat (S k))) in *.
  set (dm := inject_Z (Z.of_nat (S m))) in *.
  set (c := 1 - s / dk).
  assert (Hsdk : s / dk < 1).
  { apply Qlt_shift_div_r; [ exact Hdk | lra ]. }
  assert (Hsdk0 : 0 <= s / dk).
  { apply Qle_shift_div_l; [ exact Hdk | ].
    assert (E0 : 0 * dk == 0) by ring. rewrite E0. exact Hs. }
  assert (Hc : 0 < c) by (unfold c; lra).
  assert (Hcn : 0 <= qpow c (S k)) by (apply qpow_nonneg_base; lra).
  set (j := (S m * k + m)%nat).
  assert (HSj : S j = (S m * S k)%nat) by (unfold j; rewrite Nat.mul_succ_r; lia).
  assert (Hmj : (m <= j)%nat) by (unfold j; lia).
  apply Qle_trans with (expt_process s j * qpow c (S k)).
  { apply Qmult_le_compat_r; [ apply expt_monotone_le; assumption | exact Hcn ]. }
  unfold expt_process. rewrite HSj.
  assert (Einj : inject_Z (Z.of_nat (S m * S k)) == dm * dk).
  { unfold dm, dk. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity. }
  set (x := s / (dm * dk)).
  assert (Hdmk : 0 < dm * dk) by (apply Qmult_lt_0_compat; assumption).
  assert (Hx : 0 <= x).
  { unfold x. apply Qle_shift_div_l; [ exact Hdmk | ].
    assert (E0 : 0 * (dm * dk) == 0) by ring. rewrite E0. exact Hs. }
  assert (Eb : qpow (1 + s / inject_Z (Z.of_nat (S m * S k))) (S m * S k)
               == qpow (qpow (1 + x) (S m)) (S k)).
  { rewrite <- qpow_mul. apply qpow_wd. unfold x. rewrite Einj. reflexivity. }
  rewrite Eb.
  pose proof (qpow_bernoulli_upper x (S m) Hx) as HU. fold dm in HU.
  assert (Ec : 1 - dm * x == c) by (unfold x, c; field; lra).
  rewrite Ec in HU.
  set (P := qpow (1 + x) (S m)) in *.
  assert (HP : 0 <= P) by (unfold P; apply qpow_nonneg_base; lra).
  rewrite qpow_mult_distr.
  rewrite <- (qpow_one (S k)).
  apply qpow_le_base; [ apply Qmult_le_0_compat; lra | exact HU ].
Qed.

(** The key inequality without division: a_m (1 - s^2/n) <= a_n for n > s. *)
Lemma expt_gap_one_sided : forall s m k, 0 <= s -> s < inject_Z (Z.of_nat (S k)) ->
  expt_process s m * (1 - s * s / inject_Z (Z.of_nat (S k))) <= expt_process s k.
Proof.
  intros s m k Hs Hsk.
  pose proof (exp1_pos_denom k) as Hdk.
  pose proof (expt_times_companion s m k Hs Hsk) as HC.
  pose proof (expt_nonneg s m Hs) as Ham.
  pose proof (expt_nonneg s k Hs) as Hak.
  set (dk := inject_Z (Z.of_nat (S k))) in *.
  set (c := 1 - s / dk) in *. set (b := 1 + s / dk).
  set (y := 1 - s * s / (dk * dk)).
  assert (Hdd : 0 < dk * dk) by (apply Qmult_lt_0_compat; assumption).
  assert (Hss : 0 <= s * s) by (apply Qmult_le_0_compat; assumption).
  assert (Hss2 : s * s <= dk * dk).
  { apply Qle_trans with (dk * s).
    - apply Qmult_le_compat_r; lra.
    - apply qmul_le_l; lra. }
  assert (Hq0 : 0 <= s * s / (dk * dk)).
  { apply Qle_shift_div_l; [ exact Hdd | ].
    assert (E0 : 0 * (dk * dk) == 0) by ring. rewrite E0. exact Hss. }
  assert (Hq1 : s * s / (dk * dk) <= 1).
  { apply Qle_shift_div_r; [ exact Hdd | lra ]. }
  assert (Hy0 : 0 <= y) by (unfold y; lra).
  assert (Hy1 : y <= 1) by (unfold y; lra).
  pose proof (qpow_lower_tangent 1 y k Hy0 Hy1) as HT.
  assert (Ed : inject_Z (Z.of_nat k) + 1 == dk) by (unfold dk; rewrite inj_S; reflexivity).
  rewrite Ed, qpow_one in HT.
  assert (Et : 1 * (1 - dk * (1 - y)) == 1 - s * s / dk) by (unfold y; field; lra).
  rewrite Et in HT.
  assert (Ey : y == b * c) by (unfold y, b, c; field; lra).
  rewrite (qpow_wd _ _ (S k) Ey) in HT.
  rewrite <- qpow_mult_distr in HT.
  change (qpow b (S k)) with (expt_process s k) in HT.
  set (ak := expt_process s k) in *. set (am := expt_process s m) in *.
  set (C := qpow c (S k)) in *.
  apply Qle_trans with (am * (ak * C)).
  - apply qmul_le_l; assumption.
  - assert (E3 : am * (ak * C) == (am * C) * ak) by ring. rewrite E3.
    apply Qle_trans with (1 * ak); [ apply Qmult_le_compat_r; assumption | ].
    assert (E4 : 1 * ak == ak) by ring. rewrite E4. apply Qle_refl.
Qed.

(** One upper bound for all stages (for every s >= 0). *)
Lemma expt_bounded : forall s m k0, 0 <= s -> s < inject_Z (Z.of_nat (S k0)) ->
  expt_process s m <= 1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0).
Proof.
  intros s m k0 Hs Hk0.
  pose proof (exp1_pos_denom k0) as Hd.
  assert (Hc : 0 < 1 - s / inject_Z (Z.of_nat (S k0))).
  { assert (s / inject_Z (Z.of_nat (S k0)) < 1)
      by (apply Qlt_shift_div_r; [ exact Hd | lra ]).
    lra. }
  apply Qle_shift_div_l; [ apply qpow_pos; exact Hc | ].
  apply expt_times_companion; assumption.
Qed.

(* ===================================================================== *)
(*  4. The e^s-ladder is a Cauchy process, with an explicit modulus      *)
(* ===================================================================== *)

(** For n >= k0, where k0 + 1 > s, and for every m:
    a_m - a_n <= B s^2 / (n + 1),   B = (1 - s/(k0+1))^(-(k0+1)). *)
Theorem expt_modulus : forall s k0, 0 <= s -> s < inject_Z (Z.of_nat (S k0)) ->
  forall m n, (k0 <= n)%nat ->
  expt_process s m - expt_process s n
  <= 1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0)
     * (s * s / inject_Z (Z.of_nat (S n))).
Proof.
  intros s k0 Hs Hk0 m n Hn.
  assert (Hsn : s < inject_Z (Z.of_nat (S n))).
  { eapply Qlt_le_trans; [ exact Hk0 | apply inj_le; lia ]. }
  pose proof (expt_gap_one_sided s m n Hs Hsn) as HG.
  pose proof (expt_bounded s m k0 Hs Hk0) as HB.
  pose proof (expt_nonneg s m Hs) as Ham.
  pose proof (exp1_pos_denom n) as Hdn.
  set (dn := inject_Z (Z.of_nat (S n))) in *.
  set (B := 1 / qpow (1 - s / inject_Z (Z.of_nat (S k0))) (S k0)) in *.
  assert (Hq : 0 <= s * s / dn).
  { apply Qle_shift_div_l; [ exact Hdn | ].
    assert (E0 : 0 * dn == 0) by ring. rewrite E0.
    apply Qmult_le_0_compat; assumption. }
  assert (H1 : expt_process s m * (s * s / dn) <= B * (s * s / dn))
    by (apply Qmult_le_compat_r; assumption).
  assert (E : expt_process s m * (1 - s * s / dn)
              == expt_process s m - expt_process s m * (s * s / dn)) by ring.
  rewrite E in HG. lra.
Qed.

(** (1 + s/n)^n is a Cauchy process for every s >= 0. *)
Theorem expt_process_is_Cauchy : forall s, 0 <= s -> is_Cauchy (expt_process s).
Proof.
  intros s Hs eps Heps.
  assert (H01 : 0 < 1) by lra.
  destruct (ladder_archimedean s 1 H01) as [K0 HK0].
  assert (Hk0 : s < inject_Z (Z.of_nat (S K0))).
  { rewrite inj_S. lra. }
  set (B := 1 / qpow (1 - s / inject_Z (Z.of_nat (S K0))) (S K0)).
  destruct (ladder_archimedean (B * (s * s)) eps Heps) as [K2 HK2].
  exists (Nat.max K0 K2). intros m n Hm Hn.
  assert (key : forall a b, (Nat.max K0 K2 <= b)%nat ->
                  expt_process s a - expt_process s b < eps).
  { intros a b Hb.
    eapply Qle_lt_trans; [ apply (expt_modulus s K0 Hs Hk0 a b); lia | ].
    fold B.
    pose proof (exp1_pos_denom b) as Hdb.
    assert (Hdb2 : inject_Z (Z.of_nat K2) <= inject_Z (Z.of_nat (S b)))
      by (apply inj_le; lia).
    set (db := inject_Z (Z.of_nat (S b))) in *.
    assert (E : B * (s * s / db) == B * (s * s) / db) by (field; lra).
    rewrite E. apply Qlt_shift_div_r; [ exact Hdb | ].
    eapply Qlt_le_trans; [ exact HK2 | ].
    rewrite (Qmult_comm eps db). apply Qmult_le_compat_r; lra. }
  apply Qabs_case; intros _.
  - apply key; lia.
  - assert (E : - (expt_process s m - expt_process s n)
                == expt_process s n - expt_process s m) by ring.
    rewrite E. apply key; lia.
Qed.

(* ===================================================================== *)
(*  5. The e-ladder (1 + 1/n)^n: below three, strictly increasing,       *)
(*     Cauchy with the modulus 3/(N0+1)                                   *)
(* ===================================================================== *)

(** The e-ladder is below three at every stage. *)
Theorem exp1_upper : forall N : nat, exp1_process N < 3.
Proof.
  intro N. unfold exp1_process.
  pose proof (exp1_pos_denom N) as Hd.
  remember (inject_Z (Z.of_nat (S N))) as d eqn:Hde.
  assert (Hh : 0 < 1 / d).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hd. }
  assert (Hdh : d * (1 / d) == 1) by (field; lra).
  pose proof (qpow_quad_strict (1 / d) N Hh) as HB.
  rewrite <- Hde in HB.
  assert (Hb : d * (1 / d) <= 1) by (rewrite Hdh; apply Qle_refl).
  specialize (HB Hb). rewrite Hdh in HB. lra.
Qed.

Lemma mono_core : forall (d : Q) (n : nat),
  0 < d ->
  inject_Z (Z.of_nat (S (S n))) == d + 1 ->
  qpow (1 + 1 / d) (S n) < qpow (1 + 1 / (d + 1)) (S (S n)).
Proof.
  intros d n Hd Hinj.
  set (a := 1 + 1 / d).
  set (x := - (1 / ((d + 1) * (d + 1)))).
  assert (He1 : (d + 1) * (d + 1) == 1 + d * (d + 2)) by ring.
  assert (Hdd : 0 <= d * (d + 2)) by (apply Qmult_le_0_compat; lra).
  assert (Hepos : 0 < (d + 1) * (d + 1)) by lra.
  assert (Hinv : 0 < 1 / ((d + 1) * (d + 1))).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hepos. }
  assert (Hinv1 : 1 / ((d + 1) * (d + 1)) <= 1).
  { apply Qle_shift_div_r; [ exact Hepos | lra ]. }
  assert (Hx : -1 <= x) by (unfold x; lra).
  assert (Hne : ~ x == 0) by (unfold x; intro Hc; lra).
  assert (Hapos : 0 < a).
  { unfold a. assert (0 < 1 / d).
    { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. exact Hd. }
    lra. }
  assert (Hb : 1 + 1 / (d + 1) == a * (1 + x)).
  { unfold a, x. field. split; lra. }
  assert (Hr : a * (1 + (d + 1) * x) == 1).
  { unfold a, x. field. split; lra. }
  pose proof (bernoulli_strict x n Hx Hne) as HBs.
  rewrite Hinj in HBs.
  set (A := qpow a (S n)).
  assert (HA : 0 < A) by (unfold A; apply qpow_pos; exact Hapos).
  set (Bx := qpow (1 + x) (S (S n))) in *.
  assert (Hq : qpow (1 + 1 / (d + 1)) (S (S n)) == (a * A) * Bx).
  { rewrite (qpow_wd _ _ (S (S n)) Hb), qpow_mult.
    change (qpow a (S (S n))) with (a * qpow a (S n)). reflexivity. }
  assert (HaA : 0 < a * A) by (apply Qmult_lt_0_compat; assumption).
  assert (H1 : (a * A) * (1 + (d + 1) * x) < (a * A) * Bx).
  { apply Qmult_lt_l; [ exact HaA | exact HBs ]. }
  assert (H2 : (a * A) * (1 + (d + 1) * x) == A).
  { transitivity (A * (a * (1 + (d + 1) * x))); [ ring | rewrite Hr; ring ]. }
  rewrite Hq. rewrite H2 in H1. exact H1.
Qed.

(** The e-ladder strictly increases at every stage. *)
Theorem exp1_increasing : forall N : nat, exp1_process N < exp1_process (S N).
Proof.
  intro N. unfold exp1_process.
  pose proof (exp1_pos_denom N) as Hd.
  pose proof (inj_S (S N)) as Hs.
  apply Qlt_le_trans with
    (qpow (1 + 1 / (inject_Z (Z.of_nat (S N)) + 1)) (S (S N))).
  - apply mono_core; [ exact Hd | exact Hs ].
  - apply Qle_lteq. right. apply qpow_wd. rewrite Hs. reflexivity.
Qed.

(** Summary: the ladder (1 + 1/n)^n increases and lies between 2 and 3. *)
Theorem exp1_ladder : forall N : nat,
  2 <= exp1_process N /\ exp1_process N < exp1_process (S N) /\ exp1_process (S N) < 3.
Proof.
  intro N. split; [ apply exp1_lower | split; [ apply exp1_increasing | apply exp1_upper ] ].
Qed.

(** One-sided gap: any stage exceeds a stage n >= 1 by less than 3/(n+1). *)
Lemma exp1_gap : forall m n : nat, (1 <= n)%nat ->
  exp1_process m - exp1_process n < 3 / inject_Z (Z.of_nat (S n)).
Proof.
  intros m n Hn.
  assert (Hs : 0 <= 1) by lra.
  assert (Hsn : 1 < inject_Z (Z.of_nat (S n))).
  { rewrite inj_S. pose proof (inj_pos n ltac:(lia)) as Hp. lra. }
  pose proof (expt_gap_one_sided 1 m n Hs Hsn) as HG.
  change (expt_process 1 m) with (exp1_process m) in HG.
  change (expt_process 1 n) with (exp1_process n) in HG.
  pose proof (exp1_upper m) as Hu.
  pose proof (exp1_pos_denom n) as Hd.
  set (d := inject_Z (Z.of_nat (S n))) in *.
  set (a := exp1_process m) in *. set (b := exp1_process n) in *.
  assert (E : a * (1 - 1 * 1 / d) == a - a / d) by (field; lra).
  rewrite E in HG.
  assert (H3 : a / d < 3 / d).
  { unfold Qdiv. apply Qmult_lt_compat_r; [ apply Qinv_lt_0_compat; exact Hd | exact Hu ]. }
  set (q := a / d) in *. set (r := 3 / d) in *. lra.
Qed.

(** The explicit modulus: beyond the stage N0 any two stages of the e-ladder
    differ by less than 3/(N0+1). *)
Theorem exp1_modulus : forall N0 m n : nat, (N0 <= m)%nat -> (N0 <= n)%nat ->
  Qabs (exp1_process m - exp1_process n) < 3 / inject_Z (Z.of_nat (S N0)).
Proof.
  intros N0 m n Hm Hn. destruct N0 as [|N1].
  - pose proof (exp1_lower m) as Lm. pose proof (exp1_upper m) as Um.
    pose proof (exp1_lower n) as Ln. pose proof (exp1_upper n) as Un.
    change (inject_Z (Z.of_nat 1)) with 1.
    assert (E : 3 / 1 == 3) by reflexivity. rewrite E.
    apply Qabs_case; intros _; lra.
  - pose proof (exp1_pos_denom (S N1)) as Hd0.
    assert (key : forall a b : nat, (S N1 <= b)%nat ->
              exp1_process a - exp1_process b < 3 / inject_Z (Z.of_nat (S (S N1)))).
    { intros a b Hb.
      eapply Qlt_le_trans; [ apply (exp1_gap a b); lia | ].
      pose proof (exp1_pos_denom b) as Hdb.
      assert (Hle : inject_Z (Z.of_nat (S (S N1))) <= inject_Z (Z.of_nat (S b)))
        by (apply inj_le; lia).
      set (d0 := inject_Z (Z.of_nat (S (S N1)))) in *.
      set (db := inject_Z (Z.of_nat (S b))) in *.
      apply Qle_shift_div_l; [ exact Hd0 | ].
      assert (E : 3 / db * d0 == 3 * d0 / db) by (field; lra).
      rewrite E. apply Qle_shift_div_r; [ exact Hdb | lra ]. }
    apply Qabs_case; intros _.
    + apply key; lia.
    + assert (E : - (exp1_process m - exp1_process n)
                  == exp1_process n - exp1_process m) by ring.
      rewrite E. apply key; lia.
Qed.

(** The e-ladder is a Cauchy process. *)
Theorem exp1_is_Cauchy : is_Cauchy exp1_process.
Proof.
  intros eps Heps.
  destruct (ladder_archimedean 3 eps Heps) as [K HK].
  exists K. intros m n Hm Hn.
  eapply Qlt_trans; [ apply (exp1_modulus K m n Hm Hn) | ].
  pose proof (exp1_pos_denom K) as Hd.
  pose proof (inj_S K) as HS.
  set (dK := inject_Z (Z.of_nat (S K))) in *.
  set (k := inject_Z (Z.of_nat K)) in *.
  apply Qlt_shift_div_r; [ exact Hd | ].
  assert (Hle : k * eps <= dK * eps).
  { apply Qmult_le_compat_r; [ rewrite HS; lra | lra ]. }
  rewrite (Qmult_comm eps dK). lra.
Qed.
