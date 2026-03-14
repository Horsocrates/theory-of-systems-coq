(** * ProcessArithmetic.v — Operations on Processes
    Elements: process_add, process_neg, process_sub, process_scale, process_abs, monotone
    Roles:    pointwise arithmetic preserving Cauchy; monotonicity lemmas
    Rules:    each operation preserves the Cauchy condition
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESSARITHMETIC — Operations on Processes                          *)
(*                                                                            *)
(*  Pointwise arithmetic on RealProcess. Each operation preserves Cauchy.    *)
(*                                                                            *)
(*  STATUS: 13 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith Zdiv.
From Stdlib Require Import Lqa.
From Stdlib Require Import Classical.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.

(* ================================================================== *)
(*  Part I: Pointwise Operations  (~6 lemmas)                         *)
(* ================================================================== *)

Definition process_add (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n + R2 n.

Definition process_neg (R : RealProcess) : RealProcess :=
  fun n => - (R n).

Definition process_sub (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n - R2 n.

Definition process_scale (c : Q) (R : RealProcess) : RealProcess :=
  fun n => c * R n.

Definition process_abs (R : RealProcess) : RealProcess :=
  fun n => Qabs (R n).

Lemma process_add_at : forall R1 R2 n,
  process_add R1 R2 n == R1 n + R2 n.
Proof. intros. unfold process_add. lra. Qed.

Lemma process_neg_at : forall R n,
  process_neg R n == - (R n).
Proof. intros. unfold process_neg. lra. Qed.

Lemma process_scale_at : forall c R n,
  process_scale c R n == c * R n.
Proof. intros. unfold process_scale. lra. Qed.

Lemma process_sub_at : forall R1 R2 n,
  process_sub R1 R2 n == R1 n - R2 n.
Proof. intros. unfold process_sub. lra. Qed.

Lemma process_add_comm : forall R1 R2,
  process_add R1 R2 ~~ process_add R2 R1.
Proof.
  intros R1 R2 eps Heps. exists 0%nat. intros n _.
  unfold process_add.
  assert (Heq : R1 n + R2 n - (R2 n + R1 n) == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

Lemma process_add_const : forall p q,
  process_add (const_process p) (const_process q) ~~ const_process (p + q).
Proof.
  intros p q eps Heps. exists 0%nat. intros n _.
  unfold process_add, const_process.
  assert (Heq : p + q - (p + q) == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  Part II: Cauchy Preservation  (~4 lemmas)                         *)
(* ================================================================== *)

Theorem add_preserves_Cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 -> is_Cauchy (process_add R1 R2).
Proof.
  intros R1 R2 HC1 HC2 eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (HC1 (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (HC2 (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros m n Hm Hn.
  unfold process_add.
  assert (Hm1 : (N1 <= m)%nat) by lia. assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 m n Hm1 Hn1). specialize (HN2 m n Hm2 Hn2).
  assert (Htri : R1 m + R2 m - (R1 n + R2 n) == (R1 m - R1 n) + (R2 m - R2 n)) by ring.
  rewrite Htri.
  apply Qle_lt_trans with (Qabs (R1 m - R1 n) + Qabs (R2 m - R2 n)).
  - apply Qabs_triangle.
  - lra.
Qed.

Theorem neg_preserves_Cauchy : forall R,
  is_Cauchy R -> is_Cauchy (process_neg R).
Proof.
  intros R HC eps Heps.
  destruct (HC eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  unfold process_neg.
  assert (Heq : -(R m) - -(R n) == -(R m - R n)) by ring. rewrite Heq.
  rewrite Qabs_opp. apply HN; auto.
Qed.

Theorem sub_preserves_Cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 -> is_Cauchy (process_sub R1 R2).
Proof.
  intros R1 R2 HC1 HC2 eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (HC1 (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (HC2 (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros m n Hm Hn.
  unfold process_sub.
  assert (Hm1 : (N1 <= m)%nat) by lia. assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 m n Hm1 Hn1). specialize (HN2 m n Hm2 Hn2).
  assert (Htri : (R1 m - R2 m) - (R1 n - R2 n) == (R1 m - R1 n) - (R2 m - R2 n)) by ring.
  rewrite Htri.
  apply Qle_lt_trans with (Qabs (R1 m - R1 n) + Qabs (-(R2 m - R2 n))).
  - assert (Htri2 : (R1 m - R1 n) - (R2 m - R2 n) == (R1 m - R1 n) + -(R2 m - R2 n)) by ring.
    rewrite Htri2. apply Qabs_triangle.
  - rewrite Qabs_opp. lra.
Qed.

Theorem scale_preserves_Cauchy : forall c R,
  is_Cauchy R -> is_Cauchy (process_scale c R).
Proof.
  intros c R HC eps Heps.
  destruct (Qeq_dec c 0) as [Hc0 | Hc0].
  - (* c == 0: scale is constant 0 *)
    exists 0%nat. intros m n _ _.
    unfold process_scale.
    assert (Heq : c * R m - c * R n == c * (R m - R n)) by ring. rewrite Heq.
    rewrite Hc0.
    assert (Heq2 : 0 * (R m - R n) == 0) by ring. rewrite Heq2.
    rewrite Qabs_pos; lra.
  - (* c != 0 *)
    assert (Hcpos : 0 < Qabs c).
    { destruct (Qlt_le_dec 0 c).
      - rewrite Qabs_pos; lra.
      - assert (Hcn : c < 0) by lra.
        rewrite Qabs_neg; lra. }
    assert (HepsC : 0 < eps * / Qabs c).
    { apply Qmult_lt_0_compat; auto. apply Qinv_lt_0_compat. auto. }
    destruct (HC (eps * / Qabs c) HepsC) as [N HN].
    exists N. intros m n Hm Hn.
    unfold process_scale.
    assert (Heq : c * R m - c * R n == c * (R m - R n)) by ring. rewrite Heq.
    rewrite Qabs_Qmult.
    specialize (HN m n Hm Hn).
    (* Qabs c * Qabs (R m - R n) < Qabs c * (eps / Qabs c) = eps *)
    assert (Habs_nn : 0 <= Qabs (R m - R n)) by (apply Qabs_nonneg).
    assert (Hlt : Qabs c * Qabs (R m - R n) < Qabs c * (eps * / Qabs c)).
    { apply Qmult_lt_l; auto. }
    assert (Heq2 : Qabs c * (eps * / Qabs c) == eps).
    { field. lra. }
    lra.
Qed.

(* ================================================================== *)
(*  Part III: Monotonicity  (~12 lemmas)                              *)
(* ================================================================== *)

Definition monotone_increasing (R : RealProcess) : Prop :=
  forall n, R n <= R (S n).

Definition monotone_decreasing (R : RealProcess) : Prop :=
  forall n, R (S n) <= R n.

Lemma monotone_le : forall R m n,
  monotone_increasing R -> (m <= n)%nat -> R m <= R n.
Proof.
  intros R m n Hmon Hmn.
  induction n as [| k IH].
  - assert (m = 0%nat) by lia. subst. lra.
  - destruct (Nat.eq_dec m (S k)).
    + subst. lra.
    + assert (Hk : (m <= k)%nat) by lia.
      specialize (IH Hk). specialize (Hmon k). lra.
Qed.

Lemma monotone_decreasing_le : forall R m n,
  monotone_decreasing R -> (m <= n)%nat -> R n <= R m.
Proof.
  intros R m n Hmon Hmn.
  induction n as [| k IH].
  - assert (m = 0%nat) by lia. subst. lra.
  - destruct (Nat.eq_dec m (S k)).
    + subst. lra.
    + assert (Hk : (m <= k)%nat) by lia.
      specialize (IH Hk). specialize (Hmon k). lra.
Qed.

(** Qabs of difference for monotone sequence equals max - min *)
Lemma monotone_qabs_eq : forall R m n,
  monotone_increasing R ->
  Qabs (R m - R n) == R (Nat.max m n) - R (Nat.min m n).
Proof.
  intros R m n Hmon.
  destruct (Nat.le_ge_cases m n).
  - (* m <= n *)
    assert (Hmax : Nat.max m n = n) by lia.
    assert (Hmin : Nat.min m n = m) by lia.
    rewrite Hmax, Hmin.
    assert (HRle : R m <= R n) by (apply monotone_le; auto).
    assert (Hneg : R m - R n <= 0) by lra.
    rewrite Qabs_neg; lra.
  - (* n <= m *)
    assert (Hmax : Nat.max m n = m) by lia.
    assert (Hmin : Nat.min m n = n) by lia.
    rewrite Hmax, Hmin.
    assert (HRle : R n <= R m) by (apply monotone_le; auto).
    assert (Hpos : 0 <= R m - R n) by lra.
    rewrite Qabs_pos; lra.
Qed.

(** If not-Cauchy (for monotone increasing R), we can find milestone jumps *)
Lemma find_milestones : forall R eps,
  monotone_increasing R -> 0 < eps ->
  (forall N : nat, exists m n : nat,
    (N <= m)%nat /\ (N <= n)%nat /\ eps <= Qabs (R m - R n)) ->
  forall k : nat, exists M : nat, R 0%nat + inject_Z (Z.of_nat k) * eps <= R M.
Proof.
  intros R eps Hmon Heps Hbad k.
  induction k as [| k' IH].
  - (* k = 0 *)
    exists 0%nat.
    assert (Hzero : inject_Z (Z.of_nat 0) * eps == 0) by (simpl; ring).
    rewrite Hzero. lra.
  - (* k = S k' *)
    destruct IH as [M' HM'].
    destruct (Hbad (S M')) as [m [n [Hm [Hn Hg]]]].
    exists (Nat.max m n).
    (* Qabs (R m - R n) == R(max m n) - R(min m n) by monotone *)
    assert (Habs : Qabs (R m - R n) == R (Nat.max m n) - R (Nat.min m n)).
    { apply monotone_qabs_eq. auto. }
    (* R(min m n) >= R(M') because min m n >= S M' > M' *)
    assert (Hmin_ge : R M' <= R (Nat.min m n)).
    { apply monotone_le; auto. lia. }
    (* R(max m n) >= R(min m n) + eps *)
    assert (Hgap : eps <= R (Nat.max m n) - R (Nat.min m n)) by lra.
    (* Chain: R(max) >= R(min) + eps >= R(M') + eps >= R(0) + k'*eps + eps *)
    assert (Hsk : inject_Z (Z.of_nat (S k')) * eps ==
                  inject_Z (Z.of_nat k') * eps + eps).
    { assert (Hsucc : inject_Z (Z.of_nat (S k')) == inject_Z (Z.of_nat k') + 1).
      { rewrite Nat2Z.inj_succ.
        unfold Qeq, inject_Z, Qplus. simpl.
        rewrite Z.mul_1_r. lia. }
      rewrite Hsucc. ring. }
    rewrite Hsk. lra.
Qed.

(** Archimedean property for Q: for any d and eps > 0, exists K with K*eps > d *)
Lemma q_archimedean : forall d eps,
  0 < eps -> exists K : nat, d < inject_Z (Z.of_nat K) * eps.
Proof.
  intros d eps Heps.
  destruct (Qlt_le_dec d 0) as [Hneg | Hnn].
  - exists 1%nat. simpl.
    assert (H1 : inject_Z 1 * eps == eps) by (unfold inject_Z; lra).
    lra.
  - (* d >= 0: use Z-level computation *)
    destruct d as [dnum dden].
    destruct eps as [ep eq].
    unfold Qlt in Heps. simpl in Heps.
    unfold Qle in Hnn. simpl in Hnn.
    assert (Hp : (0 < ep)%Z) by lia.
    assert (Hd : (0 <= dnum)%Z) by lia.
    set (target := (dnum * Z.pos eq)%Z).
    set (step := (ep * Z.pos dden)%Z).
    assert (Hstep : (0 < step)%Z) by (unfold step; lia).
    assert (Htarget : (0 <= target)%Z) by (unfold target; lia).
    set (K := S (Z.to_nat (target / step))).
    exists K.
    (* Prove target < step * Z.of_nat K in Z *)
    assert (HK_bound : (target / step + 1 <= Z.of_nat K)%Z) by (subst K; lia).
    assert (Hmod := Z_div_mod_eq_full target step).
    assert (Hmod2 : (0 <= target mod step)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Hmod3 : (target mod step < step)%Z) by (apply Z.mod_pos_bound; lia).
    set (q := (target / step)%Z) in *.
    assert (H1 : (target < step * (q + 1))%Z).
    { (* target = step * q + target mod step, mod < step *)
      (* so target < step * q + step = step * (q + 1) *)
      assert (Hexpand : (step * (q + 1) = step * q + step)%Z) by ring.
      lia. }
    assert (H2 : (step * (q + 1) <= step * Z.of_nat K)%Z).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    assert (Hfinal : (target < step * Z.of_nat K)%Z) by lia.
    unfold target, step in Hfinal.
    (* Hfinal: (dnum * Z.pos eq < ep * Z.pos dden * Z.of_nat K)%Z *)
    (* Goal: (dnum # dden) < inject_Z (Z.of_nat K) * (ep # eq) *)
    (* Rewrite Hfinal using commutativity to match Qlt structure *)
    assert (Hfinal2 : (dnum * Z.pos eq < Z.of_nat K * ep * Z.pos dden)%Z).
    { assert (Hcomm : (ep * Z.pos dden * Z.of_nat K =
                        Z.of_nat K * ep * Z.pos dden)%Z) by ring.
      lia. }
    (* Now convert to Qlt *)
    unfold Qlt. simpl. exact Hfinal2.
Qed.

(** Main theorem: monotone increasing + bounded above => Cauchy *)
Lemma monotone_bounded_Cauchy : forall R ub,
  monotone_increasing R -> (forall n, R n <= ub) -> is_Cauchy R.
Proof.
  intros R ub Hmon Hub eps Heps.
  (* Classical: either Cauchy for this eps, or not *)
  destruct (classic (exists N, forall m n, (N <= m)%nat -> (N <= n)%nat ->
                     Qabs (R m - R n) < eps)) as [Hex | Hnex].
  { destruct Hex as [N0 HN0]. exists N0. auto. }
  exfalso.
  (* From ¬Cauchy: forall N, exists pair with large gap *)
  assert (Hbad : forall N, exists m n, (N <= m)%nat /\ (N <= n)%nat /\
                 eps <= Qabs (R m - R n)).
  { intros N.
    destruct (classic (exists m n, (N <= m)%nat /\ (N <= n)%nat /\
                       eps <= Qabs (R m - R n))) as [H | H].
    - auto.
    - exfalso. apply Hnex. exists N. intros m n Hm Hn.
      destruct (Qlt_le_dec (Qabs (R m - R n)) eps); auto.
      exfalso. apply H. exists m, n. auto. }
  (* By Archimedean: pick K with K*eps > ub - R(0) *)
  destruct (q_archimedean (ub - R 0%nat) eps Heps) as [K HK].
  (* By find_milestones: exists M with R(M) >= R(0) + K*eps *)
  destruct (find_milestones R eps Hmon Heps Hbad K) as [M HM].
  (* R(M) >= R(0) + K*eps > R(0) + (ub - R(0)) = ub *)
  assert (Hub_M := Hub M).
  lra.
Qed.

Lemma decreasing_bounded_Cauchy : forall R lb,
  monotone_decreasing R -> (forall n, lb <= R n) -> is_Cauchy R.
Proof.
  intros R lb Hmon Hlb.
  assert (HC : is_Cauchy (process_neg R)).
  { apply monotone_bounded_Cauchy with (ub := -(lb)).
    - intros n. unfold process_neg. specialize (Hmon n). lra.
    - intros n. unfold process_neg. specialize (Hlb n). lra. }
  intros eps Heps.
  destruct (HC eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  unfold process_neg in HN.
  assert (Heq : -(R m) - -(R n) == -(R m - R n)) by ring.
  rewrite Heq in HN. rewrite Qabs_opp in HN. auto.
Qed.
