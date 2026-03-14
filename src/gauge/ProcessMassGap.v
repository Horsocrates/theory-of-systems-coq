(** * ProcessMassGap.v — Process Mass Gap: Formal Criterion
    Elements: Q_process, has_process_mass_gap, su2_gap_process
    Roles:    formal criterion for mass gap as process property (P4)
    Rules:    PMG1 (uniform lower bound), PMG2 (Cauchy rate), PMG3 (monotone)
    Status:   complete
    STATUS: ~45 Qed, 0 Admitted
    AXIOMS: none
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS MASS GAP — Formal Criterion for Mass Gap as Process         *)
(*                                                                            *)
(*  Definition: A process {gap_M} has process mass gap ε if:                *)
(*    PMG1: gap_M ≥ ε for all M                                             *)
(*    PMG2: |gap_{M+1} − gap_M| ≤ C · r^M (Cauchy, explicit rate)          *)
(*    PMG3: gap_{M+1} ≥ gap_M (monotonicity)                                *)
(*                                                                            *)
(*  This is the P4 formalization: the process IS the physics.                *)
(*  No completed limit needed. The mass gap is well-defined at every stage.  *)
(*                                                                            *)
(*  STATUS: ~45 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import SeriesConvergence.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import gauge.ExactMassGap.
From ToS Require Import gauge.SpectralGapCorrect.
From ToS Require Import gauge.TransferMatrixProof.
From ToS Require Import stdlib.Combinatorics.

(* ================================================================== *)
(*  Part I: The Definition                                              *)
(* ================================================================== *)

Definition Q_process := nat -> Q.

Definition has_process_mass_gap (gap_proc : Q_process) : Prop :=
  exists (eps C r : Q),
    0 < eps /\
    (forall M, eps <= gap_proc M) /\
    0 < C /\ 0 < r /\ r < 1 /\
    (forall M, Qabs (gap_proc (S M) - gap_proc M) <= C * Qpow r M) /\
    (forall M, gap_proc M <= gap_proc (S M)).

Lemma pmg_gap_positive : forall gap_proc,
  has_process_mass_gap gap_proc ->
  forall M, 0 < gap_proc M.
Proof.
  intros gap_proc H M.
  destruct H as [eps [C [r H]]].
  destruct H as [Heps [Hunif _]].
  assert (Hu := Hunif M). lra.
Qed.

Lemma pmg_monotone_le : forall gap_proc,
  has_process_mass_gap gap_proc ->
  forall M N, (M <= N)%nat -> gap_proc M <= gap_proc N.
Proof.
  intros gap_proc H M N Hle.
  destruct H as [eps [C [r H]]].
  destruct H as [_ [_ [_ [_ [_ [_ Hmono]]]]]].
  induction Hle as [|N' Hle IH].
  - lra.
  - assert (Hm := Hmono N'). lra.
Qed.

(* ================================================================== *)
(*  Part II: SU(2) Gap Process                                         *)
(* ================================================================== *)

Definition su2_gap_process (beta : Q) : Q_process :=
  fun M => spectral_gap 1 beta M.

Lemma su2_gap_at_0 : su2_gap_process 1 0%nat == 289 # 384.
Proof.
  unfold su2_gap_process. exact spectral_gap_beta_1.
Qed.

(* ================================================================== *)
(*  Part III: Helper Lemmas                                             *)
(* ================================================================== *)

Lemma Qpow_plus : forall (q : Q) (a b : nat),
  Qpow q (a + b) == Qpow q a * Qpow q b.
Proof.
  intros q a b. induction a as [|a' IH].
  - simpl. ring.
  - replace (S a' + b)%nat with (S (a' + b)) by lia.
    simpl Qpow. rewrite IH. ring.
Qed.

Lemma Qpow_nonneg_half : forall k, 0 <= Qpow (1 # 2) k.
Proof. intros. apply Qpow_nonneg. lra. Qed.

Lemma Qpow_pos_half : forall k, 0 < Qpow (1 # 2) k.
Proof.
  induction k as [|k IH].
  - simpl. lra.
  - simpl. assert (H : 0 < (1#2)) by lra.
    apply Qmult_lt_0_compat; assumption.
Qed.

Lemma inject_Z_mult_Q : forall a b : Z,
  inject_Z (a * b) == inject_Z a * inject_Z b.
Proof. intros. unfold Qeq. simpl. lia. Qed.

(* ================================================================== *)
(*  Part IV: Bessel Partial Sum Step                                    *)
(* ================================================================== *)

Lemma bessel_partial_step : forall n beta M,
  bessel_partial n beta (S M) == bessel_partial n beta M + bessel_term n (S M) beta.
Proof. intros. simpl. ring. Qed.

Definition gap_bracket (m : nat) (beta : Q) : Q :=
  bessel_term 0 m beta - 2 * bessel_term 2 m beta + bessel_term 4 m beta.

Lemma gap_step_eq : forall beta M,
  character_mass_gap beta (S M) == character_mass_gap beta M + gap_bracket (S M) beta.
Proof.
  intros beta M.
  unfold gap_bracket.
  rewrite (gap_formula beta (S M)).
  rewrite (gap_formula beta M).
  rewrite !bessel_partial_step.
  ring.
Qed.

(* ================================================================== *)
(*  Part V: Bracket Positivity — The Key Lemma                         *)
(* ================================================================== *)

(** The Qpow cancellation lemma: (1/2)^k * 2^k = 1 *)
Lemma Qpow_half_cancel : forall k,
  Qpow (1 # 2) k * inject_Z (Z.of_nat (Nat.pow 2 k)) == 1.
Proof.
  induction k as [|k IH].
  - simpl. ring.
  - unfold Qeq. simpl Qpow. simpl Nat.pow.
    unfold Qmult, inject_Z, Qnum, Qden.
    rewrite Z.mul_1_r.
    change (Z.of_nat (2 * Nat.pow 2 k)) with (2 * Z.of_nat (Nat.pow 2 k))%Z.
    assert (IH' : Qpow (1 # 2) k * inject_Z (Z.of_nat (Nat.pow 2 k)) == 1) by exact IH.
    unfold Qeq, Qmult, inject_Z, Qnum, Qden in IH'.
    rewrite Z.mul_1_r in IH'. nia.
Qed.

(** Denominator of bessel_term at β=1 *)
Definition bt_denom (n m : nat) : nat :=
  Nat.pow 2 (n + 2 * m) * fact m * fact (n + m).

Lemma pow2_pos : forall k, (0 < Nat.pow 2 k)%nat.
Proof. induction k; simpl; lia. Qed.

Lemma fact_nat_pos : forall n, (0 < fact n)%nat.
Proof.
  induction n as [|n IH].
  - simpl. lia.
  - simpl. nia.
Qed.

Lemma bt_denom_pos : forall n m, (0 < bt_denom n m)%nat.
Proof.
  intros n m. unfold bt_denom.
  assert (H1 := pow2_pos (n + 2*m)).
  assert (H2 := fact_nat_pos m).
  assert (H3 := fact_nat_pos (n+m)).
  nia.
Qed.

(** Qpow respects Qeq *)
Lemma Qpow_compat : forall q1 q2 k, q1 == q2 -> Qpow q1 k == Qpow q2 k.
Proof.
  intros q1 q2 k Heq. induction k as [|k IH].
  - simpl. lra.
  - simpl.
    assert (Hstep : q1 * Qpow q1 k == q2 * Qpow q2 k).
    { apply Qmult_comp; assumption. }
    exact Hstep.
Qed.

Lemma Qdiv_1_2_eq : 1 / 2 == 1 # 2.
Proof. unfold Qeq. simpl. lia. Qed.

(** Division-multiplication cancellation *)
Lemma Qdiv_mul_cancel : forall a b c,
  ~ b == 0 -> a / b * (c * b) == a * c.
Proof. intros. field. assumption. Qed.

(** bessel_term n m 1 * bt_denom == 1: proved via Qpow_half_cancel *)
Lemma bessel_term_inv : forall n m,
  bessel_term n m 1 * inject_Z (Z.of_nat (bt_denom n m)) == 1.
Proof.
  intros n m.
  unfold bessel_term, bt_denom, fact_prod, fact_Q.
  rewrite !Nat2Z.inj_mul, !inject_Z_mult_Q.
  (* Non-zero facts *)
  assert (Hfm_ne : ~ inject_Z (Z.of_nat (fact m)) == 0).
  { unfold Qeq. simpl. rewrite Z.mul_1_r. assert (H := fact_nat_pos m). lia. }
  assert (Hfnm_ne : ~ inject_Z (Z.of_nat (fact (n+m))) == 0).
  { unfold Qeq. simpl. rewrite Z.mul_1_r. assert (H := fact_nat_pos (n+m)). lia. }
  (* The goal involves Qpow (1/2) k / (fm * fnm) * (pow2k * fm * fnm) == 1 *)
  (* This equals Qpow (1/2) k * pow2k by cancellation *)
  (* Strategy: extract Qpow * pow2k, then apply Qpow_half_cancel *)
  assert (Hcancel :
    Qpow (1 / 2) (n + 2 * m) /
      (inject_Z (Z.of_nat (fact m)) * inject_Z (Z.of_nat (fact (n + m)))) *
    (inject_Z (Z.of_nat (Nat.pow 2 (n + 2 * m))) *
     inject_Z (Z.of_nat (fact m)) * inject_Z (Z.of_nat (fact (n + m))))
    ==
    Qpow (1 / 2) (n + 2 * m) * inject_Z (Z.of_nat (Nat.pow 2 (n + 2 * m)))).
  { field. split; assumption. }
  transitivity (Qpow (1 / 2) (n + 2 * m) * inject_Z (Z.of_nat (Nat.pow 2 (n + 2 * m)))).
  { exact Hcancel. }
  assert (Hpow_eq := Qpow_compat _ _ (n + 2*m) Qdiv_1_2_eq).
  transitivity (Qpow (1 # 2) (n + 2 * m) * inject_Z (Z.of_nat (Nat.pow 2 (n + 2 * m)))).
  { apply Qmult_comp; [exact Hpow_eq | reflexivity]. }
  exact (Qpow_half_cancel (n + 2 * m)).
Qed.

(** The key denominator inequality: 2 * D(0,m) <= D(2,m) *)
Lemma denom_ineq_02 : forall m,
  (2 * bt_denom 0 m <= bt_denom 2 m)%nat.
Proof.
  intros m. unfold bt_denom.
  replace (0 + 2 * m)%nat with (2 * m)%nat by lia.
  replace (0 + m)%nat with m by lia.
  replace (2 + 2 * m)%nat with (S (S (2 * m))) by lia.
  replace (2 + m)%nat with (S (S m)) by lia.
  simpl Nat.pow. simpl fact.
  nia.
Qed.

(** BT(0,m,1) >= 2 * BT(2,m,1) — the domination lemma *)
Lemma bessel_term_0_dominates_2 : forall m,
  2 * bessel_term 2 m 1 <= bessel_term 0 m 1.
Proof.
  intros m.
  assert (Hdn := denom_ineq_02 m).
  assert (Hd0 := bt_denom_pos 0 m).
  assert (Hd2 := bt_denom_pos 2 m).
  assert (Hinv0 := bessel_term_inv 0 m).
  assert (Hinv2 := bessel_term_inv 2 m).
  (* Multiply goal by positive D0 * D2 to eliminate fractions *)
  set (D0 := inject_Z (Z.of_nat (bt_denom 0 m))).
  set (D2 := inject_Z (Z.of_nat (bt_denom 2 m))).
  assert (HD0_pos : 0 < D0).
  { subst D0. unfold Qlt. simpl. lia. }
  assert (HD2_pos : 0 < D2).
  { subst D2. unfold Qlt. simpl. lia. }
  (* BT0 * D0 == 1 and BT2 * D2 == 1 *)
  (* So BT0 == 1/D0 and BT2 == 1/D2 *)
  (* 2 * BT2 <= BT0 iff 2 * BT2 * D0 * D2 <= BT0 * D0 * D2 *)
  (* iff 2 * (BT2 * D2) * D0 <= (BT0 * D0) * D2 *)
  (* iff 2 * 1 * D0 <= 1 * D2 *)
  (* iff 2 * D0 <= D2 — which is denom_ineq_02 *)
  apply Qmult_le_r with (z := D0 * D2).
  { apply Qmult_lt_0_compat; assumption. }
  (* LHS: 2 * BT2 * (D0 * D2) *)
  assert (Hlhs : 2 * bessel_term 2 m 1 * (D0 * D2) == 2 * D0).
  { assert (H1 : bessel_term 2 m 1 * D2 == 1) by exact Hinv2.
    assert (H2 : 2 * bessel_term 2 m 1 * (D0 * D2)
                 == 2 * (bessel_term 2 m 1 * D2) * D0) by ring.
    assert (H3 : 2 * (bessel_term 2 m 1 * D2) * D0
                 == 2 * 1 * D0).
    { apply Qmult_comp; [apply Qmult_comp; [reflexivity|exact H1]|reflexivity]. }
    transitivity (2 * (bessel_term 2 m 1 * D2) * D0); [exact H2|].
    transitivity (2 * 1 * D0); [exact H3|ring]. }
  assert (Hrhs : bessel_term 0 m 1 * (D0 * D2) == D2).
  { assert (H1 : bessel_term 0 m 1 * D0 == 1) by exact Hinv0.
    assert (H2 : bessel_term 0 m 1 * (D0 * D2)
                 == (bessel_term 0 m 1 * D0) * D2) by ring.
    assert (H3 : (bessel_term 0 m 1 * D0) * D2 == 1 * D2).
    { apply Qmult_comp; [exact H1|reflexivity]. }
    transitivity ((bessel_term 0 m 1 * D0) * D2); [exact H2|].
    transitivity (1 * D2); [exact H3|ring]. }
  (* Now: 2*D0 <= D2 (nat inequality lifted to Q) *)
  assert (HZ : (Z.of_nat (2 * bt_denom 0 m) <= Z.of_nat (bt_denom 2 m))%Z).
  { zify. lia. }
  assert (Hnat_le : 2 * D0 <= D2).
  { unfold D0, D2.
    assert (Hle_z : inject_Z (Z.of_nat (2 * bt_denom 0 m)) <=
                    inject_Z (Z.of_nat (bt_denom 2 m))).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (H2eq : inject_Z (Z.of_nat (2 * bt_denom 0 m)) ==
                   2 * inject_Z (Z.of_nat (bt_denom 0 m))).
    { rewrite Nat2Z.inj_mul. unfold Qeq. simpl. lia. }
    lra. }
  lra.
Qed.

(** Bracket is nonneg at β=1 *)
Lemma gap_bracket_nonneg : forall m,
  0 <= gap_bracket m 1.
Proof.
  intros m. unfold gap_bracket.
  assert (H1 := bessel_term_0_dominates_2 m).
  assert (H2 := bessel_term_nonneg 4 m 1).
  assert (Hone : (0 : Q) <= 1) by lra.
  specialize (H2 Hone). lra.
Qed.

(* ================================================================== *)
(*  Part VI: Character Mass Gap Properties at β=1                      *)
(* ================================================================== *)

Lemma char_gap_eq : forall beta M,
  character_mass_gap beta M == matrix_mass_gap 1 beta M.
Proof.
  intros. rewrite matrix_gap_eq_character. reflexivity.
Qed.

Lemma char_gap_at_0_positive :
  0 < character_mass_gap 1 0.
Proof.
  assert (H := gap_at_beta_1_positive).
  unfold gap_M0, t0_M0, t1_M0 in H.
  rewrite gap_formula. unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
  unfold Qlt. simpl. lia.
Qed.

Lemma char_gap_step_nonneg : forall M,
  character_mass_gap 1 M <= character_mass_gap 1 (S M).
Proof.
  intros M.
  rewrite gap_step_eq.
  assert (H := gap_bracket_nonneg (S M)). lra.
Qed.

Lemma char_gap_positive : forall M,
  0 < character_mass_gap 1 M.
Proof.
  induction M as [|M IH].
  - exact char_gap_at_0_positive.
  - assert (H := char_gap_step_nonneg M). lra.
Qed.

Lemma spectral_gap_eq_char_gap : forall M,
  spectral_gap 1 1 M == character_mass_gap 1 M.
Proof.
  intros M. unfold spectral_gap.
  rewrite matrix_gap_eq_character.
  assert (Hpos := char_gap_positive M).
  apply Qabs_pos. lra.
Qed.

(* ================================================================== *)
(*  Part VII: PMG3 — Monotonicity                                       *)
(* ================================================================== *)

Theorem pmg3_beta_1 : forall M,
  su2_gap_process 1 M <= su2_gap_process 1 (S M).
Proof.
  intros M. unfold su2_gap_process.
  rewrite !spectral_gap_eq_char_gap.
  apply char_gap_step_nonneg.
Qed.

(* ================================================================== *)
(*  Part VIII: PMG1 — Uniform Lower Bound                               *)
(* ================================================================== *)

Theorem pmg1_beta_1 : forall M,
  289 # 384 <= su2_gap_process 1 M.
Proof.
  induction M as [|M IH].
  - assert (H := su2_gap_at_0). change (289 # 384 <= su2_gap_process 1 0%nat). lra.
  - assert (Hm := pmg3_beta_1 M). lra.
Qed.

(* ================================================================== *)
(*  Part IX: PMG2 — Cauchy Rate                                         *)
(* ================================================================== *)

Lemma fact_Q_ge_1 : forall n, 1 <= fact_Q n.
Proof.
  intros n. unfold fact_Q.
  unfold Qle. simpl. rewrite Z.mul_1_r.
  assert (H : (1 <= fact n)%nat).
  { assert (Hp := fact_nat_pos n). lia. }
  lia.
Qed.

Lemma Qpow_le_1 : forall q k, 0 <= q -> q <= 1 -> Qpow q k <= 1.
Proof.
  intros q k Hq0 Hq1. induction k as [|k IH].
  - simpl. lra.
  - simpl.
    assert (H : q * Qpow q k <= 1 * 1).
    { apply Qmult_le_compat_nonneg.
      - split; lra.
      - split; [apply Qpow_nonneg; lra | exact IH]. }
    lra.
Qed.

(** bt_denom(4,m) >= bt_denom(0,m) — higher Bessel index has bigger denom *)
Lemma denom_ineq_04 : forall m,
  (bt_denom 0 m <= bt_denom 4 m)%nat.
Proof.
  intros m. unfold bt_denom.
  replace (0 + 2*m)%nat with (2*m)%nat by lia.
  replace (0 + m)%nat with m by lia.
  (* Goal: 2^(2m)*m!*m! <= 2^(4+2m)*m!*(4+m)! *)
  (* 2^(4+2m) = 2^4 * 2^(2m) = 16 * 2^(2m) *)
  replace (4 + 2*m)%nat with (4 + 2*m)%nat by lia.
  assert (Hpow : (Nat.pow 2 (4 + 2*m) = 16 * Nat.pow 2 (2*m))%nat).
  { replace (4 + 2*m)%nat with (S (S (S (S (2*m))))) by lia.
    simpl Nat.pow. lia. }
  rewrite Hpow.
  (* Goal: 2^(2m)*m!*m! <= 16*2^(2m)*m!*(4+m)! *)
  assert (Hfact_le : (fact m <= fact (4 + m))%nat).
  { apply Nat.le_trans with (m := fact (S m)).
    - simpl. assert (Hp := fact_nat_pos m). nia.
    - apply Nat.le_trans with (m := fact (S (S m))).
      + simpl. assert (Hp := fact_nat_pos (S m)). nia.
      + apply Nat.le_trans with (m := fact (S (S (S m)))).
        * simpl. assert (Hp := fact_nat_pos (S (S m))). nia.
        * replace (4 + m)%nat with (S (S (S (S m)))) by lia.
          simpl. assert (Hp := fact_nat_pos (S (S (S m)))). nia. }
  assert (Hp := pow2_pos (2*m)).
  assert (Hf := fact_nat_pos m).
  nia.
Qed.

(** BT(4,m,1) <= BT(0,m,1) *)
Lemma bessel_term_4_le_0 : forall m,
  bessel_term 4 m 1 <= bessel_term 0 m 1.
Proof.
  intros m.
  assert (Hd0 := bt_denom_pos 0 m).
  assert (Hd4 := bt_denom_pos 4 m).
  assert (Hinv0 := bessel_term_inv 0 m).
  assert (Hinv4 := bessel_term_inv 4 m).
  assert (Hdn := denom_ineq_04 m).
  set (D0 := inject_Z (Z.of_nat (bt_denom 0 m))).
  set (D4 := inject_Z (Z.of_nat (bt_denom 4 m))).
  assert (HD0_pos : 0 < D0) by (subst D0; unfold Qlt; simpl; lia).
  assert (HD4_pos : 0 < D4) by (subst D4; unfold Qlt; simpl; lia).
  apply Qmult_le_r with (z := D0 * D4).
  { apply Qmult_lt_0_compat; assumption. }
  assert (Hlhs : bessel_term 4 m 1 * (D0 * D4) == D0).
  { assert (H1 : bessel_term 4 m 1 * D4 == 1) by exact Hinv4.
    assert (H2 : bessel_term 4 m 1 * (D0 * D4) == (bessel_term 4 m 1 * D4) * D0) by ring.
    assert (H3 : (bessel_term 4 m 1 * D4) * D0 == 1 * D0).
    { apply Qmult_comp; [exact H1|reflexivity]. }
    transitivity ((bessel_term 4 m 1 * D4) * D0); [exact H2|].
    transitivity (1 * D0); [exact H3|ring]. }
  assert (Hrhs : bessel_term 0 m 1 * (D0 * D4) == D4).
  { assert (H1 : bessel_term 0 m 1 * D0 == 1) by exact Hinv0.
    assert (H2 : bessel_term 0 m 1 * (D0 * D4) == (bessel_term 0 m 1 * D0) * D4) by ring.
    assert (H3 : (bessel_term 0 m 1 * D0) * D4 == 1 * D4).
    { apply Qmult_comp; [exact H1|reflexivity]. }
    transitivity ((bessel_term 0 m 1 * D0) * D4); [exact H2|].
    transitivity (1 * D4); [exact H3|ring]. }
  assert (Hnat_le : D0 <= D4).
  { unfold D0, D4. unfold Qle, inject_Z. simpl. lia. }
  lra.
Qed.

(** gap_bracket m 1 <= 2 * BT(0,m,1) *)
Lemma gap_step_le_2bt0 : forall m,
  gap_bracket m 1 <= 2 * bessel_term 0 m 1.
Proof.
  intros m. unfold gap_bracket.
  assert (H1 := bessel_term_nonneg 2 m 1).
  assert (H2 := bessel_term_4_le_0 m).
  assert (Hone : (0 : Q) <= 1) by lra.
  specialize (H1 Hone). lra.
Qed.

(** 4 * bt_denom(0,m) <= bt_denom(0, S m) *)
Lemma denom_ineq_0_step : forall m,
  (4 * bt_denom 0 m <= bt_denom 0 (S m))%nat.
Proof.
  intros m. unfold bt_denom.
  replace (0 + 2*m)%nat with (2*m)%nat by lia.
  replace (0 + m)%nat with m by lia.
  replace (0 + 2 * S m)%nat with (2 + 2*m)%nat by lia.
  replace (0 + S m)%nat with (S m) by lia.
  replace (2 + 2*m)%nat with (S (S (2*m))) by lia.
  simpl Nat.pow. simpl fact. nia.
Qed.

(** Geometric bound via denominator inequality *)
Lemma bt0_geometric : forall m,
  bessel_term 0 (S m) 1 <= (1#4) * bessel_term 0 m 1.
Proof.
  intros m.
  assert (Hd0 := bt_denom_pos 0 m).
  assert (Hd0s := bt_denom_pos 0 (S m)).
  assert (Hinv0 := bessel_term_inv 0 m).
  assert (Hinv0s := bessel_term_inv 0 (S m)).
  set (D0 := inject_Z (Z.of_nat (bt_denom 0 m))).
  set (Ds := inject_Z (Z.of_nat (bt_denom 0 (S m)))).
  assert (HD0_pos : 0 < D0) by (subst D0; unfold Qlt; simpl; lia).
  assert (HDs_pos : 0 < Ds) by (subst Ds; unfold Qlt; simpl; lia).
  apply Qmult_le_r with (z := D0 * Ds).
  { apply Qmult_lt_0_compat; assumption. }
  (* LHS: BT(0,S m,1) * (D0 * Ds) == D0 *)
  assert (Hlhs : bessel_term 0 (S m) 1 * (D0 * Ds) == D0).
  { assert (H1 : bessel_term 0 (S m) 1 * Ds == 1) by exact Hinv0s.
    assert (H2 : bessel_term 0 (S m) 1 * (D0 * Ds) == (bessel_term 0 (S m) 1 * Ds) * D0)
      by ring.
    assert (H3 : (bessel_term 0 (S m) 1 * Ds) * D0 == 1 * D0).
    { apply Qmult_comp; [exact H1|reflexivity]. }
    transitivity ((bessel_term 0 (S m) 1 * Ds) * D0); [exact H2|].
    transitivity (1 * D0); [exact H3|ring]. }
  (* RHS: (1#4) * BT(0,m,1) * (D0 * Ds) == (1#4) * Ds *)
  assert (Hrhs : (1 # 4) * bessel_term 0 m 1 * (D0 * Ds) == (1 # 4) * Ds).
  { assert (H1 : bessel_term 0 m 1 * D0 == 1) by exact Hinv0.
    assert (H2 : (1 # 4) * bessel_term 0 m 1 * (D0 * Ds)
                 == (1 # 4) * (bessel_term 0 m 1 * D0) * Ds) by ring.
    assert (H3 : (1 # 4) * (bessel_term 0 m 1 * D0) * Ds == (1 # 4) * 1 * Ds).
    { apply Qmult_comp; [apply Qmult_comp; [reflexivity|exact H1]|reflexivity]. }
    transitivity ((1 # 4) * (bessel_term 0 m 1 * D0) * Ds); [exact H2|].
    transitivity ((1 # 4) * 1 * Ds); [exact H3|ring]. }
  (* Now: D0 <= (1#4) * Ds iff 4 * D0 <= Ds *)
  assert (Hdn := denom_ineq_0_step m).
  assert (Hnat_le : 4 * D0 <= Ds).
  { unfold D0, Ds.
    assert (Hle_z : inject_Z (Z.of_nat (4 * bt_denom 0 m)) <=
                    inject_Z (Z.of_nat (bt_denom 0 (S m)))).
    { unfold Qle, inject_Z. simpl. lia. }
    assert (H4eq : inject_Z (Z.of_nat (4 * bt_denom 0 m)) ==
                   4 * inject_Z (Z.of_nat (bt_denom 0 m))).
    { rewrite Nat2Z.inj_mul. unfold Qeq. simpl. lia. }
    lra. }
  lra.
Qed.

(** BT(0, S M, 1) <= (1/4)^{S M} — inductive via bt0_geometric *)
Lemma bt0_le_pow : forall m,
  bessel_term 0 (S m) 1 <= Qpow (1 # 4) (S m).
Proof.
  induction m as [|m' IH].
  - unfold bessel_term, fact_prod, fact_Q, fact. unfold Qle, Qpow, Qdiv, Qmult, Qinv.
    simpl. lia.
  - assert (Hgeo := bt0_geometric (S m')).
    simpl Qpow.
    assert (Hcompat : (1 # 4) * bessel_term 0 (S m') 1 <= (1 # 4) * Qpow (1 # 4) (S m')).
    { rewrite (Qmult_le_l _ _ (1#4)). exact IH. lra. }
    apply Qle_trans with ((1 # 4) * bessel_term 0 (S m') 1); assumption.
Qed.

(** (1/4)^{S M} <= (1/4)^M *)
Lemma Qpow_quarter_dec : forall M,
  Qpow (1 # 4) (S M) <= Qpow (1 # 4) M.
Proof.
  induction M as [|M' IH].
  - simpl. lra.
  - simpl.
    assert (H1 : (1 # 4) * Qpow (1 # 4) (S M') <= (1 # 4) * Qpow (1 # 4) M').
    { rewrite (Qmult_le_l _ _ (1#4)). exact IH. lra. }
    assert (H2 : (1 # 4) * Qpow (1 # 4) M' <= 1 * Qpow (1 # 4) M').
    { assert (Hpn : 0 <= Qpow (1#4) M') by (apply Qpow_nonneg; lra).
      assert (H14 : (1#4) <= 1) by lra. lra. }
    lra.
Qed.

(** PMG2: Cauchy rate at β=1 with C=2, r=1/4 *)
Theorem pmg2_beta_1 : forall M,
  Qabs (su2_gap_process 1 (S M) - su2_gap_process 1 M) <= 2 * Qpow (1 # 4) M.
Proof.
  intros M. unfold su2_gap_process.
  rewrite !spectral_gap_eq_char_gap.
  assert (Hstep := gap_step_eq 1 M).
  assert (Hbn := gap_bracket_nonneg (S M)).
  assert (Habs : Qabs (character_mass_gap 1 (S M) - character_mass_gap 1 M) ==
                 gap_bracket (S M) 1).
  { assert (Hdiff : character_mass_gap 1 (S M) - character_mass_gap 1 M == gap_bracket (S M) 1)
      by lra.
    rewrite Hdiff. apply Qabs_pos. lra. }
  assert (Hle : Qabs (character_mass_gap 1 (S M) - character_mass_gap 1 M) <=
                gap_bracket (S M) 1) by (rewrite Habs; lra).
  assert (Hle2 : gap_bracket (S M) 1 <= 2 * bessel_term 0 (S M) 1).
  { apply gap_step_le_2bt0. }
  assert (Hle3 := bt0_le_pow M).
  assert (Hle4 := Qpow_quarter_dec M).
  assert (Hbt_nn : 0 <= bessel_term 0 (S M) 1).
  { apply bessel_term_nonneg. lra. }
  assert (Hcompat : 2 * bessel_term 0 (S M) 1 <= 2 * Qpow (1 # 4) (S M)).
  { rewrite (Qmult_le_l _ _ 2). exact Hle3. lra. }
  assert (Hcompat2 : 2 * Qpow (1 # 4) (S M) <= 2 * Qpow (1 # 4) M).
  { rewrite (Qmult_le_l _ _ 2). exact Hle4. lra. }
  lra.
Qed.

(* ================================================================== *)
(*  Part X: Main Theorem                                                *)
(* ================================================================== *)

(** ★ PROCESS MASS GAP FOR SU(2) AT β=1 ★ *)
Theorem su2_has_process_mass_gap :
  has_process_mass_gap (su2_gap_process 1).
Proof.
  exists (289 # 384), 2, (1 # 4).
  split; [lra|].
  split; [exact pmg1_beta_1|].
  split; [lra|].
  split; [lra|].
  split; [lra|].
  split; [exact pmg2_beta_1|].
  exact pmg3_beta_1.
Qed.

(* ================================================================== *)
(*  Part XI: Explicit Values and Properties                             *)
(* ================================================================== *)

Lemma su2_gap_at_1 : su2_gap_process 1 1%nat == 7541 # 7680.
Proof.
  unfold su2_gap_process, spectral_gap.
  rewrite matrix_gap_eq_character. rewrite gap_formula.
  simpl bessel_partial.
  unfold bessel_term, fact_prod, fact_Q, fact.
  assert (Hpos : 0 < character_mass_gap 1 1).
  { apply char_gap_positive. }
  rewrite gap_formula in Hpos.
  simpl bessel_partial in Hpos.
  unfold bessel_term, fact_prod, fact_Q, fact in Hpos.
  assert (Hval : bessel_partial 0 1 0 + bessel_term 0 1 1 -
                 2 * (bessel_partial 2 1 0 + bessel_term 2 1 1) +
                 (bessel_partial 4 1 0 + bessel_term 4 1 1) == 7541 # 7680).
  { unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
    unfold Qeq. simpl. lia. }
  assert (Habs : Qabs (7541 # 7680) == 7541 # 7680).
  { apply Qabs_pos. lra. }
  rewrite Hval in * |- *. exact Habs.
Qed.

Lemma su2_gap_at_2 : su2_gap_process 1 2%nat == 367489 # 368640.
Proof.
  unfold su2_gap_process, spectral_gap.
  rewrite matrix_gap_eq_character. rewrite gap_formula.
  assert (Hpos := char_gap_positive 2). rewrite gap_formula in Hpos.
  assert (Hval : bessel_partial 0 1 2 - 2 * bessel_partial 2 1 2 + bessel_partial 4 1 2
                 == 367489 # 368640).
  { unfold bessel_partial, bessel_term, fact_prod, fact_Q, fact.
    unfold Qeq. simpl. lia. }
  assert (Habs : Qabs (367489 # 368640) == 367489 # 368640).
  { apply Qabs_pos. lra. }
  transitivity (Qabs (bessel_partial 0 1 2 - 2 * bessel_partial 2 1 2 + bessel_partial 4 1 2)).
  { reflexivity. }
  rewrite Hval. exact Habs.
Qed.

Lemma su2_gap_increasing_0_1 :
  su2_gap_process 1 0%nat < su2_gap_process 1 1%nat.
Proof.
  rewrite su2_gap_at_0, su2_gap_at_1. lra.
Qed.

Lemma su2_gap_increasing_1_2 :
  su2_gap_process 1 1%nat < su2_gap_process 1 2%nat.
Proof.
  rewrite su2_gap_at_1, su2_gap_at_2. lra.
Qed.

(* ================================================================== *)
(*  Part XII: All rational β > 0                                        *)
(* ================================================================== *)

(** Spectral gap positive for all rational β — from SpectralGapCorrect.v *)
Theorem pmg_spectral_all_beta : forall beta,
  0 < beta -> 0 < su2_gap_process beta 0%nat.
Proof.
  intros beta Hb. unfold su2_gap_process.
  exact (spectral_gap_pos_all_rational beta Hb).
Qed.

(* ================================================================== *)
(*  Part XIII: Summary                                                  *)
(* ================================================================== *)

Theorem process_mass_gap_summary :
  (* The SU(2) gap process at β=1 has a process mass gap *)
  has_process_mass_gap (su2_gap_process 1) /\
  (* PMG1: gap ≥ 289/384 for all M *)
  (forall M, 289 # 384 <= su2_gap_process 1 M) /\
  (* PMG3: monotonically increasing *)
  (forall M, su2_gap_process 1 M <= su2_gap_process 1 (S M)) /\
  (* Concrete values *)
  su2_gap_process 1 0%nat == 289 # 384 /\
  su2_gap_process 1 1%nat == 7541 # 7680.
Proof.
  split; [exact su2_has_process_mass_gap |].
  split; [exact pmg1_beta_1 |].
  split; [exact pmg3_beta_1 |].
  split; [exact su2_gap_at_0 |].
  exact su2_gap_at_1.
Qed.

(* ================================================================== *)
(*  CHECKS                                                              *)
(* ================================================================== *)

Check su2_has_process_mass_gap.
Check pmg1_beta_1.
Check pmg2_beta_1.
Check pmg3_beta_1.
Check su2_gap_at_0.
Check su2_gap_at_1.
Check su2_gap_at_2.
Check process_mass_gap_summary.
Print Assumptions su2_has_process_mass_gap.
