(** * Sqrt2Processes.v — The square root of two as a class of processes:
      Newton, the continued fraction and the shrinking intervals — each is a
      Cauchy process, each reaches every precision, and they are equivalent

    E/R/R reading (done before coding; audit of Part III of the Mathematics
    volume, chapter III.4, places 4.1, 4.3 and 4.4, 2026-11-14):

    Elements: the rational approximations — the stages of a process nat -> Q.
    Roles:    a process that gives the square root of two — its square comes
              below every precision of 2; the class of such processes — the
              role-limit the chapter calls the square root of two.
    Rules:    the rule of each process (the Newton step, the step of the
              continued fraction, halving with a choice by the square of the
              midpoint); process_equiv — the difference goes below every
              precision.
    Proved:   (1) the predicate with the sign: non-negative members and the
                  square tending to 2; from it the Cauchy condition FOLLOWS,
                  and any two such processes are equivalent — the class is
                  one; without the sign the predicate of the chapter is
                  satisfied by R and by -R, two classes;
              (2) the continued-fraction process is the Pell process and
                  gives the root, with |x_n^2 - 2| = 1 / q_n^2;
              (3) the Newton process gives the root, with the explicit bound
                  |x_n^2 - 2| <= 1 / 2^n, and every step strictly improves;
              (4) the process of shrinking intervals for the square equal to
                  two is built (the half is chosen by comparing rationals),
                  is a Cauchy process and gives the root, with
                  |m_n^2 - 2| <= 4 / 2^n;
              (5) the three processes are pairwise equivalent;
              (6) the two forms of the Cauchy condition used in the
                  repository are equivalent; the shrinking theorem in the
                  form with nested intervals in the premise.
    P4 diagnostic ("could it be otherwise?"): every statement is about
              finite stages and rational bounds. Forced: (1)-(6). NOT
              claimed: a rational (or any completed) number whose square is
              2 — there is none (Sqrt2Irrational.v); a quotient type of
              processes; that the open family of ALL processes for the root
              is formalized — the class is given by the predicate, three
              members are exhibited.

    STATUS: 52 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia.

(* Require WITHOUT Import: these files declare the same names (is_Cauchy, ...). *)
From ToS Require ShrinkingIntervals_ERR.
From ToS Require Archimedean_ERR.
From ToS Require process.ProcessCore.
From ToS Require stdlib.ProcessRefinement.
From ToS Require analysis.Sqrt2Irrational.
From ToS Require stdlib.qphysics.QPhysicsProcesses.
From ToS Require Import Sqrt2Approx.
From ToS Require Import stdlib.RefinementSqrt.

Module SI := ShrinkingIntervals_ERR.
Module AR := Archimedean_ERR.
Module PC := ProcessCore.
Module PR := ProcessRefinement.

Open Scope Q_scope.

(* ========================================================================= *)
(*  1. VALUES AND SIMPLE FACTS NAMED IN THE CHAPTER                          *)
(* ========================================================================= *)

Lemma newton_3 : sqrt2_newton 3%nat == 577#408.
Proof. vm_compute. reflexivity. Qed.

Lemma cf_3 : sqrt2_cf 3%nat == 17#12.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_sq_1 : sqrt2_newton 1%nat * sqrt2_newton 1%nat == 9#4.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_sq_2 : sqrt2_newton 2%nat * sqrt2_newton 2%nat == 289#144.
Proof. vm_compute. reflexivity. Qed.

(** The two processes are not equal stage by stage. *)
Lemma newton_cf_not_process_eq : ~ PR.process_eq sqrt2_newton sqrt2_cf.
Proof. intro H. exact (differ_at_2 (H 2%nat)). Qed.

Lemma quality_comparable : forall K : nat,
  sqrt2_quality (sqrt2_newton K) <= sqrt2_quality (sqrt2_cf K) \/
  sqrt2_quality (sqrt2_cf K) < sqrt2_quality (sqrt2_newton K).
Proof.
  intro K.
  destruct (Qlt_le_dec (sqrt2_quality (sqrt2_cf K)) (sqrt2_quality (sqrt2_newton K))) as [H | H].
  - right. exact H.
  - left. exact H.
Qed.

(* ========================================================================= *)
(*  2. THE TWO FORMS OF THE CAUCHY CONDITION ARE EQUIVALENT                  *)
(* ========================================================================= *)

(** The Cauchy condition of ShrinkingIntervals_ERR.v / Archimedean_ERR.v (indices n > N)
    and that of ProcessCore.v (indices N <= n) are equivalent. *)
Lemma Cauchy_SI_iff_PC : forall R : nat -> Q, SI.is_Cauchy R <-> PC.is_Cauchy R.
Proof.
  intro R. unfold SI.is_Cauchy, PC.is_Cauchy. split; intros H eps Heps;
    destruct (H eps Heps) as [N HN].
  - exists (S N). intros m n Hm Hn. apply HN; lia.
  - exists N. intros m n Hm Hn. apply HN; lia.
Qed.

Lemma Cauchy_AR_iff_PC : forall R : nat -> Q, AR.is_Cauchy R <-> PC.is_Cauchy R.
Proof.
  intro R. unfold AR.is_Cauchy, PC.is_Cauchy. split; intros H eps Heps;
    destruct (H eps Heps) as [N HN].
  - exists (S N). intros m n Hm Hn. apply HN; lia.
  - exists N. intros m n Hm Hn. apply HN; lia.
Qed.

(* ========================================================================= *)
(*  3. THE PREDICATE "GIVES THE SQUARE ROOT OF TWO" AND ITS SIGN             *)
(* ========================================================================= *)

(** The square of the process comes below every precision of 2. *)
Definition sq_to_2 (R : nat -> Q) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat -> Qabs (R n * R n - 2) < eps.

(** The predicate as it is written in the chapter: a Cauchy process whose square tends
    to 2. It has no condition on the sign. *)
Definition gives_sqrt2 (R : nat -> Q) : Prop := PC.is_Cauchy R /\ sq_to_2 R.

(** The predicate with the sign: non-negative members and the square tending to 2. The
    Cauchy condition is then a THEOREM, and the class is ONE. *)
Definition gives_pos_sqrt2 (R : nat -> Q) : Prop := (forall n : nat, 0 <= R n) /\ sq_to_2 R.

Lemma Q01 : 0 < 1.
Proof. reflexivity. Qed.

Lemma sq_close_ge1 : forall x : Q, 0 <= x -> Qabs (x * x - 2) < 1 -> 1 <= x.
Proof.
  intros x Hx Hq.
  apply Qabs_Qlt_condition in Hq. destruct Hq as [Hlo _].
  destruct (Qlt_le_dec x 1) as [Hlt | Hge]; [ | exact Hge ].
  exfalso.
  assert (Hxx : x * x <= 1).
  { setoid_replace 1 with (1 * 1) by ring.
    apply Qmult_le_compat_nonneg; split; lra. }
  lra.
Qed.

Lemma two_abs_le : forall x y : Q, 1 <= x -> 1 <= y ->
  2 * Qabs (x - y) <= Qabs (x * x - y * y).
Proof.
  intros x y Hx Hy.
  assert (E : x * x - y * y == (x - y) * (x + y)) by ring.
  rewrite E, Qabs_Qmult.
  rewrite (Qabs_pos (x + y)) by lra.
  rewrite (Qmult_comm 2).
  apply Qmult_le_compat_nonneg; split; try lra; apply Qabs_nonneg.
Qed.

Lemma sq_diff_triangle : forall x y : Q,
  Qabs (x * x - y * y) <= Qabs (x * x - 2) + Qabs (y * y - 2).
Proof.
  intros x y.
  assert (E : x * x - y * y == (x * x - 2) + - (y * y - 2)) by ring.
  rewrite E.
  eapply Qle_trans; [ apply Qabs_triangle | ].
  rewrite Qabs_opp. apply Qle_refl.
Qed.

(** Any two such processes are equivalent: the class is one. *)
Theorem pos_sqrt2_unique : forall R S : nat -> Q,
  gives_pos_sqrt2 R -> gives_pos_sqrt2 S -> PC.process_equiv R S.
Proof.
  intros R S [HR0 HR] [HS0 HS] eps Heps.
  destruct (HR 1 Q01) as [N1 H1].
  destruct (HS 1 Q01) as [N2 H2].
  destruct (HR eps Heps) as [N3 H3].
  destruct (HS eps Heps) as [N4 H4].
  exists (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)). intros n Hn.
  assert (Hx : 1 <= R n) by (apply sq_close_ge1; [ apply HR0 | apply H1; lia ]).
  assert (Hy : 1 <= S n) by (apply sq_close_ge1; [ apply HS0 | apply H2; lia ]).
  pose proof (two_abs_le (R n) (S n) Hx Hy) as HB.
  pose proof (sq_diff_triangle (R n) (S n)) as HC.
  assert (Ha : Qabs (R n * R n - 2) < eps) by (apply H3; lia).
  assert (Hb : Qabs (S n * S n - 2) < eps) by (apply H4; lia).
  set (a := Qabs (R n - S n)) in *.
  set (b := Qabs (R n * R n - S n * S n)) in *.
  set (c := Qabs (R n * R n - 2)) in *.
  set (d := Qabs (S n * S n - 2)) in *.
  lra.
Qed.

(** The Cauchy condition follows from the other two. *)
Theorem pos_sqrt2_Cauchy : forall R : nat -> Q, gives_pos_sqrt2 R -> PC.is_Cauchy R.
Proof.
  intros R [HR0 HR] eps Heps.
  destruct (HR 1 Q01) as [N1 H1].
  destruct (HR eps Heps) as [N3 H3].
  exists (Nat.max N1 N3). intros m n Hm Hn.
  assert (Hx : 1 <= R m) by (apply sq_close_ge1; [ apply HR0 | apply H1; lia ]).
  assert (Hy : 1 <= R n) by (apply sq_close_ge1; [ apply HR0 | apply H1; lia ]).
  pose proof (two_abs_le (R m) (R n) Hx Hy) as HB.
  pose proof (sq_diff_triangle (R m) (R n)) as HC.
  assert (Ha : Qabs (R m * R m - 2) < eps) by (apply H3; lia).
  assert (Hb : Qabs (R n * R n - 2) < eps) by (apply H3; lia).
  set (a := Qabs (R m - R n)) in *.
  set (b := Qabs (R m * R m - R n * R n)) in *.
  set (c := Qabs (R m * R m - 2)) in *.
  set (d := Qabs (R n * R n - 2)) in *.
  lra.
Qed.

Theorem pos_gives_sqrt2 : forall R : nat -> Q, gives_pos_sqrt2 R -> gives_sqrt2 R.
Proof.
  intros R H. split; [ apply pos_sqrt2_Cauchy; exact H | exact (proj2 H) ].
Qed.

Lemma sq_to_2_opp : forall R : nat -> Q, sq_to_2 R -> sq_to_2 (fun n => - R n).
Proof.
  intros R H eps Heps. destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
  assert (E : - R n * - R n - 2 == R n * R n - 2) by ring.
  rewrite E. apply HN; exact Hn.
Qed.

Lemma Cauchy_opp : forall R : nat -> Q, PC.is_Cauchy R -> PC.is_Cauchy (fun n => - R n).
Proof.
  intros R H eps Heps. destruct (H eps Heps) as [N HN]. exists N. intros m n Hm Hn.
  assert (E : - R m - - R n == - (R m - R n)) by ring.
  rewrite E, Qabs_opp. apply HN; assumption.
Qed.

(** Without the sign the predicate of the chapter is satisfied by -R together with R ... *)
Theorem gives_sqrt2_opp : forall R : nat -> Q, gives_sqrt2 R -> gives_sqrt2 (fun n => - R n).
Proof.
  intros R [HC HS]. split; [ apply Cauchy_opp; exact HC | apply sq_to_2_opp; exact HS ].
Qed.

(** ... and R and -R are not equivalent: the predicate without the sign describes two
    classes. *)
Theorem pos_not_equiv_opp : forall R : nat -> Q,
  gives_pos_sqrt2 R -> ~ PC.process_equiv R (fun n => - R n).
Proof.
  intros R [HR0 HR] Heq.
  destruct (HR 1 Q01) as [N1 H1].
  destruct (Heq 1 Q01) as [N HN].
  set (n := Nat.max N N1).
  assert (Hx : 1 <= R n) by (apply sq_close_ge1; [ apply HR0 | apply H1; unfold n; lia ]).
  assert (HNn : Qabs (R n - - R n) < 1) by (apply HN; unfold n; lia).
  assert (E : R n - - R n == R n + R n) by ring.
  rewrite E in HNn. rewrite Qabs_pos in HNn by lra. lra.
Qed.

(* ========================================================================= *)
(*  4. THE PELL PROCESS AND THE CONTINUED-FRACTION PROCESS                   *)
(* ========================================================================= *)

Lemma inv_nat_small : forall eps : Q, 0 < eps ->
  exists N : nat, forall n : nat, (N <= n)%nat -> / inject_Z (Z.of_nat (S n)) < eps.
Proof.
  intros [a b] Heps. unfold Qlt in Heps; simpl in Heps.
  exists (Pos.to_nat b). intros n Hn.
  assert (Hn' : (Z.pos b <= Z.of_nat n)%Z).
  { rewrite <- (positive_nat_Z b). apply Nat2Z.inj_le. exact Hn. }
  change (Z.of_nat (S n)) with (Z.pos (Pos.of_succ_nat n)).
  unfold Qlt, Qinv, inject_Z. simpl.
  rewrite Zpos_P_of_succ_nat. nia.
Qed.

Theorem sx_sq_to_2 : sq_to_2 sx.
Proof.
  intros eps Heps. destruct (inv_nat_small eps Heps) as [N HN].
  exists N. intros n Hn.
  rewrite sx_abs_eq.
  apply Qle_lt_trans with (/ inject_Z (Z.of_nat (S n))); [ | apply HN; exact Hn ].
  apply Qinv_antitone.
  - apply injZ_pos. lia.
  - apply injZ_le. pose proof (qq_ge n) as Hq. destruct (pell_inv n) as [Hpos _]. nia.
Qed.

Lemma cf_pell : forall k : nat,
  (sqrt2_cf_p k = pp k /\ sqrt2_cf_q k = qq k) /\
  (sqrt2_cf_p (S k) = pp (S k) /\ sqrt2_cf_q (S k) = qq (S k)).
Proof.
  induction k as [| k [[Hp Hq] [Hp' Hq']]].
  - unfold pp, qq. simpl. split; split; reflexivity.
  - split; [ split; assumption | ].
    destruct (pell_S (S k)) as [Ep Eq]. destruct (pell_S k) as [Ep0 Eq0].
    change (sqrt2_cf_p (S (S k))) with (2 * sqrt2_cf_p (S k) + sqrt2_cf_p k)%Z.
    change (sqrt2_cf_q (S (S k))) with (2 * sqrt2_cf_q (S k) + sqrt2_cf_q k)%Z.
    rewrite Hp, Hq, Hp', Hq'. split; lia.
Qed.

(** The continued-fraction process coincides stage by stage with the Pell process of
    Sqrt2Approx.v. *)
Lemma cf_eq_sx : forall k : nat, sqrt2_cf k == sx k.
Proof.
  intro k. destruct (cf_pell k) as [[Hp Hq] _].
  unfold sqrt2_cf, sx. rewrite Hp, Hq. reflexivity.
Qed.

Theorem cf_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_cf.
Proof.
  split.
  - intro n. rewrite cf_eq_sx. destruct (sx_range n) as [H _]. lra.
  - intros eps Heps. destruct (sx_sq_to_2 eps Heps) as [N HN]. exists N. intros n Hn.
    rewrite cf_eq_sx. apply HN; exact Hn.
Qed.

(* ========================================================================= *)
(*  5. THE NEWTON PROCESS: THE ERROR FALLS AT LEAST FOURFOLD A STEP          *)
(* ========================================================================= *)

Lemma newton_step_ge1 : forall x : Q, 1 <= x -> 1 <= (x + 2 / x) / 2.
Proof.
  intros x Hx.
  assert (E : (x + 2 / x) / 2 - 1 == ((x - 1) * (x - 1) + 1) / (2 * x)) by (field; lra).
  assert (P : 0 <= ((x - 1) * (x - 1) + 1) / (2 * x)).
  { apply Qle_shift_div_l; [ lra | ]. rewrite Qmult_0_l. nra. }
  set (y := (x + 2 / x) / 2) in *.
  set (z := ((x - 1) * (x - 1) + 1) / (2 * x)) in *.
  lra.
Qed.

Lemma newton_ge1 : forall n : nat, 1 <= sqrt2_newton n.
Proof.
  induction n as [| n IH].
  - change (sqrt2_newton 0) with 1. apply Qle_refl.
  - change (sqrt2_newton (S n)) with ((sqrt2_newton n + 2 / sqrt2_newton n) / 2).
    apply newton_step_ge1. exact IH.
Qed.

(** One Newton step: x'^2 - 2 = (x^2 - 2)^2 / (4 x^2). *)
Lemma newton_step_sq : forall x : Q, 1 <= x ->
  (x + 2 / x) / 2 * ((x + 2 / x) / 2) - 2 == (x * x - 2) * (x * x - 2) / (4 * (x * x)).
Proof. intros x Hx. field. lra. Qed.

Lemma newton_step_quality : forall x : Q, 1 <= x -> Qabs (x * x - 2) <= 1 ->
  Qabs ((x + 2 / x) / 2 * ((x + 2 / x) / 2) - 2) <= Qabs (x * x - 2) / 4.
Proof.
  intros x Hx Hq.
  rewrite (newton_step_sq x Hx).
  assert (Hxx : 1 <= x * x).
  { setoid_replace 1 with (1 * 1) by ring. apply Qmult_le_compat_nonneg; split; lra. }
  set (xx := x * x) in *.
  set (q := xx - 2) in *.
  assert (Ha : 0 <= Qabs q) by apply Qabs_nonneg.
  assert (Hqq : q * q == Qabs q * Qabs q).
  { rewrite <- Qabs_Qmult. symmetry. apply Qabs_pos. nra. }
  assert (Hpos : 0 < 4 * xx) by lra.
  rewrite Qabs_pos.
  - apply Qle_shift_div_r; [ exact Hpos | ].
    setoid_replace (Qabs q / 4 * (4 * xx)) with (Qabs q * xx) by field.
    rewrite Hqq.
    set (a := Qabs q) in *. nra.
  - apply Qle_shift_div_l; [ exact Hpos | ]. rewrite Qmult_0_l. nra.
Qed.

Lemma Qpow2_ge1 : forall n : nat, 1 <= SI.Qpow2 n.
Proof. intro n. unfold SI.Qpow2, Qle. simpl. lia. Qed.

(** The explicit bound: |x_n^2 - 2| <= 1 / 2^n. *)
Lemma newton_quality_bound : forall n : nat,
  Qabs (sqrt2_newton n * sqrt2_newton n - 2) * SI.Qpow2 n <= 1.
Proof.
  induction n as [| n IH].
  - vm_compute. discriminate.
  - change (sqrt2_newton (S n)) with ((sqrt2_newton n + 2 / sqrt2_newton n) / 2).
    pose proof (newton_ge1 n) as Hx.
    pose proof (Qpow2_ge1 n) as HP.
    pose proof (SI.Qpow2_double n) as HD.
    set (x := sqrt2_newton n) in *.
    assert (Ha : 0 <= Qabs (x * x - 2)) by apply Qabs_nonneg.
    assert (Hq1 : Qabs (x * x - 2) <= 1).
    { set (a := Qabs (x * x - 2)) in *. set (P := SI.Qpow2 n) in *. nra. }
    pose proof (newton_step_quality x Hx Hq1) as Hstep.
    rewrite HD.
    set (a' := Qabs ((x + 2 / x) / 2 * ((x + 2 / x) / 2) - 2)) in *.
    set (a := Qabs (x * x - 2)) in *.
    set (P := SI.Qpow2 n) in *.
    assert (Hstep' : 4 * a' <= a).
    { assert (E : a == 4 * (a / 4)) by field. rewrite E. lra. }
    assert (Ha' : 0 <= a') by (unfold a'; apply Qabs_nonneg).
    nra.
Qed.

Theorem newton_sq_to_2 : sq_to_2 sqrt2_newton.
Proof.
  intros eps Heps.
  destruct (SI.Archimedean eps Heps) as [N HN].
  exists N. intros n Hn.
  apply Qle_lt_trans with (1 / SI.Qpow2 n).
  - apply Qle_shift_div_l; [ apply SI.Qpow2_pos | apply newton_quality_bound ].
  - apply Qle_lt_trans with (1 / SI.Qpow2 N); [ | exact HN ].
    apply SI.width_shrinks; [ reflexivity | exact Hn ].
Qed.

Theorem newton_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_newton.
Proof.
  split; [ | exact newton_sq_to_2 ].
  intro n. pose proof (newton_ge1 n). lra.
Qed.

Lemma quality_pos : forall x : Q, 0 < Qabs (x * x - 2).
Proof.
  intro x. destruct (Qlt_le_dec 0 (Qabs (x * x - 2))) as [H | H]; [ exact H | exfalso ].
  apply Qabs_Qle_condition in H. destruct H as [H1 H2].
  apply (Sqrt2Irrational.no_rational_sqrt2 x). lra.
Qed.

(** Every Newton step strictly improves the approximation. *)
Theorem newton_strictly_improves : forall n : nat,
  sqrt2_quality (sqrt2_newton (S n)) < sqrt2_quality (sqrt2_newton n).
Proof.
  intro n. unfold sqrt2_quality.
  change (sqrt2_newton (S n)) with ((sqrt2_newton n + 2 / sqrt2_newton n) / 2).
  pose proof (newton_ge1 n) as Hx.
  pose proof (Qpow2_ge1 n) as HP.
  pose proof (newton_quality_bound n) as HB.
  pose proof (quality_pos (sqrt2_newton n)) as Hpos.
  set (x := sqrt2_newton n) in *.
  assert (Hq1 : Qabs (x * x - 2) <= 1).
  { set (a := Qabs (x * x - 2)) in *. set (P := SI.Qpow2 n) in *. nra. }
  pose proof (newton_step_quality x Hx Hq1) as Hstep.
  set (a' := Qabs ((x + 2 / x) / 2 * ((x + 2 / x) / 2) - 2)) in *.
  set (a := Qabs (x * x - 2)) in *.
  assert (E : a == 4 * (a / 4)) by field.
  set (b := a / 4) in *. lra.
Qed.

(* ========================================================================= *)
(*  6. THE PROCESS OF SHRINKING INTERVALS FOR THE SQUARE EQUAL TO TWO        *)
(* ========================================================================= *)

(** The half is chosen by comparing two rationals — the square of the midpoint and 2:
    the left half if the square of the midpoint is at least 2, else the right one. The
    choice does not refer to the target. *)
Definition sqrt2_choose (s : SI.BisectionState) : bool :=
  Qle_bool 2 ((SI.bis_left s + SI.bis_right s) / 2 * ((SI.bis_left s + SI.bis_right s) / 2)).

Definition sqrt2_start : SI.BisectionState := SI.mkBisection 1 2.

Definition sqrt2_bisect : nat -> Q := SI.bisect_process sqrt2_choose sqrt2_start.

(** The process of shrinking intervals that gives the square root of two IS a Cauchy
    process. *)
Theorem sqrt2_bisect_Cauchy : SI.is_Cauchy sqrt2_bisect.
Proof. apply SI.bisect_is_Cauchy. reflexivity. Qed.

Lemma sqrt2_bisect_inv : forall n : nat,
  1 <= SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n) /\
  SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n) *
    SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n) <= 2 /\
  2 <= SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n) *
    SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n) /\
  SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n) <= 2 /\
  SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n) <=
    SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n).
Proof.
  induction n as [| n IH].
  - simpl. split; [ | split; [ | split; [ | split ] ] ]; unfold Qle; simpl; lia.
  - simpl SI.bisect_iter.
    destruct (SI.bisect_iter sqrt2_choose sqrt2_start n) as [l r].
    simpl in IH. destruct IH as (H1 & H2 & H3 & H4 & H5).
    unfold sqrt2_choose. simpl SI.bis_left. simpl SI.bis_right.
    set (m := (l + r) / 2).
    assert (Hm2 : 2 * m == l + r) by (unfold m; field).
    destruct (Qle_bool 2 (m * m)) eqn:Hc.
    + apply Qle_bool_iff in Hc. unfold SI.bisect_left. simpl. fold m.
      split; [ | split; [ | split; [ | split ] ] ]; try assumption; lra.
    + assert (Hlt : m * m < 2).
      { apply Qnot_le_lt. intro Hle. apply Qle_bool_iff in Hle. rewrite Hle in Hc. discriminate. }
      unfold SI.bisect_right. simpl. fold m.
      split; [ | split; [ | split; [ | split ] ] ]; try assumption; lra.
Qed.

(** The explicit bound: |m_n^2 - 2| <= 4 / 2^n. *)
Lemma sqrt2_bisect_quality : forall n : nat,
  Qabs (sqrt2_bisect n * sqrt2_bisect n - 2) <= 4 / SI.Qpow2 n.
Proof.
  intro n. unfold sqrt2_bisect, SI.bisect_process.
  pose proof (sqrt2_bisect_inv n) as (H1 & H2 & H3 & H4 & H5).
  pose proof (SI.bisect_width_n sqrt2_choose sqrt2_start n) as Hw.
  change (SI.bis_right sqrt2_start - SI.bis_left sqrt2_start) with (2 - 1) in Hw.
  pose proof (SI.Qpow2_pos n) as Hp.
  set (l := SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n)) in *.
  set (r := SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n)) in *.
  set (P := SI.Qpow2 n) in *.
  set (m := (l + r) / 2).
  assert (Hm2 : 2 * m == l + r) by (unfold m; field).
  assert (Hw4 : 4 / P == 4 * (r - l)).
  { rewrite Hw. field. lra. }
  rewrite Hw4.
  apply Qabs_Qle_condition. split; nra.
Qed.

Theorem sqrt2_bisect_sq_to_2 : sq_to_2 sqrt2_bisect.
Proof.
  intros eps Heps.
  assert (H4 : 0 < 4) by reflexivity.
  destruct (SI.Archimedean_width 4 eps H4 Heps) as [N HN].
  exists N. intros n Hn.
  apply Qle_lt_trans with (4 / SI.Qpow2 n); [ apply sqrt2_bisect_quality | ].
  apply Qle_lt_trans with (4 / SI.Qpow2 N); [ | exact HN ].
  apply SI.width_shrinks; [ exact H4 | exact Hn ].
Qed.

Theorem sqrt2_bisect_gives_pos_sqrt2 : gives_pos_sqrt2 sqrt2_bisect.
Proof.
  split; [ | exact sqrt2_bisect_sq_to_2 ].
  intro n. unfold sqrt2_bisect, SI.bisect_process.
  pose proof (sqrt2_bisect_inv n) as (H1 & H2 & H3 & H4 & H5).
  set (l := SI.bis_left (SI.bisect_iter sqrt2_choose sqrt2_start n)) in *.
  set (r := SI.bis_right (SI.bisect_iter sqrt2_choose sqrt2_start n)) in *.
  set (m := (l + r) / 2).
  assert (Hm2 : 2 * m == l + r) by (unfold m; field).
  lra.
Qed.

(* ========================================================================= *)
(*  7. THREE PROCESSES GIVE THE ROOT AND ARE PAIRWISE EQUIVALENT             *)
(* ========================================================================= *)

Theorem newton_gives_sqrt2 : gives_sqrt2 sqrt2_newton.
Proof. apply pos_gives_sqrt2. exact newton_gives_pos_sqrt2. Qed.

Theorem cf_gives_sqrt2 : gives_sqrt2 sqrt2_cf.
Proof. apply pos_gives_sqrt2. exact cf_gives_pos_sqrt2. Qed.

Theorem bisect_gives_sqrt2 : gives_sqrt2 sqrt2_bisect.
Proof. apply pos_gives_sqrt2. exact sqrt2_bisect_gives_pos_sqrt2. Qed.

Theorem newton_Cauchy_SI : SI.is_Cauchy sqrt2_newton.
Proof. apply Cauchy_SI_iff_PC. exact (proj1 newton_gives_sqrt2). Qed.

Theorem cf_Cauchy_SI : SI.is_Cauchy sqrt2_cf.
Proof. apply Cauchy_SI_iff_PC. exact (proj1 cf_gives_sqrt2). Qed.

(** The Newton process and the continued-fraction process are equivalent. *)
Theorem newton_cf_equiv : PC.process_equiv sqrt2_newton sqrt2_cf.
Proof. apply pos_sqrt2_unique; [ exact newton_gives_pos_sqrt2 | exact cf_gives_pos_sqrt2 ]. Qed.

Theorem newton_bisect_equiv : PC.process_equiv sqrt2_newton sqrt2_bisect.
Proof. apply pos_sqrt2_unique; [ exact newton_gives_pos_sqrt2 | exact sqrt2_bisect_gives_pos_sqrt2 ]. Qed.

Theorem cf_bisect_equiv : PC.process_equiv sqrt2_cf sqrt2_bisect.
Proof. apply pos_sqrt2_unique; [ exact cf_gives_pos_sqrt2 | exact sqrt2_bisect_gives_pos_sqrt2 ]. Qed.

(** The predicate of the chapter (without the sign) is satisfied by two non-equivalent
    processes. *)
Theorem page_predicate_two_classes :
  gives_sqrt2 sqrt2_cf /\ gives_sqrt2 (fun n => - sqrt2_cf n) /\
  ~ PC.process_equiv sqrt2_cf (fun n => - sqrt2_cf n).
Proof.
  split; [ exact cf_gives_sqrt2 | split ].
  - apply gives_sqrt2_opp. exact cf_gives_sqrt2.
  - apply pos_not_equiv_opp. exact cf_gives_pos_sqrt2.
Qed.

(* ========================================================================= *)
(*  8. THE SHRINKING THEOREM WITH INTERVALS IN THE PREMISE                   *)
(* ========================================================================= *)

(** shrinking_interval_Cauchy has no intervals in its statement; here is the form with
    nested intervals in the premise. *)
Theorem interval_process_Cauchy :
  forall (I : SI.IntervalProcess) (R : nat -> Q) (w : Q), 0 < w ->
  (forall m n : nat, (m <= n)%nat -> SI.ip_left I m <= R n <= SI.ip_right I m) ->
  (forall m : nat, SI.ip_right I m - SI.ip_left I m <= w / SI.Qpow2 m) ->
  SI.is_Cauchy R.
Proof.
  intros I R w Hw Hin Hwid.
  apply (SI.shrinking_interval_Cauchy R 0 w Hw).
  intros m n Hmn.
  apply Qle_trans with (SI.ip_right I m - SI.ip_left I m).
  - apply SI.points_in_interval_diff; [ apply Hin; lia | apply Hin; exact Hmn ].
  - setoid_replace (w - 0) with w by ring. apply Hwid.
Qed.

Theorem newton_distance_bound : forall m n : nat, (m <= n)%nat ->
  Qabs (sqrt2_newton m - sqrt2_newton n) <= (1 - 0) / SI.Qpow2 m.
Proof.
  intros m n Hmn.
  pose proof (two_abs_le _ _ (newton_ge1 m) (newton_ge1 n)) as HB.
  pose proof (sq_diff_triangle (sqrt2_newton m) (sqrt2_newton n)) as HC.
  assert (Hm : Qabs (sqrt2_newton m * sqrt2_newton m - 2) <= 1 / SI.Qpow2 m).
  { apply Qle_shift_div_l; [ apply SI.Qpow2_pos | apply newton_quality_bound ]. }
  assert (Hn : Qabs (sqrt2_newton n * sqrt2_newton n - 2) <= 1 / SI.Qpow2 m).
  { apply Qle_trans with (1 / SI.Qpow2 n).
    - apply Qle_shift_div_l; [ apply SI.Qpow2_pos | apply newton_quality_bound ].
    - apply SI.width_shrinks; [ reflexivity | exact Hmn ]. }
  setoid_replace ((1 - 0) / SI.Qpow2 m) with (1 / SI.Qpow2 m) by (unfold Qdiv; ring).
  set (a := Qabs (sqrt2_newton m - sqrt2_newton n)) in *.
  set (b := Qabs (sqrt2_newton m * sqrt2_newton m - sqrt2_newton n * sqrt2_newton n)) in *.
  set (c := Qabs (sqrt2_newton m * sqrt2_newton m - 2)) in *.
  set (d := Qabs (sqrt2_newton n * sqrt2_newton n - 2)) in *.
  set (e := 1 / SI.Qpow2 m) in *.
  lra.
Qed.

(** The Newton process meets the premise of shrinking_interval_Cauchy as soon as its own
    bound is proved. *)
Theorem newton_Cauchy_by_shrinking : SI.is_Cauchy sqrt2_newton.
Proof.
  apply (SI.shrinking_interval_Cauchy sqrt2_newton 0 1); [ reflexivity | exact newton_distance_bound ].
Qed.

(* ========================================================================= *)
(*  9. THE NAME sqrt2_process IN THE REPOSITORY: THE NEWTON PROCESS ITSELF   *)
(* ========================================================================= *)

(** QPhysicsProcesses.sqrt2_process is a function nat -> Q — the Newton process itself,
    not a predicate on processes. *)
Lemma repo_sqrt2_process_is_newton :
  forall K : nat, QPhysicsProcesses.sqrt2_process K = sqrt2_newton K.
Proof.
  induction K as [| K IH].
  - reflexivity.
  - change (QPhysicsProcesses.sqrt2_process (S K))
      with ((QPhysicsProcesses.sqrt2_process K + 2 / QPhysicsProcesses.sqrt2_process K) / 2).
    change (sqrt2_newton (S K)) with ((sqrt2_newton K + 2 / sqrt2_newton K) / 2).
    rewrite IH. reflexivity.
Qed.
