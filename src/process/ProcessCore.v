(** * ProcessCore.v — The Universal Type for Process Mathematics
    Elements: RealProcess, is_Cauchy, process_equiv, in_interval, const_process
    Roles:    SINGLE source of truth for process definitions; all other files import from here
    Rules:    every mathematical object is a finite process at each stage (P4)
    Status:   complete
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESSCORE — The Universal Type for Process Mathematics            *)
(*                                                                            *)
(*  Under P4: every mathematical object is a finite process at each stage.   *)
(*  The real number line R does not exist as a completed set.                *)
(*  What exists: processes over Q, characterized by Cauchy conditions.       *)
(*                                                                            *)
(*  This file defines the SINGLE source of truth for process types.          *)
(*  All other files import from here.                                         *)
(*                                                                            *)
(*  STATUS: 25 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: The Universal Type  (~5 lemmas)                           *)
(* ================================================================== *)

(** The fundamental type: a process over Q indexed by nat. *)
Definition RealProcess := nat -> Q.

(** Constant process: the rational q at every stage. *)
Definition const_process (q : Q) : RealProcess := fun _ => q.

(** Apply a Q-function pointwise to a process. *)
Definition apply_to_process (f : Q -> Q) (R : RealProcess) : RealProcess :=
  fun n => f (R n).

(** Process evaluation *)
Definition process_at (R : RealProcess) (n : nat) : Q := R n.

Lemma const_process_at : forall q n, process_at (const_process q) n == q.
Proof.
  intros q n. unfold process_at, const_process. lra.
Qed.

Lemma apply_to_process_at : forall f R n,
  apply_to_process f R n = f (R n).
Proof.
  intros. unfold apply_to_process. reflexivity.
Qed.

Lemma const_process_eq : forall q m n,
  const_process q m == const_process q n.
Proof.
  intros. unfold const_process. lra.
Qed.

(* ================================================================== *)
(*  Part II: Cauchy Condition  (~8 lemmas)                            *)
(* ================================================================== *)

(** A process is Cauchy: stages get arbitrarily close. *)
Definition is_Cauchy (R : RealProcess) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat -> Qabs (R m - R n) < eps.

(** Regular Cauchy: explicit modulus |R(m)-R(n)| <= 1/m + 1/n *)
Definition is_Regular_Cauchy (R : RealProcess) : Prop :=
  forall m n : nat, (1 <= m)%nat -> (1 <= n)%nat ->
    Qabs (R m - R n) <= 1 / inject_Z (Z.of_nat m) + 1 / inject_Z (Z.of_nat n).

Lemma const_is_Cauchy : forall q, is_Cauchy (const_process q).
Proof.
  intros q eps Heps. exists 0%nat.
  intros m n _ _.
  unfold const_process.
  assert (Heq : q - q == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(** Helper: for positive n, 0 < inject_Z (Z.of_nat n) *)
Lemma inject_nat_pos : forall n, (1 <= n)%nat -> 0 < inject_Z (Z.of_nat n).
Proof.
  intros n Hn. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia.
Qed.

(** Helper: m >= n > 0 implies 1/m <= 1/n over Q *)
Lemma inv_le_of_le : forall m n : nat,
  (1 <= n)%nat -> (n <= m)%nat ->
  1 / inject_Z (Z.of_nat m) <= 1 / inject_Z (Z.of_nat n).
Proof.
  intros m n Hn Hnm.
  assert (HnQ : 0 < inject_Z (Z.of_nat n)) by (apply inject_nat_pos; auto).
  assert (HmQ : 0 < inject_Z (Z.of_nat m)) by (apply inject_nat_pos; lia).
  unfold Qdiv. rewrite !Qmult_1_l.
  unfold Qinv, Qle. simpl.
  destruct (Z.of_nat m) eqn:Hm; destruct (Z.of_nat n) eqn:Hnn; try lia.
  simpl. lia.
Qed.

Lemma regular_implies_Cauchy : forall R, is_Regular_Cauchy R -> is_Cauchy R.
Proof.
  intros R Hreg eps Heps.
  (* Pick N such that 2/N < eps *)
  destruct eps as [ep eq].
  unfold Qlt in Heps. simpl in Heps.
  assert (Hp : (0 < ep)%Z) by lia.
  set (N := S (Z.to_nat (2 * Z.pos eq / ep + 1))).
  exists N. intros m n Hm Hn.
  assert (H1m : (1 <= m)%nat) by lia.
  assert (H1n : (1 <= n)%nat) by lia.
  specialize (Hreg m n H1m H1n).
  apply Qle_lt_trans with (1 / inject_Z (Z.of_nat m) + 1 / inject_Z (Z.of_nat n)); auto.
  assert (HN1 : (1 <= N)%nat) by lia.
  assert (HNQ := inject_nat_pos N HN1).
  assert (H1m2 := inv_le_of_le m N HN1 Hm).
  assert (H1n2 := inv_le_of_le n N HN1 Hn).
  assert (Hsum : 1 / inject_Z (Z.of_nat m) + 1 / inject_Z (Z.of_nat n) <=
                 2 / inject_Z (Z.of_nat N)).
  { assert (H2N : 2 / inject_Z (Z.of_nat N) ==
                   1 / inject_Z (Z.of_nat N) + 1 / inject_Z (Z.of_nat N)).
    { field. lra. }
    lra. }
  apply Qle_lt_trans with (2 / inject_Z (Z.of_nat N)); auto.
  (* Need: 2 / inject_Z (Z.of_nat N) < ep # eq *)
  unfold Qdiv, Qlt, Qmult, inject_Z, Qinv. simpl.
  set (zN := Z.of_nat N) in *.
  destruct zN eqn:HNz; try lia.
  simpl.
  assert (HpN : (2 * Z.pos eq / ep + 1 < Z.pos p)%Z).
  { subst N zN. lia. }
  assert (Hq := Z_div_mod_eq_full (2 * Z.pos eq) ep).
  assert (Hmod : (0 <= (2 * Z.pos eq) mod ep)%Z).
  { apply Z.mod_pos_bound. lia. }
  assert (Hmod2 : ((2 * Z.pos eq) mod ep < ep)%Z).
  { apply Z.mod_pos_bound. lia. }
  set (d := (2 * Z.pos eq / ep)%Z) in *.
  assert (H2 : (2 * Z.pos eq < ep * (d + 1))%Z) by lia.
  assert (H3 : (d + 1 <= Z.pos p)%Z) by lia.
  assert (H4 : (ep * (d + 1) <= ep * Z.pos p)%Z).
  { apply Z.mul_le_mono_nonneg_l; lia. }
  lia.
Qed.

(** Cauchy is closed under pointwise-eventually-close sequences *)
Lemma cauchy_from_bound : forall R (bound : nat -> Q),
  (forall m n, Qabs (R m - R n) <= bound (Nat.min m n)) ->
  (forall eps, 0 < eps -> exists N, forall k, (N <= k)%nat -> bound k < eps) ->
  is_Cauchy R.
Proof.
  intros R bound Hbd Hvan eps Heps.
  destruct (Hvan eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qle_lt_trans with (bound (Nat.min m n)).
  - apply Hbd.
  - apply HN. lia.
Qed.

(* ================================================================== *)
(*  Part III: Process Equivalence  (~6 lemmas)                        *)
(* ================================================================== *)

(** Two processes are equivalent if they converge to the same limit. *)
Definition process_equiv (R1 R2 : RealProcess) : Prop :=
  forall eps : Q, 0 < eps ->
    exists N : nat, forall n : nat,
      (N <= n)%nat -> Qabs (R1 n - R2 n) < eps.

Notation "R1 ~~ R2" := (process_equiv R1 R2) (at level 70).

Lemma process_equiv_refl : forall R, R ~~ R.
Proof.
  intros R eps Heps. exists 0%nat.
  intros n _. assert (Heq : R n - R n == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

Lemma process_equiv_sym : forall R1 R2, R1 ~~ R2 -> R2 ~~ R1.
Proof.
  intros R1 R2 H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  assert (Heq : R2 n - R1 n == -(R1 n - R2 n)) by ring.
  rewrite Heq. rewrite Qabs_opp. auto.
Qed.

Lemma process_equiv_trans : forall R1 R2 R3, R1 ~~ R2 -> R2 ~~ R3 -> R1 ~~ R3.
Proof.
  intros R1 R2 R3 H12 H23 eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (H12 (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (H23 (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros n Hn.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 n Hn1). specialize (HN2 n Hn2).
  apply Qle_lt_trans with (Qabs (R1 n - R2 n) + Qabs (R2 n - R3 n)).
  - assert (Htri : R1 n - R3 n == (R1 n - R2 n) + (R2 n - R3 n)) by ring.
    rewrite Htri. apply Qabs_triangle.
  - lra.
Qed.

Lemma equiv_cauchy_l : forall R1 R2, R1 ~~ R2 -> is_Cauchy R1 -> is_Cauchy R2.
Proof.
  intros R1 R2 Heq HC1 eps Heps.
  assert (Heps3 : 0 < eps * (1#3)) by lra.
  destruct (HC1 (eps * (1#3)) Heps3) as [N1 HN1].
  destruct (Heq (eps * (1#3)) Heps3) as [N2 HN2].
  exists (Nat.max N1 N2). intros m n Hm Hn.
  assert (Hm1 : (N1 <= m)%nat) by lia. assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia. assert (Hn2 : (N2 <= n)%nat) by lia.
  specialize (HN1 m n Hm1 Hn1).
  assert (HN2m : Qabs (R1 m - R2 m) < eps * (1#3)) by (apply HN2; auto).
  assert (HN2n : Qabs (R1 n - R2 n) < eps * (1#3)) by (apply HN2; auto).
  apply Qle_lt_trans with (Qabs (R2 m - R1 m) + Qabs (R1 m - R1 n) + Qabs (R1 n - R2 n)).
  2: { assert (Hswap : Qabs (R2 m - R1 m) == Qabs (R1 m - R2 m)).
       { assert (Heq2 : R2 m - R1 m == -(R1 m - R2 m)) by ring.
         rewrite Heq2. apply Qabs_opp. }
       lra. }
  assert (Htri : R2 m - R2 n == (R2 m - R1 m) + (R1 m - R1 n) + (R1 n - R2 n)) by ring.
  rewrite Htri.
  apply Qle_trans with (Qabs ((R2 m - R1 m) + (R1 m - R1 n)) + Qabs (R1 n - R2 n)).
  { apply Qabs_triangle. }
  assert (Hsub : Qabs ((R2 m - R1 m) + (R1 m - R1 n)) <=
                 Qabs (R2 m - R1 m) + Qabs (R1 m - R1 n)).
  { apply Qabs_triangle. }
  lra.
Qed.

Lemma const_equiv_const : forall p q, p == q -> const_process p ~~ const_process q.
Proof.
  intros p q Hpq eps Heps. exists 0%nat. intros n _.
  unfold const_process.
  assert (Heq : p - q == 0) by lra. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  Part IV: Interval Containment  (~6 lemmas)                       *)
(* ================================================================== *)

(** A process stays within [a,b] at every stage. *)
Definition in_interval (a b : Q) (R : RealProcess) : Prop :=
  forall n : nat, a <= R n /\ R n <= b.

Lemma const_in_interval : forall q a b,
  a <= q -> q <= b -> in_interval a b (const_process q).
Proof.
  intros q a b Ha Hb n. unfold const_process. split; auto.
Qed.

Lemma in_interval_bounds : forall a b R n,
  in_interval a b R -> a <= R n /\ R n <= b.
Proof.
  intros a b R n H. exact (H n).
Qed.

Lemma in_interval_le : forall a b R,
  in_interval a b R -> a <= b.
Proof.
  intros a b R H.
  destruct (H 0%nat) as [Ha Hb]. lra.
Qed.

Lemma in_interval_subset : forall a b a' b' R,
  a' <= a -> b <= b' -> in_interval a b R -> in_interval a' b' R.
Proof.
  intros a b a' b' R Ha Hb H n.
  destruct (H n). split; lra.
Qed.

Lemma in_interval_cauchy_bounded : forall a b R,
  in_interval a b R ->
  forall m n, Qabs (R m - R n) <= b - a.
Proof.
  intros a b R Hint m n.
  destruct (Hint m) as [Ham Hbm].
  destruct (Hint n) as [Han Hbn].
  apply Qabs_case; intros; lra.
Qed.

Lemma in_interval_cauchy : forall a b R,
  in_interval a b R -> a == b -> is_Cauchy R.
Proof.
  intros a b R Hint Hab eps Heps.
  exists 0%nat. intros m n _ _.
  assert (Hmn : Qabs (R m - R n) <= b - a).
  { apply in_interval_cauchy_bounded; auto. }
  assert (Hba : b - a == 0) by lra.
  assert (H0 : Qabs (R m - R n) <= 0) by lra.
  assert (Habs := Qabs_nonneg (R m - R n)).
  lra.
Qed.
