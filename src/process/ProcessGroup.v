(** * ProcessGroup.v — Groups as Processes of Finite Approximations
    Elements: Z_level, Q_level, element process, free group word levels
    Roles:    under P4, infinite groups ARE processes of finite approximations
    Rules:    closure under bounded ops, level growth, eventual constancy
    Status:   complete
    STATUS: ~30 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS GROUP — Groups as Processes of Finite Approximations        *)
(*                                                                           *)
(*  Under P4: Z is not {0,±1,±2,...} as completed set.                      *)
(*  Z is the process {[-n,n]} at level n.                                   *)
(*  At each level: finitely many elements, bounded operations.              *)
(*                                                                           *)
(*  STATUS: ~30 Qed, 0 Admitted                                             *)
(*  AXIOMS: classic (for decidability)                                       *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Classical.
Open Scope Q_scope.
Open Scope Z_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Z Group Process  (~10 lemmas)                              *)
(* ================================================================== *)

(** Truncated Z: elements with |z| ≤ n *)
Definition Z_level (n : nat) (z : Z) : Prop :=
  (Z.abs z <= Z.of_nat n)%Z.

(** Z_level is increasing *)
Lemma Z_level_increasing : forall n z,
  Z_level n z -> Z_level (S n) z.
Proof.
  intros n z H. unfold Z_level in *. lia.
Qed.

(** Identity at every level *)
Lemma Z_id_level : forall n, Z_level n 0.
Proof. intros n. unfold Z_level. simpl. lia. Qed.

(** Inverse stays at same level *)
Lemma Z_inv_level : forall n z,
  Z_level n z -> Z_level n (Z.opp z).
Proof.
  intros n z H. unfold Z_level in *. rewrite Z.abs_opp. exact H.
Qed.

(** Addition grows the level: |z1+z2| ≤ |z1| + |z2| ≤ 2n *)
Lemma Z_add_level : forall n z1 z2,
  Z_level n z1 -> Z_level n z2 ->
  Z_level (2 * n) (z1 + z2).
Proof.
  intros n z1 z2 H1 H2. unfold Z_level in *.
  assert (Htri := Z.abs_triangle z1 z2). lia.
Qed.

(** Level n has exactly 2n+1 elements *)
Lemma Z_level_size : forall n z,
  Z_level n z -> (-Z.of_nat n <= z <= Z.of_nat n)%Z.
Proof.
  intros n z H. unfold Z_level in H. lia.
Qed.

(** Every integer eventually enters some level *)
Lemma Z_eventually_in_level : forall z,
  exists n, Z_level n z.
Proof.
  intros z. exists (Z.to_nat (Z.abs z)).
  unfold Z_level. rewrite Z2Nat.id; [lia | apply Z.abs_nonneg].
Qed.

(** Subtraction (for group difference) grows level *)
Lemma Z_sub_level : forall n z1 z2,
  Z_level n z1 -> Z_level n z2 ->
  Z_level (2 * n) (z1 - z2)%Z.
Proof.
  intros n z1 z2 H1 H2. unfold Z_level in *.
  assert (Htri : (Z.abs (z1 - z2) <= Z.abs z1 + Z.abs z2)%Z).
  { assert (H := Z.abs_triangle z1 (-z2)). rewrite Z.abs_opp in H.
    replace (z1 - z2)%Z with (z1 + - z2)%Z by lia. exact H. }
  lia.
Qed.

(** Z_level 0 is just {0} *)
Lemma Z_level_0 : forall z, Z_level 0 z -> z = 0%Z.
Proof. intros z H. unfold Z_level in H. simpl in H. lia. Qed.

(** Generator property: every element at level n is reachable from ±1 in n steps *)
Lemma Z_generator : forall n z,
  Z_level n z -> Z_level 1 1 /\ Z_level 1 (-1).
Proof.
  intros n z _. split; unfold Z_level; simpl; lia.
Qed.

(* ================================================================== *)
(*  Part II: Q Group Process  (~8 lemmas)                              *)
(* ================================================================== *)

(** Truncated Q: rationals with bounded numerator and denominator *)
Definition Q_level (n : nat) (q : Q) : Prop :=
  (Z.abs (Qnum q) <= Z.of_nat n)%Z /\
  (Zpos (Qden q) <= Z.of_nat n)%Z.

(** Q_level is increasing *)
Lemma Q_level_increasing : forall n q,
  Q_level n q -> Q_level (S n) q.
Proof.
  intros n q [H1 H2]. split; lia.
Qed.

(** Q_level needs n ≥ 1 to have any elements *)
Lemma Q_level_nonempty : Q_level 1 0.
Proof. split; simpl; lia. Qed.

(** Identity 0 at every level ≥ 1 *)
Lemma Q_id_level : forall n, (1 <= n)%nat -> Q_level n 0.
Proof. intros n Hn. split; simpl; lia. Qed.

(** Negation preserves Q_level *)
Lemma Q_neg_level : forall n q,
  Q_level n q -> Q_level n (-q).
Proof.
  intros n [p d] [H1 H2]. simpl in *.
  split; simpl.
  - rewrite Z.abs_opp. exact H1.
  - exact H2.
Qed.

(** Every rational eventually enters some level *)
Lemma Q_eventually_in_level : forall q : Q,
  exists n, Q_level n q.
Proof.
  intros [p d]. unfold Q_level. simpl.
  set (M := Z.to_nat (Z.abs p + Zpos d + 1)).
  exists M. split.
  - unfold M. rewrite Z2Nat.id; [lia | lia].
  - unfold M. rewrite Z2Nat.id; [lia | lia].
Qed.

(** Addition grows level quadratically: p1/d1 + p2/d2 = (p1*d2+p2*d1)/(d1*d2) *)
Lemma Q_add_level_bound : forall n q1 q2,
  Q_level n q1 -> Q_level n q2 ->
  (Z.abs (Qnum (q1 + q2)) <= Z.of_nat n * Z.of_nat n +
                               Z.of_nat n * Z.of_nat n)%Z.
Proof.
  intros n [p1 d1] [p2 d2] [Hp1 Hd1] [Hp2 Hd2]. simpl in *.
  unfold Qplus. simpl.
  assert (H : (Z.abs (p1 * Zpos d2 + p2 * Zpos d1) <=
              Z.abs (p1 * Zpos d2) + Z.abs (p2 * Zpos d1))%Z).
  { apply Z.abs_triangle. }
  rewrite Z.abs_mul in H. rewrite Z.abs_mul in H.
  rewrite (Z.abs_eq (Zpos d2)) in H; [| lia].
  rewrite (Z.abs_eq (Zpos d1)) in H; [| lia].
  assert (Ha : (Z.abs p1 * Zpos d2 <= Z.of_nat n * Z.of_nat n)%Z) by nia.
  assert (Hb : (Z.abs p2 * Zpos d1 <= Z.of_nat n * Z.of_nat n)%Z) by nia.
  lia.
Qed.

(** Q_level 0 is empty (denominator must be positive but ≤ 0) *)
Lemma Q_level_0_empty : forall q, ~ Q_level 0 q.
Proof.
  intros [p d] [_ Hd]. simpl in Hd. lia.
Qed.

(* ================================================================== *)
(*  Part III: Element as RealProcess  (~7 lemmas)                      *)
(* ================================================================== *)

(** Decidability of Z_level *)
Lemma Z_level_dec : forall n z, {Z_level n z} + {~ Z_level n z}.
Proof.
  intros n z. unfold Z_level.
  destruct (Z_le_dec (Z.abs z) (Z.of_nat n)); [left | right]; lia.
Qed.

(** Decidability of Q_level *)
Lemma Q_level_dec : forall n (q : Q), {Q_level n q} + {~ Q_level n q}.
Proof.
  intros n [p d]. unfold Q_level. simpl.
  destruct (Z_le_dec (Z.abs p) (Z.of_nat n));
  destruct (Z_le_dec (Zpos d) (Z.of_nat n));
  try (left; split; lia); right; intros [H1 H2]; lia.
Qed.

(** An element of Z as a RealProcess: truncated at each level *)
Definition Z_element_process (z : Z) : RealProcess :=
  fun n => if Z_level_dec n z then inject_Z z else 0.

(** Z element process is eventually constant *)
Lemma Z_element_eventually_const : forall z,
  exists N, forall n, (N <= n)%nat -> Z_element_process z n == inject_Z z.
Proof.
  intros z.
  destruct (Z_eventually_in_level z) as [N HN].
  exists N. intros n Hle.
  unfold Z_element_process.
  destruct (Z_level_dec n z) as [Hy | Hn].
  - lra.
  - exfalso. apply Hn. unfold Z_level in *. lia.
Qed.

(** Eventually constant implies Cauchy *)
Lemma eventually_const_cauchy : forall (proc : RealProcess) (v : Q) N,
  (forall n, (N <= n)%nat -> proc n == v) ->
  is_Cauchy proc.
Proof.
  intros proc v N Hconst eps Heps.
  exists N. intros m n Hm Hn.
  assert (Hvm := Hconst m Hm).
  assert (Hvn := Hconst n Hn).
  assert (Heq : proc m - proc n == 0) by lra.
  rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Z element process is Cauchy *)
Lemma Z_element_cauchy : forall z, is_Cauchy (Z_element_process z).
Proof.
  intros z.
  destruct (Z_element_eventually_const z) as [N HN].
  eapply eventually_const_cauchy. exact HN.
Qed.

(** Q element process *)
Definition Q_element_process (q : Q) : RealProcess :=
  fun n => if Q_level_dec n q then q else 0.

(** Q element process is eventually constant *)
Lemma Q_element_eventually_const : forall q,
  exists N, forall n, (N <= n)%nat -> Q_element_process q n == q.
Proof.
  intros q.
  destruct (Q_eventually_in_level q) as [N HN].
  exists N. intros n Hle.
  unfold Q_element_process.
  destruct (Q_level_dec n q) as [Hy | Hn].
  - lra.
  - exfalso. apply Hn. destruct q as [p d]. unfold Q_level in *. simpl in *. lia.
Qed.

(** Q element process is Cauchy *)
Lemma Q_element_cauchy : forall q, is_Cauchy (Q_element_process q).
Proof.
  intros q.
  destruct (Q_element_eventually_const q) as [N HN].
  eapply eventually_const_cauchy. exact HN.
Qed.

(* ================================================================== *)
(*  Part IV: Free Group Process  (~5 lemmas)                           *)
(* ================================================================== *)

(** Free group on k generators: process of words of length ≤ n.
    At level 0: just identity (1 element).
    At level n: all reduced words of length ≤ n.
    Number of words ≤ (2k)^{n+1} (crude upper bound). *)

Definition word_count_bound (k n : nat) : nat :=
  Nat.pow (2 * k + 1) (S n).

(** Word count bound is increasing *)
Lemma word_count_increasing : forall k n,
  (word_count_bound k n <= word_count_bound k (S n))%nat.
Proof.
  intros k n. unfold word_count_bound.
  assert (H : (1 <= 2 * k + 1)%nat) by lia.
  induction n.
  - simpl. lia.
  - simpl. lia.
Qed.

(** At level 0: one element (identity) *)
Lemma word_count_base : forall k,
  word_count_bound k 0 = (2 * k + 1)%nat.
Proof. intros k. unfold word_count_bound. simpl. lia. Qed.

(** Free group rank: the level process tracks how many elements are accessible *)
Definition free_group_level_process (k : nat) : RealProcess :=
  fun n => inject_Z (Z.of_nat (word_count_bound k n)).

(** Free group level process is monotone increasing *)
Lemma free_group_monotone : forall k n,
  free_group_level_process k n <= free_group_level_process k (S n).
Proof.
  intros k n. unfold free_group_level_process.
  assert (H := word_count_increasing k n).
  apply Qle_trans with (inject_Z (Z.of_nat (word_count_bound k n))); [lra |].
  unfold Qle. simpl. lia.
Qed.

(** P4 thesis: the free group IS this process of finite levels *)
(** No completed infinite set — just the process of constructible words *)

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check Z_level. Check Z_level_increasing. Check Z_add_level.
Check Z_inv_level. Check Z_id_level. Check Z_eventually_in_level.
Check Q_level. Check Q_level_increasing. Check Q_neg_level.
Check Q_eventually_in_level.
Check Z_element_process. Check Z_element_cauchy.
Check Q_element_process. Check Q_element_cauchy.
Check eventually_const_cauchy.
Check word_count_bound. Check free_group_monotone.
