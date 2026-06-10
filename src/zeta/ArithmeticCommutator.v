(* ArithmeticCommutator.v *)
(* Arithmetic Heisenberg: Commutator of multiplicative and additive adjacency *)
(* June 2026 — DERIVED, NOT TABULATED.  tr_comm_sq_arith was a hardcoded
   lookup table (if K=12 then -128 ...), asserted rather than computed; the
   operators it claimed to describe (mult_adj/add_adj, DivisibilityGraph.v)
   were imported but unused.  Now Tr([M,A]^2) IS the matrix computation on
   the K-node truncation, and the former table values are THEOREMS verified
   by vm_compute from the real operators (they matched: -128/-268/-476).
   NEW general theorem: Tr([M,A]^2) <= 0 for EVERY K, derived from the
   antisymmetry of the commutator of symmetric operators — the honest
   "uncertainty-flavored" content behind the Heisenberg framing.

   ============ E/R/R разбор ============
     Elements: узлы 1..K (натуральные числа); матрицы смежности
               mult_adj (делимость) и add_adj (соседство ±1) — РЕАЛЬНЫЕ
               операторы из DivisibilityGraph.v.
     Roles:    мультипликативная и аддитивная структуры N как два
               несовместимых разбиения ролей; коммутатор [M,A] — мера их
               несовместимости; след Tr([M,A]^2) — её скаляр.
     Rules:    матричное произведение/след на K-узловом обрезе (конечные
               суммы, P4); симметрия M и A => антисимметрия [M,A] =>
               Tr([M,A]^2) = -Sigma C_ij^2 <= 0 — ОБЩАЯ теорема, не таблица.
   ДИАГНОСТИКА (P4): прежняя версия приписывала Элементу (таблице значений)
   роль вывода из Правил (операторов) — значения были верными ДАННЫМИ, но
   эпистемический статус "вычислено" был не заслужен. Теперь вывод честный:
   определение = вычисление, негативность = теорема, конкретика = vm_compute.
   ЧЕСТНАЯ ГРАНИЦА: это конечно-узловая несовместимость двух структур N
   ("арифметический Гейзенберг" как ФРЕЙМИНГ); неравенство неопределённости
   с нормами состояний и связь с нулями дзеты здесь НЕ выводятся.

   STATUS: 22 Qed, 0 Admitted, 0 axioms *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From ToS Require Import DivisibilityGraph.

(* ===================================================================== *)
(*  Finite matrix calculus on the K-node truncation                       *)
(* ===================================================================== *)

(* Sum over node indices 0..K-1 *)
Fixpoint sum_nodes (K : nat) (f : nat -> Q) : Q :=
  match K with
  | O => 0
  | S k => sum_nodes k f + f k
  end.

Open Scope Q_scope.

(* Matrix product entry (truncated to K nodes) *)
Definition mat_mul_at (K : nat) (f g : nat -> nat -> Q) (i k : nat) : Q :=
  sum_nodes K (fun j => f i j * g j k).

(* Commutator entry [M,A]_{ij} of the REAL operators *)
Definition comm_at (K i j : nat) : Q :=
  mat_mul_at K mult_adj add_adj i j - mat_mul_at K add_adj mult_adj i j.

(* Tr([M,A]^2) for the K-node arithmetic graphs — COMPUTED, not tabulated
   (June 2026: was a hardcoded if-K-then-value lookup) *)
Definition tr_comm_sq_arith (K : nat) : Q :=
  sum_nodes K (fun i => sum_nodes K (fun j => comm_at K i j * comm_at K j i)).

(* ===================================================================== *)
(*  General structure: symmetric operators, antisymmetric commutator       *)
(* ===================================================================== *)

Lemma sum_nodes_ext : forall K (f g : nat -> Q),
  (forall i, (i < K)%nat -> f i == g i) ->
  sum_nodes K f == sum_nodes K g.
Proof.
  induction K as [| k IH]; intros f g H; simpl.
  - reflexivity.
  - rewrite (IH f g); [| intros i Hi; apply H; lia].
    rewrite (H k (Nat.lt_succ_diag_r k)). reflexivity.
Qed.

(* Divisibility adjacency is symmetric *)
Lemma mult_adj_symmetric : forall i j, mult_adj i j == mult_adj j i.
Proof.
  intros i j. unfold mult_adj.
  destruct (Nat.eqb (S i) (S j)) eqn:E1; destruct (Nat.eqb (S j) (S i)) eqn:E2.
  - reflexivity.
  - apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2. lia.
  - apply Nat.eqb_neq in E1. apply Nat.eqb_eq in E2. lia.
  - rewrite (orb_comm (divides (S i) (S j)) (divides (S j) (S i))). reflexivity.
Qed.

(* Successor adjacency is symmetric *)
Lemma add_adj_symmetric : forall i j, add_adj i j == add_adj j i.
Proof.
  intros i j. unfold add_adj.
  destruct (Nat.eqb (S i) j) eqn:E1; destruct (Nat.eqb (S j) i) eqn:E2;
  destruct (Nat.eqb i (S j)) eqn:E3; destruct (Nat.eqb j (S i)) eqn:E4;
  try reflexivity;
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  end; lia.
Qed.

(* Product of symmetric operators transposes by swapping order and indices *)
Lemma mat_mul_swap : forall K (f g : nat -> nat -> Q),
  (forall a b, f a b == f b a) ->
  (forall a b, g a b == g b a) ->
  forall i k, mat_mul_at K f g i k == mat_mul_at K g f k i.
Proof.
  intros K f g Hf Hg i k. unfold mat_mul_at.
  apply sum_nodes_ext. intros j Hj.
  rewrite (Hf i j). rewrite (Hg j k). ring.
Qed.

(* ★ The commutator of the two symmetric adjacencies is ANTISYMMETRIC *)
Lemma comm_antisymmetric : forall K i j,
  comm_at K i j == - comm_at K j i.
Proof.
  intros K i j. unfold comm_at.
  rewrite (mat_mul_swap K mult_adj add_adj mult_adj_symmetric add_adj_symmetric i j).
  rewrite (mat_mul_swap K add_adj mult_adj add_adj_symmetric mult_adj_symmetric i j).
  ring.
Qed.

Lemma sum_nodes_nonpos : forall K (f : nat -> Q),
  (forall i, (i < K)%nat -> f i <= 0) ->
  sum_nodes K f <= 0.
Proof.
  induction K as [| k IH]; intros f H; simpl.
  - lra.
  - assert (H1 : sum_nodes k f <= 0) by (apply IH; intros i Hi; apply H; lia).
    assert (H2 : f k <= 0) by (apply H; lia).
    lra.
Qed.

(* ★ GENERAL THEOREM: Tr([M,A]^2) <= 0 for EVERY truncation K.
   Antisymmetry gives C_ij * C_ji = -C_ij^2, so the trace is a sum of
   nonpositive terms.  The concrete values below are sharp instances. *)
Theorem tr_comm_sq_nonpos : forall K, tr_comm_sq_arith K <= 0.
Proof.
  intro K. unfold tr_comm_sq_arith.
  apply sum_nodes_nonpos. intros i Hi.
  apply sum_nodes_nonpos. intros j Hj.
  rewrite (comm_antisymmetric K j i).
  setoid_replace (comm_at K i j * - comm_at K i j)
    with (- (comm_at K i j * comm_at K i j)) by ring.
  assert (Hsq : 0 <= comm_at K i j * comm_at K i j).
  { destruct (Qlt_le_dec (comm_at K i j) 0) as [Hn | Hp].
    - setoid_replace (comm_at K i j * comm_at K i j)
        with ((- comm_at K i j) * (- comm_at K i j)) by ring.
      apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; lra. }
  lra.
Qed.

(* ===================================================================== *)
(*  Concrete commutator values — now DERIVED from the operators            *)
(* ===================================================================== *)

Lemma comm_12 : tr_comm_sq_arith 12 == -(128).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_20 : tr_comm_sq_arith 20 == -(268).
Proof. vm_compute. reflexivity. Qed.

Lemma comm_30 : tr_comm_sq_arith 30 == -(476).
Proof. vm_compute. reflexivity. Qed.

(* === Commutator magnitude grows with K === *)

Lemma comm_grows_20_30 :
  Qabs (tr_comm_sq_arith 30) > Qabs (tr_comm_sq_arith 20).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 30) == 476) by (vm_compute; reflexivity).
  assert (H2: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  rewrite H1, H2. unfold Qlt. simpl. lia.
Qed.

Lemma comm_grows_12_20 :
  Qabs (tr_comm_sq_arith 20) > Qabs (tr_comm_sq_arith 12).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  assert (H2: Qabs (tr_comm_sq_arith 12) == 128) by (vm_compute; reflexivity).
  rewrite H1, H2. unfold Qlt. simpl. lia.
Qed.

(* === Arithmetic commutator exceeds simple average === *)

Lemma arithmetic_larger_20 :
  Qabs (tr_comm_sq_arith 20) > 10 * (19#2).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 20) == 268) by (vm_compute; reflexivity).
  rewrite H1. unfold Qlt. simpl. lia.
Qed.

Lemma arithmetic_larger_12 :
  Qabs (tr_comm_sq_arith 12) > 20 * (11#4).
Proof.
  assert (H1: Qabs (tr_comm_sq_arith 12) == 128) by (vm_compute; reflexivity).
  rewrite H1. unfold Qlt. simpl. lia.
Qed.

(* === Nonzero commutator: multiplicative and additive do not commute === *)

Lemma noncomm_12 : ~ (tr_comm_sq_arith 12 == 0).
Proof.
  intro Heq.
  assert (Hval: tr_comm_sq_arith 12 == -(128)) by (vm_compute; reflexivity).
  rewrite Hval in Heq. unfold Qeq in Heq. simpl in Heq. lia.
Qed.

Lemma noncomm_20 : ~ (tr_comm_sq_arith 20 == 0).
Proof.
  intro Heq.
  assert (Hval: tr_comm_sq_arith 20 == -(268)) by (vm_compute; reflexivity).
  rewrite Hval in Heq. unfold Qeq in Heq. simpl in Heq. lia.
Qed.

Lemma noncomm_30 : ~ (tr_comm_sq_arith 30 == 0).
Proof.
  intro Heq.
  assert (Hval: tr_comm_sq_arith 30 == -(476)) by (vm_compute; reflexivity).
  rewrite Hval in Heq. unfold Qeq in Heq. simpl in Heq. lia.
Qed.

(* === Negativity: instances of tr_comm_sq_nonpos, sharp by computation === *)

Lemma comm_negative_12 : tr_comm_sq_arith 12 < 0.
Proof.
  assert (H: tr_comm_sq_arith 12 == -(128)) by (vm_compute; reflexivity).
  rewrite H. unfold Qlt. simpl. lia.
Qed.

Lemma comm_negative_20 : tr_comm_sq_arith 20 < 0.
Proof.
  assert (H: tr_comm_sq_arith 20 == -(268)) by (vm_compute; reflexivity).
  rewrite H. unfold Qlt. simpl. lia.
Qed.

Lemma comm_negative_30 : tr_comm_sq_arith 30 < 0.
Proof.
  assert (H: tr_comm_sq_arith 30 == -(476)) by (vm_compute; reflexivity).
  rewrite H. unfold Qlt. simpl. lia.
Qed.

(* === Commutator at trivial K: single node, everything commutes === *)

Lemma comm_trivial : tr_comm_sq_arith 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* === Monotone growth pattern === *)

Lemma comm_monotone :
  Qabs (tr_comm_sq_arith 12) < Qabs (tr_comm_sq_arith 20) /\
  Qabs (tr_comm_sq_arith 20) < Qabs (tr_comm_sq_arith 30).
Proof.
  split.
  - exact comm_grows_12_20.
  - exact comm_grows_20_30.
Qed.
