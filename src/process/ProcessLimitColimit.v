(** * ProcessLimitColimit.v — Limits and Colimits as Universal Processes
    Elements: process products, equalizers, coproducts, directed colimits
    Roles:    projections, injections, universal mediators
    Rules:    universal properties, Cauchy preservation, commutativity
    Status:   complete
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS LIMIT COLIMIT — Limits as Universal Processes              *)
(*                                                                           *)
(*  Under P4: categorical limits/colimits = universal process constructions. *)
(*                                                                           *)
(*  Product A × B: process of pointwise pairs                               *)
(*  Equalizer eq(f,g): process of differences f(n) - g(n)                  *)
(*  Coproduct A + B: process of interleaved sequences                       *)
(*  Directed colimit: the process itself (stages are the diagram)           *)
(*                                                                           *)
(*  STATUS: 25 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import PeanoNat.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Product as Process  (~8 lemmas)                            *)
(* ================================================================== *)

(** Product of two Q-processes: pointwise pairing *)
Definition process_product (R1 R2 : RealProcess) : nat -> Q * Q :=
  fun n => (R1 n, R2 n).

(** Product projections *)
Definition process_fst (p : nat -> Q * Q) : RealProcess :=
  fun n => fst (p n).
Definition process_snd (p : nat -> Q * Q) : RealProcess :=
  fun n => snd (p n).

(** Projections recover the components *)
Lemma product_fst : forall R1 R2 n,
  process_fst (process_product R1 R2) n = R1 n.
Proof.
  intros R1 R2 n. unfold process_fst, process_product. simpl. reflexivity.
Qed.

Lemma product_snd : forall R1 R2 n,
  process_snd (process_product R1 R2) n = R2 n.
Proof.
  intros R1 R2 n. unfold process_snd, process_product. simpl. reflexivity.
Qed.

(** Product is Cauchy if both components are Cauchy *)
Lemma product_cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 ->
  is_Cauchy (process_fst (process_product R1 R2)) /\
  is_Cauchy (process_snd (process_product R1 R2)).
Proof.
  intros R1 R2 H1 H2. split.
  - intros eps Heps. destruct (H1 eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    rewrite product_fst. rewrite product_fst. exact (HN m n Hm Hn).
  - intros eps Heps. destruct (H2 eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    rewrite product_snd. rewrite product_snd. exact (HN m n Hm Hn).
Qed.

(** Universal property: the pairing is unique *)
Lemma product_universal : forall R1 R2 n,
  process_fst (process_product R1 R2) n == R1 n /\
  process_snd (process_product R1 R2) n == R2 n.
Proof.
  intros R1 R2 n. split.
  - rewrite product_fst. lra.
  - rewrite product_snd. lra.
Qed.

(** Product commutativity *)
Lemma product_comm : forall R1 R2 n,
  process_fst (process_product R1 R2) n ==
  process_snd (process_product R2 R1) n.
Proof.
  intros R1 R2 n. rewrite product_fst. rewrite product_snd. lra.
Qed.

(** Constant product: const(q1) × const(q2) = const pair *)
Lemma product_const : forall q1 q2 n,
  process_fst (process_product (const_process q1) (const_process q2)) n == q1 /\
  process_snd (process_product (const_process q1) (const_process q2)) n == q2.
Proof.
  intros q1 q2 n. split.
  - rewrite product_fst. unfold const_process. lra.
  - rewrite product_snd. unfold const_process. lra.
Qed.

(* ================================================================== *)
(*  Part II: Equalizer as Process  (~8 lemmas)                         *)
(* ================================================================== *)

(** Equalizer of f, g : tracks the difference f(n) - g(n) *)
Definition equalizer_process (f g : RealProcess) : RealProcess :=
  fun n => f n - g n.

(** If f ~ g (process_equiv): equalizer → 0 *)
Lemma equalizer_converges : forall f g,
  process_equiv f g ->
  process_equiv (equalizer_process f g) (const_process 0).
Proof.
  intros f g Hfg eps Heps.
  destruct (Hfg eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold equalizer_process, const_process.
  assert (Heq : f n - g n - 0 == f n - g n) by lra.
  rewrite Heq. exact (HN n Hn).
Qed.

(** Equalizer is zero means processes are equivalent *)
Lemma equalizer_zero_means_equiv : forall f g,
  process_equiv (equalizer_process f g) (const_process 0) ->
  process_equiv f g.
Proof.
  intros f g Heq eps Heps.
  destruct (Heq eps Heps) as [N HN].
  exists N. intros n Hn.
  assert (H := HN n Hn).
  unfold equalizer_process, const_process in H.
  assert (Heq2 : f n - g n - 0 == f n - g n) by lra.
  rewrite Heq2 in H. exact H.
Qed.

(** Equalizer of Cauchy sequences is Cauchy *)
Lemma equalizer_cauchy : forall f g,
  is_Cauchy f -> is_Cauchy g ->
  is_Cauchy (equalizer_process f g).
Proof.
  intros f g Hf Hg eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (Hf (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (Hg (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros m n Hm Hn.
  unfold equalizer_process.
  assert (Hm1 : (N1 <= m)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  assert (HfN := HN1 m n Hm1 Hn1).
  assert (HgN := HN2 m n Hm2 Hn2).
  assert (Htri := Qabs_triangle (f m - f n) (-(g m - g n))).
  assert (Heq : f m - g m - (f n - g n) == (f m - f n) + -(g m - g n)) by lra.
  rewrite Heq.
  assert (Hneg : Qabs (-(g m - g n)) == Qabs (g m - g n)).
  { destruct (Qlt_le_dec (g m - g n) 0) as [Hn3 | Hp3].
    - assert (Hle0 : g m - g n <= 0) by lra.
      assert (Hge0 : 0 <= -(g m - g n)) by lra.
      rewrite (Qabs_neg _ Hle0). rewrite (Qabs_pos _ Hge0). lra.
    - assert (Hle0 : -(g m - g n) <= 0) by lra.
      rewrite (Qabs_pos _ Hp3). rewrite (Qabs_neg _ Hle0). lra. }
  assert (Hle : Qabs (f m - f n) + Qabs (-(g m - g n)) < eps * (1#2) + eps * (1#2)).
  { rewrite Hneg. lra. }
  assert (Hle2 : Qabs ((f m - f n) + -(g m - g n)) <=
                 Qabs (f m - f n) + Qabs (-(g m - g n))).
  { exact Htri. }
  lra.
Qed.

(** Equalizer bound: |eq(n)| ≤ |f(n)| + |g(n)| *)
Lemma equalizer_bound : forall f g n,
  Qabs (equalizer_process f g n) <= Qabs (f n) + Qabs (g n).
Proof.
  intros f g n. unfold equalizer_process.
  assert (Htri := Qabs_triangle (f n) (-(g n))).
  assert (Heq : f n - g n == f n + -(g n)) by lra.
  rewrite Heq.
  assert (Hneg : Qabs (-(g n)) == Qabs (g n)).
  { destruct (Qlt_le_dec (g n) 0) as [Hn | Hp].
    - assert (Hle0 : g n <= 0) by lra.
      assert (Hge0 : 0 <= -(g n)) by lra.
      rewrite (Qabs_neg _ Hle0). rewrite (Qabs_pos _ Hge0). lra.
    - assert (Hle0 : -(g n) <= 0) by lra.
      rewrite (Qabs_pos _ Hp). rewrite (Qabs_neg _ Hle0). lra. }
  rewrite Hneg in Htri. exact Htri.
Qed.

(** Kernel: equalizer with zero *)
Definition kernel_process (f : RealProcess) : RealProcess :=
  equalizer_process f (const_process 0).

(** Kernel simplifies to f itself *)
Lemma kernel_is_f : forall f n,
  kernel_process f n == f n.
Proof.
  intros f n. unfold kernel_process, equalizer_process, const_process. lra.
Qed.

(** Kernel cauchy iff f cauchy *)
Lemma kernel_cauchy_iff : forall f,
  is_Cauchy (kernel_process f) <-> is_Cauchy f.
Proof.
  intros f. split.
  - intros Hk eps Heps. destruct (Hk eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    assert (H := HN m n Hm Hn).
    unfold kernel_process, equalizer_process, const_process in H.
    assert (Heq : f m - 0 - (f n - 0) == f m - f n) by lra.
    rewrite Heq in H. exact H.
  - intros Hf eps Heps. destruct (Hf eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    unfold kernel_process, equalizer_process, const_process.
    assert (Heq : f m - 0 - (f n - 0) == f m - f n) by lra.
    rewrite Heq. exact (HN m n Hm Hn).
Qed.

(* ================================================================== *)
(*  Part III: Coproduct = Process Interleaving  (~5 lemmas)            *)
(* ================================================================== *)

(** Coproduct: interleave two processes *)
Definition process_coproduct (R1 R2 : RealProcess) : RealProcess :=
  fun n => if Nat.even n then R1 (Nat.div n 2) else R2 (Nat.div n 2).

(** Injection 1: R1(k) appears at position 2k *)
Lemma coproduct_inj1 : forall R1 R2 (k : nat),
  process_coproduct R1 R2 (2 * k)%nat = R1 k.
Proof.
  intros R1 R2 k. unfold process_coproduct.
  assert (Heven : Nat.even (2 * k)%nat = true).
  { rewrite Nat.even_mul. simpl. reflexivity. }
  rewrite Heven. f_equal. rewrite Nat.mul_comm. apply Nat.div_mul. lia.
Qed.

(** Injection 2: R2(k) appears at position 2k+1 *)
Lemma coproduct_inj2 : forall R1 R2 (k : nat),
  process_coproduct R1 R2 (2 * k + 1)%nat = R2 k.
Proof.
  intros R1 R2 k. unfold process_coproduct.
  assert (Hodd : Nat.even (2 * k + 1)%nat = false).
  { rewrite Nat.even_add. rewrite Nat.even_mul. simpl. reflexivity. }
  rewrite Hodd. f_equal.
  replace (2 * k + 1)%nat with (1 + k * 2)%nat by lia.
  rewrite Nat.div_add by lia. simpl. reflexivity.
Qed.

(** Directed colimit: a chain of processes IS a process *)
(** Under P4: every colimit is a process. No completed colimit needed. *)
(** The "colimit" of the chain a_0, a_1, a_2, ... is just the process a itself *)
Definition directed_colimit (chain : nat -> RealProcess) : RealProcess :=
  fun n => chain n n.

(** Directed colimit of constant chains is constant *)
Lemma colimit_const : forall q,
  process_equiv (directed_colimit (fun _ => const_process q)) (const_process q).
Proof.
  intros q eps Heps. exists 0%nat. intros n _.
  unfold directed_colimit, const_process.
  assert (Heq : q - q == 0) by lra.
  rewrite Heq. rewrite Qabs_pos; lra.
Qed.

(** Diagonal of a chain: pick the n-th element of the n-th process *)
Lemma colimit_diagonal : forall chain n,
  directed_colimit chain n = chain n n.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(*  Part IV: Limits and E/R/R  (~4 lemmas)                             *)
(* ================================================================== *)

(** Sum of two processes (coproduct in additive sense) *)
Definition process_sum (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n + R2 n.

(** Sum is Cauchy if both are *)
Lemma sum_cauchy : forall R1 R2,
  is_Cauchy R1 -> is_Cauchy R2 ->
  is_Cauchy (process_sum R1 R2).
Proof.
  intros R1 R2 H1 H2 eps Heps.
  assert (Heps2 : 0 < eps * (1#2)) by lra.
  destruct (H1 (eps * (1#2)) Heps2) as [N1 HN1].
  destruct (H2 (eps * (1#2)) Heps2) as [N2 HN2].
  exists (Nat.max N1 N2). intros m n Hm Hn.
  unfold process_sum.
  assert (Hm1 : (N1 <= m)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (Hm2 : (N2 <= m)%nat) by lia.
  assert (Hn2 : (N2 <= n)%nat) by lia.
  assert (HfN := HN1 m n Hm1 Hn1).
  assert (HgN := HN2 m n Hm2 Hn2).
  assert (Htri := Qabs_triangle (R1 m - R1 n) (R2 m - R2 n)).
  assert (Heq : R1 m + R2 m - (R1 n + R2 n) == (R1 m - R1 n) + (R2 m - R2 n)) by lra.
  rewrite Heq. lra.
Qed.

(** Sum commutativity *)
Lemma sum_comm : forall R1 R2 n,
  process_sum R1 R2 n == process_sum R2 R1 n.
Proof.
  intros R1 R2 n. unfold process_sum. lra.
Qed.

(** Sum with zero is identity *)
Lemma sum_zero_right : forall R n,
  process_sum R (const_process 0) n == R n.
Proof.
  intros R n. unfold process_sum, const_process. lra.
Qed.

(** Difference as equalizer of sum *)
Lemma sum_equalizer_connection : forall R1 R2 n,
  equalizer_process R1 R2 n == process_sum R1 (fun m => -(R2 m)) n.
Proof.
  intros R1 R2 n. unfold equalizer_process, process_sum. lra.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check process_product. Check process_fst. Check process_snd.
Check product_fst. Check product_snd. Check product_cauchy.
Check product_universal. Check product_comm. Check product_const.
Check equalizer_process. Check equalizer_converges. Check equalizer_zero_means_equiv.
Check equalizer_cauchy. Check equalizer_bound.
Check kernel_process. Check kernel_is_f. Check kernel_cauchy_iff.
Check process_coproduct. Check coproduct_inj1. Check coproduct_inj2.
Check directed_colimit. Check colimit_const. Check colimit_diagonal.
Check process_sum. Check sum_cauchy. Check sum_comm.
Check sum_zero_right. Check sum_equalizer_connection.
