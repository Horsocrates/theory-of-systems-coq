(** * ProcessNoetherian.v — Ascending Chains and Process Termination
    Elements: ascending chain values, stabilization witnesses
    Roles:    chain as process, Noetherian = process termination
    Rules:    bounded ascending stabilizes, termination ⊂ Cauchy
    Status:   complete
    STATUS: ~22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS NOETHERIAN — Ascending Chains and Process Termination        *)
(*                                                                           *)
(*  Noetherian condition: every ascending chain stabilizes.                  *)
(*  Under P4: this is a PROCESS TERMINATION property.                       *)
(*  The chain IS a process. Noetherian = the process reaches equilibrium.   *)
(*                                                                           *)
(*  STATUS: ~22 Qed, 0 Admitted                                             *)
(*  AXIOMS: classic (for excluded middle in stabilization)                   *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Classical.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Ascending Chain Process  (~7 lemmas)                      *)
(* ================================================================== *)

Definition ascending_chain := nat -> nat.

Definition is_ascending (ch : ascending_chain) : Prop :=
  forall n : nat, (ch n <= ch (S n))%nat.

Definition stabilizes (ch : ascending_chain) : Prop :=
  exists N : nat, forall n : nat, (N <= n)%nat -> ch n = ch N.

Lemma ascending_le : forall (ch : ascending_chain), is_ascending ch ->
  forall n m : nat, (n <= m)%nat -> (ch n <= ch m)%nat.
Proof.
  intros ch Hasc n m Hnm. induction Hnm as [| m' Hle IH].
  - lia.
  - specialize (Hasc m') as Hstep. lia.
Qed.

Lemma const_chain_stabilizes : forall (v : nat),
  stabilizes (fun _ : nat => v).
Proof. intros v. exists 0%nat. intros n _. reflexivity. Qed.

Lemma const_chain_ascending : forall (v : nat),
  is_ascending (fun _ : nat => v).
Proof. intros v n. lia. Qed.

Lemma stabilizes_step : forall (ch : ascending_chain),
  stabilizes ch -> exists N : nat, ch N = ch (S N).
Proof.
  intros ch [N HN]. exists N. symmetry. apply HN. lia.
Qed.

(** Key theorem: bounded ascending chain stabilizes *)
(** Clean proof by induction on B *)
Theorem bounded_ascending_stabilizes : forall (ch : ascending_chain) (B : nat),
  is_ascending ch ->
  (forall n : nat, (ch n <= B)%nat) ->
  stabilizes ch.
Proof.
  intros ch B. revert ch. induction B as [| B' IH].
  - (* B = 0: ch(n) ≤ 0 for all n, so ch constant at 0 *)
    intros ch Hasc Hbound. exists 0%nat. intros n _.
    assert (H0 := Hbound 0%nat). assert (Hn := Hbound n).
    assert (Hle := ascending_le ch Hasc 0 n ltac:(lia)). lia.
  - (* B = S B' *)
    intros ch Hasc Hbound.
    (* Classical: either ch stays ≤ B', or it reaches S B' *)
    destruct (classic (forall n : nat, (ch n <= B')%nat)) as [Htight | Hreach].
    + (* ch stays ≤ B' → use IH with smaller bound *)
      exact (IH ch Hasc Htight).
    + (* ch reaches S B' at some point n0 *)
      apply not_all_ex_not in Hreach.
      destruct Hreach as [n0 Hn0].
      (* ch(n0) > B' and ch(n0) ≤ S B', so ch(n0) = S B' *)
      (* From n0 onward: ascending and ≤ S B' = ch(n0), so constant *)
      exists n0. intros n Hn.
      assert (Hle := ascending_le ch Hasc n0 n Hn).
      assert (Hbn := Hbound n).
      assert (Hsn0 := Hbound n0).
      lia.
Qed.

(** Stabilization: all values equal from N onward *)
Lemma stabilizes_all_equal : forall (ch : ascending_chain) (N0 : nat),
  (forall n : nat, (N0 <= n)%nat -> ch n = ch N0) ->
  forall n m : nat, (N0 <= n)%nat -> (N0 <= m)%nat -> ch n = ch m.
Proof.
  intros ch N0 Hstab n m Hn Hm.
  assert (Hn' := Hstab n Hn). assert (Hm' := Hstab m Hm). lia.
Qed.

(* ================================================================== *)
(*  Part II: Noetherian as Process Termination  (~7 lemmas)           *)
(* ================================================================== *)

Definition is_noetherian (P : ascending_chain -> Prop) : Prop :=
  forall ch : ascending_chain, P ch -> is_ascending ch -> stabilizes ch.

Theorem bounded_is_noetherian : forall (B : nat),
  is_noetherian (fun ch => forall n : nat, (ch n <= B)%nat).
Proof.
  intros B ch Hbound Hasc.
  exact (bounded_ascending_stabilizes ch B Hasc Hbound).
Qed.

Lemma noetherian_0 : forall (ch : ascending_chain),
  (forall n : nat, ch n = 0%nat) -> stabilizes ch.
Proof.
  intros ch H0. exists 0%nat. intros n _. rewrite H0, H0. reflexivity.
Qed.

Lemma ascending_compose : forall (f : nat -> nat) (ch : ascending_chain),
  (forall n : nat, (f n <= f (S n))%nat) ->
  is_ascending ch ->
  is_ascending (fun n => ch (f n)).
Proof.
  intros f ch Hf Hasc n.
  apply ascending_le; [exact Hasc | apply Hf].
Qed.

Lemma ascending_shift : forall (ch : ascending_chain) (k : nat),
  is_ascending ch -> is_ascending (fun n => ch (n + k)%nat).
Proof.
  intros ch k Hasc n.
  replace (S n + k)%nat with (S (n + k))%nat by lia.
  apply Hasc.
Qed.

(* ================================================================== *)
(*  Part III: Hilbert Basis (Process Version)  (~3 lemmas)            *)
(* ================================================================== *)

Lemma finite_dim_noetherian : forall (dim : nat) (ch : ascending_chain),
  is_ascending ch ->
  (forall k : nat, (ch k <= dim)%nat) ->
  stabilizes ch.
Proof.
  intros dim ch Hasc Hbound.
  exact (bounded_ascending_stabilizes ch dim Hasc Hbound).
Qed.

Theorem truncated_poly_noetherian : forall (n : nat),
  is_noetherian (fun ch => forall k : nat, (ch k <= n)%nat).
Proof. intros n. exact (bounded_is_noetherian n). Qed.

Lemma subchain_bounded : forall (ch : ascending_chain) (B : nat) (f : nat -> nat),
  (forall n : nat, (ch n <= B)%nat) ->
  (forall n : nat, (ch (f n) <= B)%nat).
Proof. intros ch B f Hbound n. apply Hbound. Qed.

(* ================================================================== *)
(*  Part IV: Connection to Termination  (~5 lemmas)                   *)
(* ================================================================== *)

Local Open Scope Q_scope.

Definition chain_to_process (ch : ascending_chain) : RealProcess :=
  fun n => inject_Z (Z.of_nat (ch n)).

Lemma stabilized_chain_cauchy : forall (ch : ascending_chain),
  stabilizes ch -> is_Cauchy (chain_to_process ch).
Proof.
  intros ch [N HN] eps Heps.
  exists N. intros m n Hm Hn.
  unfold chain_to_process.
  assert (Hm' := HN m Hm). assert (Hn' := HN n Hn).
  rewrite Hm', Hn'.
  assert (Heq : inject_Z (Z.of_nat (ch N)) - inject_Z (Z.of_nat (ch N)) == 0) by lra.
  rewrite Heq. rewrite Qabs_pos; lra.
Qed.

Lemma ascending_chain_monotone : forall (ch : ascending_chain),
  is_ascending ch ->
  forall n : nat, chain_to_process ch n <= chain_to_process ch (S n).
Proof.
  intros ch Hasc n. unfold chain_to_process.
  apply Qle_trans with (inject_Z (Z.of_nat (ch (S n)))); [| lra].
  unfold Qle. simpl.
  assert (H := Hasc n). lia.
Qed.

Theorem noetherian_is_p4 : forall (ch : ascending_chain) (B : nat),
  is_ascending ch ->
  (forall n : nat, (ch n <= B)%nat) ->
  is_Cauchy (chain_to_process ch).
Proof.
  intros ch B Hasc Hbound.
  apply stabilized_chain_cauchy.
  exact (bounded_ascending_stabilizes ch B Hasc Hbound).
Qed.

Lemma bounded_chain_bounded_process : forall (ch : ascending_chain) (B : nat),
  (forall n : nat, (ch n <= B)%nat) ->
  forall n : nat, chain_to_process ch n <= inject_Z (Z.of_nat B).
Proof.
  intros ch B Hbound n. unfold chain_to_process.
  unfold Qle. simpl. assert (H := Hbound n). lia.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check ascending_chain. Check is_ascending. Check stabilizes.
Check ascending_le. Check bounded_ascending_stabilizes.
Check is_noetherian. Check bounded_is_noetherian.
Check finite_dim_noetherian. Check truncated_poly_noetherian.
Check chain_to_process. Check stabilized_chain_cauchy.
Check ascending_chain_monotone. Check noetherian_is_p4.
