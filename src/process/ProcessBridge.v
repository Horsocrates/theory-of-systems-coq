(** * ProcessBridge.v — Bridging CauchySeq and RealProcess
    Elements: cauchyseq_to_process, process_to_cauchyseq, bridge roundtrips
    Roles:    isomorphism between CauchyReal and ProcessCore representations
    Rules:    preserve Cauchy properties, equivalence, and interval containment
    Status:   complete
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESSBRIDGE — Connecting CauchySeq ↔ RealProcess                *)
(*                                                                            *)
(*  CauchyReal.v defines CauchySeq (Record with proof).                     *)
(*  ProcessCore.v defines RealProcess := nat -> Q with is_Cauchy.            *)
(*  These are the same mathematical object.                                   *)
(*  This file makes the bridge explicit and proves roundtrip properties.      *)
(*                                                                            *)
(*  STATUS: 10 Qed, 0 Admitted                                               *)
(*  AXIOMS: none                                                              *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import CauchyReal.
From ToS Require Import process.ProcessCore.

(* ================================================================== *)
(*  Part I: Definitions                                                *)
(* ================================================================== *)

(** Extract the underlying process from a CauchySeq *)
Definition cauchyseq_to_process (cs : CauchySeq) : RealProcess :=
  fun n => cs_seq cs n.

(** Package a Cauchy RealProcess into a CauchySeq *)
Definition process_to_cauchyseq (R : RealProcess) (H : is_Cauchy R) : CauchySeq :=
  mkCauchy R H.

(* ================================================================== *)
(*  Part II: Cauchy preservation                                       *)
(* ================================================================== *)

(** A CauchySeq is automatically a Cauchy RealProcess *)
Lemma cauchyseq_is_cauchy : forall cs : CauchySeq,
  is_Cauchy (cauchyseq_to_process cs).
Proof.
  intros cs. unfold cauchyseq_to_process, is_Cauchy.
  exact (cs_cauchy cs).
Qed.

(** Constant CauchySeq maps to constant process *)
Lemma const_bridge : forall q,
  process_equiv (cauchyseq_to_process (cauchy_const q)) (const_process q).
Proof.
  intros q. apply process_equiv_refl.
Qed.

(* ================================================================== *)
(*  Part III: Equivalence preservation                                 *)
(* ================================================================== *)

(** CauchyReal equivalence implies ProcessCore equivalence *)
Lemma cauchy_equiv_to_process_equiv : forall cs1 cs2 : CauchySeq,
  cauchy_equiv cs1 cs2 ->
  process_equiv (cauchyseq_to_process cs1) (cauchyseq_to_process cs2).
Proof.
  intros cs1 cs2 Heq eps Heps.
  destruct (Heq eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold cauchyseq_to_process.
  exact (HN n Hn).
Qed.

(** ProcessCore equivalence between embedded CauchySeqs implies CauchyReal equivalence *)
Lemma process_equiv_to_cauchy_equiv : forall cs1 cs2 : CauchySeq,
  process_equiv (cauchyseq_to_process cs1) (cauchyseq_to_process cs2) ->
  cauchy_equiv cs1 cs2.
Proof.
  intros cs1 cs2 Heq eps Heps.
  destruct (Heq eps Heps) as [N HN].
  exists N. intros n Hn.
  unfold cauchyseq_to_process in HN.
  exact (HN n Hn).
Qed.

(* ================================================================== *)
(*  Part IV: Roundtrip properties                                      *)
(* ================================================================== *)

(** Process → CauchySeq → Process is the identity (definitionally) *)
Lemma roundtrip_process : forall R (H : is_Cauchy R),
  forall n, cauchyseq_to_process (process_to_cauchyseq R H) n = R n.
Proof.
  intros R H n. unfold cauchyseq_to_process, process_to_cauchyseq. simpl. reflexivity.
Qed.

(** Process → CauchySeq → Process is equivalent *)
Lemma roundtrip_process_equiv : forall R (H : is_Cauchy R),
  process_equiv (cauchyseq_to_process (process_to_cauchyseq R H)) R.
Proof.
  intros R H eps Heps.
  exists 0%nat. intros n _.
  rewrite roundtrip_process.
  assert (Heq : R n - R n == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(** CauchySeq → Process → CauchySeq preserves the sequence *)
Lemma roundtrip_cauchyseq : forall (cs : CauchySeq),
  forall n, cs_seq (process_to_cauchyseq
    (cauchyseq_to_process cs) (cauchyseq_is_cauchy cs)) n = cs_seq cs n.
Proof.
  intros cs n. unfold process_to_cauchyseq, cauchyseq_to_process. simpl. reflexivity.
Qed.

(** CauchySeq → Process → CauchySeq is equivalent *)
Lemma roundtrip_cauchyseq_equiv : forall (cs : CauchySeq),
  cauchy_equiv cs (process_to_cauchyseq
    (cauchyseq_to_process cs) (cauchyseq_is_cauchy cs)).
Proof.
  intros cs eps Heps.
  exists 0%nat. intros n _.
  rewrite roundtrip_cauchyseq.
  assert (Heq : cs_seq cs n - cs_seq cs n == 0) by ring. rewrite Heq.
  rewrite Qabs_pos; lra.
Qed.

(* ================================================================== *)
(*  Part V: Structural properties                                      *)
(* ================================================================== *)

(** Embedding preserves interval containment *)
Lemma bridge_preserves_interval : forall a b (cs : CauchySeq),
  (forall n, a <= cs_seq cs n /\ cs_seq cs n <= b) ->
  in_interval a b (cauchyseq_to_process cs).
Proof.
  intros a b cs Hint n.
  unfold cauchyseq_to_process.
  exact (Hint n).
Qed.

(** Embedding is injective up to equivalence *)
Lemma bridge_injective : forall cs1 cs2 : CauchySeq,
  (forall n, cs_seq cs1 n == cs_seq cs2 n) ->
  process_equiv (cauchyseq_to_process cs1) (cauchyseq_to_process cs2).
Proof.
  intros cs1 cs2 Heq eps Heps.
  exists 0%nat. intros n _.
  unfold cauchyseq_to_process.
  assert (Hdiff : cs_seq cs1 n - cs_seq cs2 n == 0).
  { specialize (Heq n). lra. }
  rewrite Hdiff. rewrite Qabs_pos; lra.
Qed.
