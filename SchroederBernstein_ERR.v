(* ========================================================================= *)
(*                                                                           *)
(*                    SCHROEDER-BERNSTEIN THEOREM                            *)
(*              Formalization Without the Axiom of Infinity                  *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*                                                                           *)
(*  Author:  Horsocrates                                                     *)
(*  Version: 2.0 (E/R/R)                                                     *)
(*  Date:    January 2026                                                    *)
(*                                                                           *)
(*  STATUS: 14 Qed, 0 Admitted (100% COMPLETE)                               *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*                                                                           *)
(*  This file demonstrates P4 (Finitude) applied to cardinality:             *)
(*                                                                           *)
(*    Elements = Points in A, B (type-level)                                 *)
(*    Roles    = Injections f : A -> B, g : B -> A                           *)
(*    Rules    = chain_depth (finite depth replaces infinite chains)         *)
(*                                                                           *)
(*  KEY INNOVATION (P4-compliant):                                           *)
(*    Instead of infinite chains, we define CHAIN DEPTH as nat.              *)
(*    Each point has finite depth or belongs to doubly-infinite chain.       *)
(*    This replaces infinite objects with FINITE PROCESSES.                  *)
(*                                                                           *)
(*  THEOREM: If exist injections f : A -> B and g : B -> A,                  *)
(*           then exists bijection h : A -> B.                               *)
(*                                                                           *)
(*  AXIOMS: classic (L3) + epsilon. NO Axiom of Infinity.                    *)
(*                                                                           *)
(* ========================================================================= *)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.

Set Implicit Arguments.

Section SchroederBernstein.

Variables A B : Type.
Variable inhA : inhabited A.
Variable inhB : inhabited B.

Variable f : A -> B.
Variable g : B -> A.

Hypothesis f_inj : forall a1 a2, f a1 = f a2 -> a1 = a2.
Hypothesis g_inj : forall b1 b2, g b1 = g b2 -> b1 = b2.

(* ======================== *)
(* PARTIAL INVERSES         *)
(* ======================== *)

Definition f_inv (b : B) : A := epsilon inhA (fun a => f a = b).
Definition g_inv (a : A) : B := epsilon inhB (fun b => g b = a).

Lemma f_inv_spec : forall b, (exists a, f a = b) -> f (f_inv b) = b.
Proof.
  intros b [a Ha]. unfold f_inv. apply epsilon_spec. exists a. exact Ha.
Qed.

Lemma g_inv_spec : forall a, (exists b, g b = a) -> g (g_inv a) = a.
Proof.
  intros a [b Hb]. unfold g_inv. apply epsilon_spec. exists b. exact Hb.
Qed.

(* ======================== *)
(* CHAIN DEPTH              *)
(* ======================== *)

(*
   Key insight: Instead of mutual induction, we define CHAIN DEPTH.
   
   An element a in A is B_rooted at depth n if:
   - n = 0: a = g(b) for some b with no f-preimage
   - n = S m: a = g(b), b = f(a'), and a' is B_rooted at depth m
   
   This gives us a well-founded measure for induction.
*)

Definition no_f_preimage (b : B) : Prop := ~ exists a, f a = b.
Definition no_g_preimage (a : A) : Prop := ~ exists b, g b = a.

(* B_rooted at specific depth *)
Inductive B_rooted_depth : nat -> A -> Prop :=
  | B_rooted_depth_0 : forall a b, 
      g b = a -> no_f_preimage b -> B_rooted_depth 0 a
  | B_rooted_depth_S : forall n a b a', 
      g b = a -> f a' = b -> B_rooted_depth n a' -> B_rooted_depth (S n) a.

(* B_rooted_in_B at specific depth *)
Inductive B_rooted_in_B_depth : nat -> B -> Prop :=
  | B_rooted_B_depth_0 : forall b, 
      no_f_preimage b -> B_rooted_in_B_depth 0 b
  | B_rooted_B_depth_S : forall n b a b', 
      f a = b -> g b' = a -> B_rooted_in_B_depth n b' -> B_rooted_in_B_depth (S n) b.

(* Original definitions as "exists some depth" *)
Definition B_rooted (a : A) : Prop := exists n, B_rooted_depth n a.
Definition B_rooted_in_B (b : B) : Prop := exists n, B_rooted_in_B_depth n b.

(* ======================== *)
(* KEY LEMMAS WITH DEPTH    *)
(* ======================== *)

(* Lemma: B_rooted elements have g-preimage *)
Lemma B_rooted_depth_has_g_preimage : forall n a, 
  B_rooted_depth n a -> exists b, g b = a.
Proof.
  intros n a HB. destruct HB as [a0 b Hgb _ | m a0 b a' Hgb _ _].
  - exists b. exact Hgb.
  - exists b. exact Hgb.
Qed.

Lemma B_rooted_has_g_preimage : forall a, B_rooted a -> exists b, g b = a.
Proof.
  intros a [n HB]. apply B_rooted_depth_has_g_preimage with n. exact HB.
Qed.

(* CORE LEMMA: depth correspondence between A and B versions *)
(* We prove this by induction on the B_rooted_depth derivation *)

Lemma depth_A_to_B_aux : forall n a,
  B_rooted_depth n a -> forall b, g b = a -> B_rooted_in_B_depth n b.
Proof.
  intros n a HBa.
  induction HBa as [a b0 Hgb0 Hnf | n' a b0 a' Hgb0 Hfa' HBa' IHa'].
  - (* B_rooted_depth_0 *)
    intros b Hgb.
    assert (b = b0) as Heq. { apply g_inj. rewrite Hgb. symmetry. exact Hgb0. }
    rewrite Heq in *.
    clear Heq.
    constructor. exact Hnf.
  - (* B_rooted_depth_S *)
    intros b Hgb.
    assert (b = b0) as Heq. { apply g_inj. rewrite Hgb. symmetry. exact Hgb0. }
    (* Don't subst - use rewrite to preserve hypothesis names *)
    rewrite Heq in *.
    clear Heq.
    (* Now: Hfa' : f a' = b0, HBa' : B_rooted_depth n' a' *)
    (* Need to find b' such that g b' = a' and apply IH *)
    destruct (B_rooted_depth_has_g_preimage HBa') as [b' Hgb'].
    apply B_rooted_B_depth_S with a' b'.
    + exact Hfa'.
    + exact Hgb'.
    + apply IHa'. exact Hgb'.
Qed.

Lemma depth_A_to_B : forall n a b,
  g b = a -> B_rooted_depth n a -> B_rooted_in_B_depth n b.
Proof.
  intros n a b Hgb HBa.
  apply depth_A_to_B_aux with a; assumption.
Qed.

Lemma depth_B_to_A : forall n b,
  B_rooted_in_B_depth n b -> B_rooted_depth n (g b).
Proof.
  intros n b HBb.
  induction HBb as [b0 Hnf | n' b0 a b' Hfa Hgb' HBb' IHb'].
  - (* B_rooted_B_depth_0 *)
    apply B_rooted_depth_0 with b0.
    + reflexivity.
    + exact Hnf.
  - (* B_rooted_B_depth_S *)
    (* b0 = f a, g b' = a, B_rooted_in_B_depth n' b' *)
    (* Need: B_rooted_depth (S n') (g b0) = B_rooted_depth (S n') (g (f a)) *)
    apply B_rooted_depth_S with b0 a.
    + reflexivity.
    + exact Hfa.
    + (* Need B_rooted_depth n' a *)
      (* We have g b' = a and IH: B_rooted_depth n' (g b') *)
      rewrite <- Hgb'.
      exact IHb'.
Qed.

(* Main correspondence lemmas *)
Lemma g_preserves_B_rooted : forall b, B_rooted (g b) -> B_rooted_in_B b.
Proof.
  intros b [n HBgb].
  exists n.
  apply depth_A_to_B with (g b).
  - reflexivity.
  - exact HBgb.
Qed.

Lemma B_rooted_in_B_implies_B_rooted_g : forall b, B_rooted_in_B b -> B_rooted (g b).
Proof.
  intros b [n HBb].
  exists n.
  apply depth_B_to_A. exact HBb.
Qed.

(* Chain separation *)
Lemma chain_separation : forall a b,
  B_rooted a -> f a = b -> B_rooted_in_B b.
Proof.
  intros a b [n HBa] Hfab.
  (* a is B_rooted_depth n, so a = g(b') for some b' *)
  destruct (B_rooted_depth_has_g_preimage HBa) as [b' Hgb'].
  (* f(a) = f(g(b')) = b *)
  (* We need B_rooted_in_B b *)
  (* b = f(g(b')) = f a *)
  (* g b' = a, so b' is B_rooted_in_B_depth n *)
  exists (S n).
  apply B_rooted_B_depth_S with a b'.
  - exact Hfab.
  - exact Hgb'.
  - apply depth_A_to_B with a.
    + exact Hgb'.
    + exact HBa.
Qed.

(* Reverse: f-preimage of B_rooted_in_B is B_rooted *)
Lemma f_preimage_B_rooted : forall a b,
  f a = b -> B_rooted_in_B b -> B_rooted a.
Proof.
  intros a b Hfab [n HBb].
  (* b is B_rooted_in_B_depth n *)
  revert a Hfab.
  induction HBb as [b0 Hnf | n' b0 a0 b' Hfa0 Hgb' HBb' IH].
  - (* B_rooted_B_depth_0: b0 has no f-preimage *)
    intros a Hfab.
    exfalso. apply Hnf. exists a. exact Hfab.
  - (* B_rooted_B_depth_S: b0 = f a0, g b' = a0, B_rooted_in_B_depth n' b' *)
    intros a Hfab.
    (* f a = b0 = f a0, so a = a0 *)
    assert (Heq : a = a0) by (apply f_inj; rewrite Hfab; symmetry; exact Hfa0).
    rewrite Heq.
    (* Now: g b' = a0, and B_rooted_in_B_depth n' b' *)
    (* Need: B_rooted a0, i.e., exists m, B_rooted_depth m a0 *)
    exists n'.
    rewrite <- Hgb'.
    apply depth_B_to_A. exact HBb'.
Qed.

(* ======================== *)
(* THE BIJECTION            *)
(* ======================== *)

Definition h (a : A) : B :=
  if excluded_middle_informative (B_rooted a)
  then if excluded_middle_informative (exists b, g b = a)
       then g_inv a
       else f a
  else f a.

(* ======================== *)
(* INJECTIVITY              *)
(* ======================== *)

Theorem h_injective : forall a1 a2, h a1 = h a2 -> a1 = a2.
Proof.
  intros a1 a2 Heq.
  unfold h in Heq.
  destruct (excluded_middle_informative (B_rooted a1)) as [HB1 | HnB1];
  destruct (excluded_middle_informative (B_rooted a2)) as [HB2 | HnB2].
  
  - (* Both B_rooted *)
    destruct (excluded_middle_informative (exists b, g b = a1)) as [Hex1 | Hnex1];
    destruct (excluded_middle_informative (exists b, g b = a2)) as [Hex2 | Hnex2].
    + (* Both: g_inv a1 = g_inv a2, so a1 = a2 *)
      assert (g (g_inv a1) = a1) by (apply g_inv_spec; exact Hex1).
      assert (g (g_inv a2) = a2) by (apply g_inv_spec; exact Hex2).
      congruence.
    + exfalso. apply Hnex2. apply B_rooted_has_g_preimage. exact HB2.
    + exfalso. apply Hnex1. apply B_rooted_has_g_preimage. exact HB1.
    + apply f_inj. exact Heq.
      
  - (* a1 B_rooted, a2 not *)
    destruct (excluded_middle_informative (exists b, g b = a1)) as [Hex1 | Hnex1].
    + (* g_inv a1 = f a2 *)
      exfalso.
      (* g_inv a1 is in B-rooted chain *)
      assert (HBgv : B_rooted_in_B (g_inv a1)).
      { apply g_preserves_B_rooted.
        assert (Hgg : g (g_inv a1) = a1) by (apply g_inv_spec; exact Hex1).
        rewrite Hgg. exact HB1. }
      (* f a2 = g_inv a1 is B_rooted_in_B *)
      (* So a2 should be B_rooted *)
      apply HnB2.
      apply f_preimage_B_rooted with (g_inv a1).
      * symmetry. exact Heq.
      * exact HBgv.
    + apply f_inj. exact Heq.
    
  - (* a2 B_rooted, a1 not - symmetric *)
    destruct (excluded_middle_informative (exists b, g b = a2)) as [Hex2 | Hnex2].
    + exfalso.
      assert (HBgv : B_rooted_in_B (g_inv a2)).
      { apply g_preserves_B_rooted.
        assert (Hgg : g (g_inv a2) = a2) by (apply g_inv_spec; exact Hex2).
        rewrite Hgg. exact HB2. }
      apply HnB1.
      apply f_preimage_B_rooted with (g_inv a2).
      * exact Heq.
      * exact HBgv.
    + apply f_inj. exact Heq.
    
  - (* Neither B_rooted *)
    apply f_inj. exact Heq.
Qed.

(* ======================== *)
(* SURJECTIVITY             *)
(* ======================== *)

Theorem h_surjective : forall b, exists a, h a = b.
Proof.
  intro b.
  destruct (excluded_middle_informative (B_rooted_in_B b)) as [HBb | HnBb].
  
  - (* b is B_rooted_in_B: use g b *)
    exists (g b).
    unfold h.
    destruct (excluded_middle_informative (B_rooted (g b))) as [HBgb | HnBgb].
    + destruct (excluded_middle_informative (exists b0, g b0 = g b)) as [Hex | Hnex].
      * assert (g (g_inv (g b)) = g b) by (apply g_inv_spec; exact Hex).
        apply g_inj. exact H.
      * exfalso. apply Hnex. exists b. reflexivity.
    + exfalso. apply HnBgb.
      apply B_rooted_in_B_implies_B_rooted_g. exact HBb.
        
  - (* b is not B_rooted_in_B: use f-preimage *)
    destruct (excluded_middle_informative (exists a, f a = b)) as [Hex | Hnex].
    + destruct Hex as [a Ha].
      exists a.
      unfold h.
      destruct (excluded_middle_informative (B_rooted a)) as [HBa | HnBa].
      * (* a B_rooted implies f a = b is B_rooted_in_B: contradiction *)
        exfalso. apply HnBb. apply chain_separation with a; assumption.
      * destruct (excluded_middle_informative (exists b0, g b0 = a)); exact Ha.
    + (* b has no f-preimage: b is B_rooted_in_B base case *)
      exfalso. apply HnBb. 
      exists 0. apply B_rooted_B_depth_0. exact Hnex.
Qed.

(* ======================== *)
(* MAIN THEOREM             *)
(* ======================== *)

Theorem Schroeder_Bernstein : exists h : A -> B,
  (forall a1 a2, h a1 = h a2 -> a1 = a2) /\
  (forall b, exists a, h a = b).
Proof.
  exists h. split.
  - exact h_injective.
  - exact h_surjective.
Qed.

End SchroederBernstein.

(* ======================== *)
(* VERIFICATION             *)
(* ======================== *)

Check Schroeder_Bernstein.
Print Assumptions Schroeder_Bernstein.

(* 
   COMPLETE PROOF - NO ADMITTED LEMMAS
   
   The key insight that made this work:
   
   1. Define B_rooted_depth and B_rooted_in_B_depth with EXPLICIT DEPTH
      This provides a natural number for induction.
   
   2. The original B_rooted is "exists n, B_rooted_depth n"
      This preserves the original semantics.
   
   3. The correspondence lemmas (depth_A_to_B, depth_B_to_A) 
      use simple induction on depth.
   
   4. Chain separation and f_preimage_B_rooted follow from correspondence.
   
   PHILOSOPHICAL POINTS:
   
   - "Chain depth" is always FINITE (it's a nat)
   - "Doubly infinite chain" = "no finite depth exists"
   - We use classical logic to decide B_rooted, but the STRUCTURE is finite
   - This demonstrates P4 (Finite Actuality): at any point, we work with finite depth
   
   AXIOMS USED:
   
   - classic (excluded middle) - this is L3 in Theory of Systems
   - epsilon (Hilbert's choice) - for partial inverses
   
   NO actual infinity is used. Chains are characterized by FINITE depth.
*)
