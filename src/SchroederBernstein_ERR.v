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
(*  STATUS: 22 Qed, 0 Admitted (100% COMPLETE)                               *)
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
(*  WITNESS ROLES (Nov 2026):                                                *)
(*    Elements = witnesses of existence statements                           *)
(*    Roles    = the UNIQUE witness (fixed by the statement itself: the      *)
(*               preimage under an injection, the truth-bit of a             *)
(*               proposition) vs. ONE witness AMONG MANY                     *)
(*    Rules    = DD extracts only the first; the proof never needs the       *)
(*               second.  P4 diagnostic ("could it be otherwise?"): for a    *)
(*               unique witness -- no, extraction adds nothing.              *)
(*                                                                           *)
(*  PREMISES: the proof takes two principles as premises, not as axioms --   *)
(*    EM : excluded middle;                                                  *)
(*    DD : extraction of the UNIQUE witness (definite description).          *)
(*  Schroeder_Bernstein_definite is closed under the global context.         *)
(*  Schroeder_Bernstein is its instance at classic and L4_definite; the      *)
(*  compiler reports classic + L4_witness for it.  The full strength of      *)
(*  L4_witness (an ARBITRARY witness, from which choice over families        *)
(*  follows) is not used anywhere in the proof.  No Axiom of Infinity.       *)
(*                                                                           *)
(* ========================================================================= *)

From ToS Require Import ToS_Axioms.
From Stdlib Require Import Classical_Pred_Type.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Wf_nat.

Set Implicit Arguments.

Section SchroederBernstein.

(* ======================== *)
(* THE TWO PREMISES         *)
(* ======================== *)

(* Excluded middle and extraction of the UNIQUE witness, as premises. *)
Variable EM : forall P : Prop, P \/ ~ P.
Variable DD : forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}.

(* Informative excluded middle: the truth-bit of P is a unique witness,
   so DD suffices (no extraction of an arbitrary witness). *)
Lemma em_inf : forall P : Prop, {P} + {~ P}.
Proof.
  intro P.
  assert (Hex : exists! b : bool, if b then P else ~ P).
  { destruct (EM P) as [HP | HnP].
    - exists true. split; [exact HP |].
      intros [|] Hb; [reflexivity | exfalso; exact (Hb HP)].
    - exists false. split; [exact HnP |].
      intros [|] Hb; [exfalso; exact (HnP Hb) | reflexivity]. }
  destruct (@DD bool _ Hex) as [b Hb].
  destruct b; [left | right]; exact Hb.
Defined.

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

(* Injectivity gives uniqueness of preimages, enabling DD *)

Lemma f_preimage_unique : forall b, (exists a, f a = b) -> exists! a, f a = b.
Proof.
  intros b [a Ha]. exists a. split.
  - exact Ha.
  - intros a' Ha'. apply f_inj. congruence.
Qed.

Lemma g_preimage_unique : forall a, (exists b, g b = a) -> exists! b, g b = a.
Proof.
  intros a [b Hb]. exists b. split.
  - exact Hb.
  - intros b' Hb'. apply g_inj. congruence.
Qed.

(* Partial inverses using DD (extraction of the unique preimage) *)
Definition f_inv (b : B) (H : exists a, f a = b) : A :=
  proj1_sig (@DD A (fun a => f a = b) (f_preimage_unique H)).
Arguments f_inv : clear implicits.

Definition g_inv (a : A) (H : exists b, g b = a) : B :=
  proj1_sig (@DD B (fun b => g b = a) (g_preimage_unique H)).
Arguments g_inv : clear implicits.

Lemma f_inv_spec : forall b (H : exists a, f a = b), f (f_inv b H) = b.
Proof.
  intros b H. unfold f_inv.
  destruct (@DD _ _ _) as [a Ha]. simpl. exact Ha.
Qed.

Lemma g_inv_spec : forall a (H : exists b, g b = a), g (g_inv a H) = a.
Proof.
  intros a H. unfold g_inv.
  destruct (@DD _ _ _) as [b Hb]. simpl. exact Hb.
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
  match em_inf (B_rooted a) with
  | left HBa => g_inv a (B_rooted_has_g_preimage HBa)
  | right _ => f a
  end.

(* ======================== *)
(* INJECTIVITY              *)
(* ======================== *)

Theorem h_injective : forall a1 a2, h a1 = h a2 -> a1 = a2.
Proof.
  intros a1 a2 Heq.
  unfold h in Heq.
  destruct (em_inf (B_rooted a1)) as [HB1 | HnB1];
  destruct (em_inf (B_rooted a2)) as [HB2 | HnB2].

  - (* Both B_rooted: g_inv a1 ... = g_inv a2 ... *)
    assert (H1 : g (g_inv a1 (B_rooted_has_g_preimage HB1)) = a1)
      by apply g_inv_spec.
    assert (H2 : g (g_inv a2 (B_rooted_has_g_preimage HB2)) = a2)
      by apply g_inv_spec.
    congruence.

  - (* a1 B_rooted, a2 not: g_inv a1 ... = f a2 *)
    exfalso.
    assert (HBgv : B_rooted_in_B (g_inv a1 (B_rooted_has_g_preimage HB1))).
    { apply g_preserves_B_rooted.
      rewrite g_inv_spec. exact HB1. }
    apply HnB2.
    apply f_preimage_B_rooted with (g_inv a1 (B_rooted_has_g_preimage HB1)).
    + symmetry. exact Heq.
    + exact HBgv.

  - (* a2 B_rooted, a1 not: f a1 = g_inv a2 ... *)
    exfalso.
    assert (HBgv : B_rooted_in_B (g_inv a2 (B_rooted_has_g_preimage HB2))).
    { apply g_preserves_B_rooted.
      rewrite g_inv_spec. exact HB2. }
    apply HnB1.
    apply f_preimage_B_rooted with (g_inv a2 (B_rooted_has_g_preimage HB2)).
    + exact Heq.
    + exact HBgv.

  - (* Neither B_rooted: f a1 = f a2 *)
    apply f_inj. exact Heq.
Qed.

(* ======================== *)
(* SURJECTIVITY             *)
(* ======================== *)

Theorem h_surjective : forall b, exists a, h a = b.
Proof.
  intro b.
  destruct (em_inf (B_rooted_in_B b)) as [HBb | HnBb].

  - (* b is B_rooted_in_B: use g b *)
    exists (g b).
    unfold h.
    destruct (em_inf (B_rooted (g b))) as [HBgb | HnBgb].
    + (* h (g b) = g_inv (g b) ... *)
      apply g_inj. apply g_inv_spec.
    + exfalso. apply HnBgb.
      apply B_rooted_in_B_implies_B_rooted_g. exact HBb.

  - (* b is not B_rooted_in_B: use f-preimage *)
    destruct (em_inf (exists a, f a = b)) as [Hex | Hnex].
    + destruct Hex as [a Ha].
      exists a.
      unfold h.
      destruct (em_inf (B_rooted a)) as [HBa | HnBa].
      * (* a B_rooted implies f a = b is B_rooted_in_B: contradiction *)
        exfalso. apply HnBb. apply chain_separation with a; assumption.
      * exact Ha.
    + (* b has no f-preimage: b is B_rooted_in_B base case *)
      exfalso. apply HnBb.
      exists 0. apply B_rooted_B_depth_0. exact Hnex.
Qed.

(* ======================== *)
(* CHAIN TRICHOTOMY         *)
(* ======================== *)

(* Nov 2026.  What the two cases of [h] cover.  Following the chain of a
   point backwards (a = g b, b = f a', ...), exactly three things can happen:
   it stops in B (this is B_rooted), it stops in A (at a point without a
   g-preimage), or it does not stop at any finite depth.  [h] uses g^-1 in
   the first case and f in the other two. *)

(* a'' is reached from a in n full backward steps *)
Inductive back : nat -> A -> A -> Prop :=
  | back_0 : forall a, back 0 a a
  | back_S : forall n a b a' a'',
      g b = a -> f a' = b -> back n a' a'' -> back (S n) a a''.

Definition A_stops (a : A) : Prop :=
  exists n a', back n a a' /\ no_g_preimage a'.

Definition B_stops (a : A) : Prop :=
  exists n a' b, back n a a' /\ g b = a' /\ no_f_preimage b.

Definition never_stops (a : A) : Prop :=
  forall n, exists a', back n a a'.

Lemma back_extend : forall n a a',
  back n a a' -> forall b a'', g b = a' -> f a'' = b -> back (S n) a a''.
Proof.
  intros n a a' H. induction H as [a | n a b a1 a2 Hg Hf Hb IH].
  - intros b a'' Hg Hf. apply back_S with b a''.
    + exact Hg.
    + exact Hf.
    + apply back_0.
  - intros b0 a'' Hg0 Hf0. apply back_S with b a1.
    + exact Hg.
    + exact Hf.
    + apply IH with b0; assumption.
Qed.

Lemma B_rooted_depth_back : forall n a,
  B_rooted_depth n a ->
  exists a' b, back n a a' /\ g b = a' /\ no_f_preimage b.
Proof.
  intros n a H. induction H as [a b Hg Hn | n a b a1 Hg Hf H1 IH].
  - exists a, b. split; [apply back_0 | split; assumption].
  - destruct IH as [a2 [b2 [Hb [Hg2 Hn2]]]].
    exists a2, b2. split; [| split; assumption].
    apply back_S with b a1; assumption.
Qed.

Lemma back_B_rooted_depth : forall n a a',
  back n a a' -> forall b, g b = a' -> no_f_preimage b -> B_rooted_depth n a.
Proof.
  intros n a a' H. induction H as [a | n a b a1 a2 Hg Hf Hb IH].
  - intros b Hg Hn. apply B_rooted_depth_0 with b; assumption.
  - intros b0 Hg0 Hn0. apply B_rooted_depth_S with b a1.
    + exact Hg.
    + exact Hf.
    + apply IH with b0; assumption.
Qed.

(* the criterion of the file is exactly "the chain stops in B" *)
Lemma B_rooted_iff_B_stops : forall a, B_rooted a <-> B_stops a.
Proof.
  intro a. split.
  - intros [n H]. destruct (@B_rooted_depth_back n a H) as [a' [b Hx]].
    exists n, a', b. exact Hx.
  - intros [n [a' [b [Hb [Hg Hn]]]]]. exists n.
    apply back_B_rooted_depth with a' b; assumption.
Qed.

Theorem chain_trichotomy :
  forall a : A, B_rooted a \/ A_stops a \/ never_stops a.
Proof.
  intro a.
  destruct (EM (B_rooted a)) as [HB | HnB]; [left; exact HB |].
  destruct (EM (A_stops a)) as [HA | HnA]; [right; left; exact HA |].
  right; right. intro n. induction n as [| n [a' Hb]].
  - exists a. apply back_0.
  - destruct (EM (exists b, g b = a')) as [[b Hgb] | Hno].
    + destruct (EM (exists a'', f a'' = b)) as [[a'' Hfa] | Hnf].
      * exists a''. apply back_extend with a' b; assumption.
      * exfalso. apply HnB. apply B_rooted_iff_B_stops.
        exists n, a', b. split; [exact Hb | split; [exact Hgb | exact Hnf]].
    + exfalso. apply HnA. exists n, a'. split; assumption.
Qed.

(* ======================== *)
(* MAIN THEOREM             *)
(* ======================== *)

(* From excluded middle and extraction of the unique witness. *)
Theorem Schroeder_Bernstein_definite : exists h : A -> B,
  (forall a1 a2, h a1 = h a2 -> a1 = a2) /\
  (forall b, exists a, h a = b).
Proof.
  exists h. split.
  - exact h_injective.
  - exact h_surjective.
Qed.

End SchroederBernstein.

(* The theorem under the two logical assumptions of the formalization:
   the instance of the premises at classic (L3) and L4_definite (L4 applied
   to a unique witness).  Statement unchanged. *)
Theorem Schroeder_Bernstein :
  forall (A B : Type) (f : A -> B) (g : B -> A),
    (forall a1 a2, f a1 = f a2 -> a1 = a2) ->
    (forall b1 b2, g b1 = g b2 -> b1 = b2) ->
    exists h : A -> B,
      (forall a1 a2, h a1 = h a2 -> a1 = a2) /\
      (forall b, exists a, h a = b).
Proof.
  intros A B f g Hf Hg.
  exact (@Schroeder_Bernstein_definite classic (@L4_definite) A B f g Hf Hg).
Qed.

(* ======================== *)
(* VERIFICATION             *)
(* ======================== *)

Check Schroeder_Bernstein_definite.
Print Assumptions Schroeder_Bernstein_definite.
(* Closed under the global context *)
Check Schroeder_Bernstein.
Print Assumptions Schroeder_Bernstein.
(* classic + L4_witness *)

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
   
   PRINCIPLES USED (as premises of Schroeder_Bernstein_definite):

   - EM: excluded middle - this is L3 in Theory of Systems
   - DD: extraction of the UNIQUE witness - for the partial inverses and
     for the truth-bit in em_inf

   Schroeder_Bernstein instantiates them at classic and L4_definite, so the
   compiler reports classic + L4_witness for it.  L4_witness in its full
   strength (an arbitrary witness; choice over families and epsilon follow
   from it) is not used.  No actual infinity: chains are characterized by
   FINITE depth.
*)
