(** * ERRTierIIResidue.v — dissolving the three residual Tier-II "soft walls" of the E/R/R category /
      dynamics, in one file.  Each was an UNFORCED lightness (a deliberately weak choice), not a
      role-limit; each dissolves 0-axiom.

      ★ WALL 1 (ERRDynamicsConjugacy: "set-conjugacy, Roles-preservation not required").  Strengthen to
        a ROLES-PRESERVING iso-conjugacy (the relabeling is an ERRMorphism iso).  iso_conjugate_is_
        conjugate: this is STRONGER — it implies the plain set-conjugacy.  Inhabited (flip).

      ★ WALL 2 (ERRDynamicsAction: "flip's return-submonoid ⊇ 2*nat, not exactly").  Pin it EXACTLY:
        return_times flip true n <-> Nat.Even n.

      ★ WALL 3 (ERRDynamicsInvariant: "sub-dynamics = a restricted map, not a full sub-FunctionalSystem
        — the constitution need not restrict").  For a RESTRICTION-STABLE constitution (one that
        survives passage to a subset), the sub-system IS a genuine FunctionalSystem (fs_subsystem),
        with an inclusion morphism (fs_incl).  Equivalence and Trivial are restriction-stable.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      sameness-of-dynamics can be carried by a Roles-PRESERVING iso (stronger than a set-bijection);
      flip's return-time submonoid is EXACTLY the evens; a sub-OBJECT is a genuine constituted system
      whenever the constitution survives restriction to a subset.
    Roles (L4): IsoConjugate (Roles-preserving conjugacy); return_times/Nat.Even (the exact submonoid);
      restriction_stable / fs_subsystem / fs_incl (the constituted sub-object).
    Elements (L1+P4): the dynamics; the carrier and its subset; the relabelings.
    P4 diagnostic (could it be otherwise?):
      all three were UNFORCED lightnesses (set-vs-iso, ⊇-vs-exact, map-vs-system) — none is a role-limit,
      so each dissolves with more work; the constitutive H1 wall is untouched.
    Honesty wall:
      iso-conjugacy IMPLIES set-conjugacy (strictly stronger; not conversely without the Roles data);
      the inclusion's mono-ness (injectivity) is the separate proof-irrelevance / decidability question
      (handled finitely in ERRFiniteQuotient) — here we give the sub-system OBJECT + the inclusion
      morphism; restriction_stable is shown for Equivalence and Trivial.  Reuses ERRDynamics*,
      ERRDynamicsConjugacy, ERRIso, ERRComposition.  0 axioms.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.       (* ERRMorphism, mkERRMorphism, err_map, err_id *)
From ToS Require Import foundation.ERRDynamics.            (* InsideOperator, evolve, SB *)
From ToS Require Import foundation.ERRDynamicsArrow.       (* flip *)
From ToS Require Import foundation.ERRDynamicsAction.      (* return_times *)
From ToS Require Import foundation.ERRDynamicsConjugacy.   (* conjugacy, Conjugate *)
From ToS Require Import foundation.ERRIso.                 (* iso *)
From Stdlib Require Import PeanoNat Bool.

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  WALL 1 — conjugacy via a Roles-preserving iso                          *)
(* ===================================================================== *)

(** A Roles-PRESERVING iso-conjugacy: the relabeling is an ERRMorphism iso intertwining the steps. *)
Definition IsoConjugate {L} {S S' : FunctionalSystem L} (f : InsideOperator S) (f' : InsideOperator S')
  : Prop :=
  exists phi : ERRMorphism S S',
    iso phi /\ (forall x, err_map phi (err_map f x) = err_map f' (err_map phi x)).

(** ★★ A Roles-preserving iso-conjugacy IMPLIES the (weaker) set-conjugacy — so it is strictly
    stronger: the wall ("Roles-preservation not required") dissolves by requiring it. *)
Lemma iso_conjugate_is_conjugate : forall {L} {S S' : FunctionalSystem L}
  (f : InsideOperator S) (f' : InsideOperator S'),
  IsoConjugate f f' -> Conjugate f f'.
Proof.
  intros L S S' f f' [phi [[psi [Hpp Hpp']] Hint]].
  exists (err_map phi), (err_map psi). split; [ exact Hpp | split; [ exact Hpp' | exact Hint ] ].
Qed.

(** ★ Inhabited: flip is iso-conjugate to itself (the identity iso intertwines). *)
Lemma flip_iso_conjugate_self : IsoConjugate flip flip.
Proof.
  exists (err_id SB). split.
  - exists (err_id SB). split; intro x; reflexivity.
  - intro x. reflexivity.
Qed.

(* ===================================================================== *)
(*  WALL 2 — flip's return-submonoid is EXACTLY the evens                  *)
(* ===================================================================== *)

(** Parity successor. *)
Lemma even_S : forall k, Nat.even (Datatypes.S k) = negb (Nat.even k).
Proof.
  induction k as [|j IH].
  - reflexivity.
  - change (Nat.even (Datatypes.S (Datatypes.S j))) with (Nat.even j).
    rewrite IH. rewrite Bool.negb_involutive. reflexivity.
Qed.

(** The flip orbit from `true` evaluates to the parity bit. *)
Lemma flip_true_eval : forall n, evolve flip true n = Nat.even n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - change (evolve flip true (Datatypes.S k)) with (negb (evolve flip true k)).
    rewrite IH. rewrite even_S. reflexivity.
Qed.

(** ★★ flip's return-time submonoid is EXACTLY the even numbers. *)
Lemma flip_return_iff_even : forall n, return_times flip true n <-> Nat.Even n.
Proof.
  intro n. unfold return_times. rewrite flip_true_eval. apply Nat.even_spec.
Qed.

(* ===================================================================== *)
(*  WALL 3 — a genuine sub-system for a restriction-stable constitution    *)
(* ===================================================================== *)

(** A constitution is RESTRICTION-STABLE if it survives passage to a subset (with the restricted
    relation). *)
Definition restriction_stable (C : Constitution) : Prop :=
  forall (D : Type) (R : D -> D -> Prop) (P : D -> Prop),
    C D R -> C { x : D | P x } (fun a b => R (proj1_sig a) (proj1_sig b)).

Lemma equiv_restriction_stable : restriction_stable EquivalenceConstitution.
Proof.
  intros D R P [Hr [Hs Ht]]. split; [ | split ].
  - intro a. apply Hr.
  - intros a b H. apply Hs. exact H.
  - intros a b c Hab Hbc. apply Ht with (proj1_sig b); assumption.
Qed.

Lemma trivial_restriction_stable : restriction_stable TrivialConstitution.
Proof. intros D R P _. exact I. Qed.

(** ★★ The sub-system on a subset A is a GENUINE FunctionalSystem when C is restriction-stable. *)
Definition fs_subsystem {L} (C : Constitution) (HC : restriction_stable C)
  (S : FunctionalSystem L) (H : fs_constitution S = C) (A : get_Elements S -> Prop)
  : FunctionalSystem L.
Proof.
  refine {| fs_constitution := C;
            fs_domain := { x : get_Elements S | A x };
            fs_relations := (fun a b => get_Roles S (proj1_sig a) (proj1_sig b));
            fs_functional := _;
            fs_element_level := fun a => fs_element_level S (proj1_sig a);
            fs_level_valid := fun a => fs_level_valid S (proj1_sig a) |}.
  apply HC. rewrite <- H. exact (fs_functional S).
Defined.

(** The inclusion morphism (sub-system into the whole). *)
Definition fs_incl {L} (C : Constitution) (HC : restriction_stable C)
  (S : FunctionalSystem L) (H : fs_constitution S = C) (A : get_Elements S -> Prop)
  : ERRMorphism (fs_subsystem C HC S H A) S :=
  @mkERRMorphism L (fs_subsystem C HC S H A) S (fun a => proj1_sig a) (fun x y Hr => Hr).

(** ★ The sub-system's triad: carrier = the subset, Roles = restricted, Rules = C. *)
Lemma fs_subsystem_triad : forall {L} C HC (S : FunctionalSystem L) H (A : get_Elements S -> Prop),
  get_Elements (fs_subsystem C HC S H A) = { x : get_Elements S | A x }
  /\ get_Roles (fs_subsystem C HC S H A) = (fun a b => get_Roles S (proj1_sig a) (proj1_sig b))
  /\ fs_constitution (fs_subsystem C HC S H A) = C.
Proof. intros. split; [ reflexivity | split; reflexivity ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE THREE RESIDUAL TIER-II WALLS DISSOLVED:
      (conjugacy)   a Roles-preserving iso-conjugacy implies set-conjugacy (stronger), and is inhabited;
      (flip exact)  flip's return-time submonoid is EXACTLY the evens;
      (sub-system)  a restriction-stable constitution gives a genuine sub-FunctionalSystem.
    Each was an unforced lightness, not a role-limit; the constitutive H1 wall is untouched. *)
Theorem err_tier2_residue :
  ((forall (L : Level) (S S' : FunctionalSystem L) (f : InsideOperator S) (f' : InsideOperator S'),
      IsoConjugate f f' -> Conjugate f f')
   /\ IsoConjugate flip flip)
  /\ (forall n, return_times flip true n <-> Nat.Even n)
  /\ (restriction_stable EquivalenceConstitution /\ restriction_stable TrivialConstitution)
  /\ (forall (L : Level) C HC (S : FunctionalSystem L) H (A : get_Elements S -> Prop),
        get_Elements (fs_subsystem C HC S H A) = { x : get_Elements S | A x }
        /\ get_Roles (fs_subsystem C HC S H A) = (fun a b => get_Roles S (proj1_sig a) (proj1_sig b))
        /\ fs_constitution (fs_subsystem C HC S H A) = C).
Proof.
  split; [ split; [ exact @iso_conjugate_is_conjugate | exact flip_iso_conjugate_self ] | ].
  split; [ exact flip_return_iff_even | ].
  split; [ split; [ exact equiv_restriction_stable | exact trivial_restriction_stable ] | ].
  exact @fs_subsystem_triad.
Qed.

Print Assumptions err_tier2_residue.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Dissolves the 3 residual Tier-II walls.  WALL 1: IsoConjugate (Roles-     *)
(*  preserving iso-conjugacy) + iso_conjugate_is_conjugate (implies set-       *)
(*  conjugacy) + flip_iso_conjugate_self.  WALL 2: even_S + flip_true_eval     *)
(*  (evolve flip true n = Nat.even n) + flip_return_iff_even (return-submonoid *)
(*  = exactly the evens, via Nat.even_spec).  WALL 3: restriction_stable +     *)
(*  equiv/trivial_restriction_stable + fs_subsystem (a genuine sub-Functional  *)
(*  System) + fs_incl (inclusion morphism) + fs_subsystem_triad.  Capstone     *)
(*  err_tier2_residue.  HONEST: iso-conjugacy is strictly stronger; the        *)
(*  inclusion's injectivity (mono) is the separate PI/decidability question    *)
(*  (ERRFiniteQuotient) — here the sub-system OBJECT + inclusion are given.    *)
(*  None of the three is a role-limit; the H1 wall (Tier III) is untouched.    *)
(* ========================================================================= *)
