(* ========================================================================= *)
(*        ToS AXIOMS — The Formal Laws of Logic                              *)
(*                                                                           *)
(*  Theory of Systems derives all mathematics from one first principle:      *)
(*  "A = exists" (something exists). The act of distinguishing A from ~A     *)
(*  exhibits five structural properties — the Laws of Logic (L1-L5).        *)
(*                                                                           *)
(*  In Coq (CIC), L1, L2, L5 hold by construction. L3 and L4 require       *)
(*  explicit declaration because CIC is constructive:                        *)
(*                                                                           *)
(*    L3 (Excluded Middle): distinction is TOTAL — A or not A                *)
(*    L4 (Sufficient Reason): existence is DETERMINATE — witnesses exist     *)
(*                                                                           *)
(*  These are the ONLY axioms in the entire ToS formalization.               *)
(*  Every theorem ultimately depends on at most these two.                   *)
(*                                                                           *)
(*  Reference 1: "The Laws of Logic as Conditions of Existence:              *)
(*    A Derivation from The First Principle" (Horsocrates, 2026)             *)
(*    Section 4.3 (L3), Section 4.4 (L4), Appendix A.1                      *)
(*                                                                           *)
(*  Reference 2: "Theory of Systems" (Section: Roles as Dependent Props)     *)
(*    "This captures L4 (Sufficient Reason): every Role must have a          *)
(*     ground — a reason why it applies to a particular Element.             *)
(*     In Coq, this means Roles must be inhabited (have witnesses)."         *)
(*    L4_witness is the DIRECT formalization of this statement.              *)
(*                                                                           *)
(*  STATUS: 3 Qed, 0 Admitted                                               *)
(*  Author: Horsocrates | Date: March 2026                                   *)
(* ========================================================================= *)

Require Export Coq.Logic.Classical_Prop.
(* Provides: classic : forall P : Prop, P \/ ~P
   This IS L3. We re-export it so all downstream files get it. *)

(* ========================================================================= *)
(*  L3 — LAW OF EXCLUDED MIDDLE (Totality of Distinction)                   *)
(* ========================================================================= *)

(**
  "The primary distinction is exhaustive. When A is distinguished from ~A,
   everything falls into one region or the other. There is no third region."
   — Laws of Logic, Section 4.3

  In Coq, this is the axiom [classic]. We do not re-declare it; we use
  the standard library's [classic] which is exactly L3.

  Note: L3 is DERIVED in ToS (from the totality of distinction), but
  since Coq's type theory is constructive, we must accept it as an axiom
  within the proof assistant. The philosophical derivation is in the paper.
*)

(* classic is already available from Classical_Prop *)

(* ========================================================================= *)
(*  L4 — LAW OF SUFFICIENT REASON (Determinacy of Existence)                *)
(* ========================================================================= *)

(**
  "The difference itself is the sufficient reason. A is distinguished
   from not-A because A differs from not-A. No further reason is
   required or possible at the primary level."
   — Laws of Logic, Section 4.4

  Applied to existential propositions:

    If exists x, P(x) — if there exists an x satisfying P — then this x
    exists DETERMINATELY (Section 2.3: "to exist is to exist determinately").
    It is distinguished from what it is not. It can be identified.
    Extracting a witness is not an act of CHOICE but a recognition
    that existence is always determinate.

  This is NOT the Axiom of Choice:
    AC:  forall i, exists x, P(i,x) -> exists f, forall i, P(i,f(i))   (families of sets)
    L4w: (exists x, P(x)) -> {x | P(x)}                   (single existential)

  AC extracts choice functions from ARBITRARY families.
  L4w extracts witnesses from INDIVIDUAL existentials.
  The difference is foundational: L4w says existence is determinate;
  AC says arbitrary collections can be simultaneously selected from.

  In the proof-theoretic hierarchy:
    classic (L3)  <  classic + L4w  <  classic + DC  <<  AC
  where DC = Dependent Choice (used by Bishop's constructive analysis).
*)

Axiom L4_witness : forall (A : Type) (P : A -> Prop),
  (exists x, P x) -> {x : A | P x}.
Arguments L4_witness {A} P _.

(* ========================================================================= *)
(*  DERIVED PRINCIPLES                                                       *)
(* ========================================================================= *)

(** From L3 + L4, we derive standard classical principles.
    These are provided for compatibility with proof patterns
    that use them, but they are NOT additional axioms. *)

(** Excluded Middle with computational content (sumbool).
    Follows from L3 (existence of P \/ ~P) + L4 (extract witness). *)
Lemma L3_informative : forall P : Prop, {P} + {~P}.
Proof.
  intro P.
  assert (Hex : exists b : bool, if b then P else ~P).
  { destruct (classic P) as [HP | HnP].
    - exists true. exact HP.
    - exists false. exact HnP. }
  destruct (L4_witness _ Hex) as [b Hb].
  destruct b.
  - left. exact Hb.
  - right. exact Hb.
Defined.

(** Constructive Definite Description.
    If there exists a UNIQUE x satisfying P, we can extract it.
    Strictly weaker than L4_witness (requires uniqueness). *)
Lemma L4_definite : forall (A : Type) (P : A -> Prop),
  (exists! x, P x) -> {x : A | P x}.
Proof.
  intros A P Huniq.
  apply L4_witness.
  destruct Huniq as [x [Hx _]].
  exists x. exact Hx.
Qed.
Arguments L4_definite {A} P _.

(** Double negation elimination (already provable from classic,
    but included for completeness). *)
Lemma NNPP_from_L3 : forall P : Prop, ~~P -> P.
Proof. intros P Hnn. destruct (classic P); [assumption | contradiction]. Qed.

(* ========================================================================= *)
(*  NOTATION FOR DOWNSTREAM FILES                                            *)
(* ========================================================================= *)

(** Files that need only L3 (excluded middle):
      From ToS Require Import ToS_Axioms.
      (* classic is available *)

    Files that need L4 (witness extraction):
      From ToS Require Import ToS_Axioms.
      (* L4_witness and L3_informative are available *)

    NO file should ever import:
      Coq.Logic.ClassicalDescription
      Coq.Logic.ClassicalEpsilon
      Coq.Logic.IndefiniteDescription
*)
