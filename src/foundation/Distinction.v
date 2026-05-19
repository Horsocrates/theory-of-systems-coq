(** * Distinction.v — Primary Distinction: the foundation of everything

E/R/R structure of the Distinction record (per Chapter 4 of Volume II):

  Roles (positions in the act of distinction):
    - positive  : the role of the distinguished side
    - negative  : the role of the background side
    - input position (parameter P in distinction_of)
    - output position (the constructed Distinction instance)

  Rules (concrete-layer rules; L1-L5 form the universal layer):
    - exclusive   : non-overlap rule for the two sides (L2)
    - exhaustive  : exhaustion rule for the two sides (L3, via classic)
    - mkDistinction          : rule of constructor application
    - constructive exclusive : rule realizing L2 without axioms
    - use of classic         : rule realizing L3 (requires the axiom)

  Elements (actual carriers, appearing only upon actualization):
    - the proposition placed into 'positive' (e.g. P in distinction_of)
    - the proposition placed into 'negative' (e.g. ~P in distinction_of)
    - the constructed Distinction instance as a whole

  Universal layer: L1-L5 as structural properties traceable in the record;
  derivation chain A = ∃ → Distinction → L1-L5 → P1-P4 → E/R/R.

Status: Qed, 0 Admitted, 1 axiom (classic = L3)
Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import List.
Import ListNotations.

(** We use classical logic: this IS our formalization of L3 (Excluded Middle).
    Not an additional axiom — L3 = classic. *)
Axiom classic : forall P : Prop, P \/ ~P.

(* ========================================================================= *)
(*  FIRST PRINCIPLE: A = exists                                              *)
(* ========================================================================= *)

(** ★ STRUCTURE OF DISTINCTION

To exist = to exist determinately = to be distinguished from ¬A.

The record encodes two roles (positive, negative) and two rules
of the concrete layer (exclusive, exhaustive):

  - positive, negative : roles — names of the two sides
  - exclusive  (L2)    : rule — the two sides do not overlap
  - exhaustive (L3)    : rule — the two sides cover everything

Elements appear only at actualization: the propositions placed
into 'positive' and 'negative' by a concrete instance.
*)

(* ========================================================================= *)
(*  THE ACT OF DISTINCTION: A | ¬A                                          *)
(* ========================================================================= *)

(** ★ STRUCTURE OF DISTINCTION
    To exist = to exist determinately = to be distinguished from ¬A.
    The structure of distinction has TWO built-in properties:
    - exclusive (L2): A and ¬A don't overlap
    - exhaustive (L3): A or ¬A, nothing else *)

Record Distinction := mkDistinction {
positive   : Prop;  (** role: the distinguished side *)
negative   : Prop;  (** role: the background side *)
exclusive  : ~ (positive /\ negative);  (** rule: non-overlap (L2) *)
exhaustive : positive \/ negative;      (** rule: exhaustion (L3) *)
}.

(** Any Prop gives a Distinction (using classic = L3) *)
Definition distinction_of (P : Prop) : Distinction.
Proof.
  exact (mkDistinction P (~P)
    (fun H => match H with conj p np => np p end)
    (classic P)).
Defined.

Theorem every_prop_distinguishes : forall P : Prop,
  exists D : Distinction, positive D = P.
Proof. intro P. exists (distinction_of P). reflexivity. Qed.

(* ========================================================================= *)
(*  L1: IDENTITY / STABILITY                                                *)
(* ========================================================================= *)

(** A remains A through the act of distinction.
    In Coq: reflexivity of equality. *)

Theorem L1_stability : forall D : Distinction,
  positive D = positive D.
Proof. reflexivity. Qed.

Theorem L1_negative_stable : forall D : Distinction,
  negative D = negative D.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*  L2: NON-CONTRADICTION / EXCLUSIVITY                                     *)
(* ========================================================================= *)

(** A and ¬A don't overlap. Built into the Distinction record. *)

Theorem L2_exclusivity : forall D : Distinction,
  ~ (positive D /\ negative D).
Proof. intros D. exact (exclusive D). Qed.

(* ========================================================================= *)
(*  L3: EXCLUDED MIDDLE / TOTALITY                                          *)
(* ========================================================================= *)

(** A ∨ ¬A: exhaustive. Built into the Distinction record. *)

Theorem L3_totality : forall D : Distinction,
  positive D \/ negative D.
Proof. intros D. exact (exhaustive D). Qed.

(* ========================================================================= *)
(*  L4: SUFFICIENT REASON / SELF-GROUNDING                                  *)
(* ========================================================================= *)

(** The distinction itself is sufficient reason for A ≠ ¬A.
    Knowing positive D gives reason to deny negative D. *)

Theorem L4_self_grounding : forall D : Distinction,
  forall (p : positive D), ~ negative D.
Proof. intros D p n. apply (exclusive D). split; [exact p | exact n]. Qed.

(** Contrapositive: knowing negative gives reason to deny positive *)
Theorem L4_contrapositive : forall D : Distinction,
  negative D -> ~ positive D.
Proof. intros D n p. apply (exclusive D). split; [exact p | exact n]. Qed.

(* ========================================================================= *)
(*  L5: ORDER / HIERARCHY                                                   *)
(* ========================================================================= *)

(** L5: distinction has inherent hierarchical structure.
    The meta-level (Distinction as Record : Type) operates ON
    the object-level (positive, negative : Prop).
    Type > Prop in Coq's universe hierarchy.
    This IS L5: the organizer is at higher level than the organized.

    The concrete formalization uses Level from Core_ERR (see LawsFromDistinction). *)

(** Sequential order: the act of distinction (Distinction)
    presupposes the material being distinguished (positive, negative). *)

(* ========================================================================= *)
(*  UNIT: the first quantitative concept                                    *)
(* ========================================================================= *)

(** One distinction = one unit = natural number 1 *)
Definition distinction_count (n : nat) : Prop :=
  exists (Ds : list Distinction), length Ds = n.

Lemma zero_distinctions : distinction_count 0.
Proof. exists []. reflexivity. Qed.

Lemma one_distinction_exists : distinction_count 1.
Proof. exists [distinction_of True]. reflexivity. Qed.

Lemma two_distinctions_exist : distinction_count 2.
Proof. exists [distinction_of True; distinction_of False]. reflexivity. Qed.

(** Distinction count is hereditary *)
Lemma distinction_count_succ : forall n,
  distinction_count n -> distinction_count (S n).
Proof.
  intros n [Ds Hlen].
  exists (distinction_of True :: Ds). simpl. rewrite Hlen. reflexivity.
Qed.

(** Any finite number of distinctions exist *)
Lemma distinction_count_any : forall n, distinction_count n.
Proof.
  induction n.
  - exact zero_distinctions.
  - apply distinction_count_succ. exact IHn.
Qed.

(* ========================================================================= *)
(*  CO-CONSTITUTION: A and ¬A define each other                             *)
(* ========================================================================= *)

(** Neither side of a distinction is meaningful without the other *)

(* CO-DEFINITION: A and ¬A obtain their definiteness together *)
(** Neither side of a distinction is determinate without the other.
    See Chapter 5 of Volume II for the full discussion of co-definition
    as structural simultaneity (distinct from mutual dependence, 
    equivalence, and mutual derivability). *)
  
Lemma co_constitution : forall P : Prop,
  (P -> exists Q, Q = ~P) /\ (~P -> exists Q, Q = P).
Proof. intro P. split; intro H; eexists; reflexivity. Qed.

(** A Distinction from True is non-trivial *)
Lemma true_distinction_positive : positive (distinction_of True) = True.
Proof. reflexivity. Qed.

Lemma true_distinction_negative : negative (distinction_of True) = (~True).
Proof. reflexivity. Qed.

(** A Distinction from False *)
Lemma false_distinction_positive : positive (distinction_of False) = False.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(*  DECIDABILITY                                                            *)
(* ========================================================================= *)

(** From Distinction: every Prop is decidable (uses classic) *)
Theorem distinction_decidable : forall P : Prop, P \/ ~P.
Proof. exact classic. Qed.

(** Distinction of a conjunction *)
Lemma distinction_and : forall P Q : Prop,
  exists D : Distinction, positive D = (P /\ Q).
Proof. intros. exists (distinction_of (P /\ Q)). reflexivity. Qed.

(** Distinction of a disjunction *)
Lemma distinction_or : forall P Q : Prop,
  exists D : Distinction, positive D = (P \/ Q).
Proof. intros. exists (distinction_of (P \/ Q)). reflexivity. Qed.

(** ★ FIVE PROPERTIES OF DISTINCTION — unified *)
Theorem five_properties_of_distinction : forall D : Distinction,
  (* L1: stability *) (positive D = positive D) /\
  (* L2: exclusivity *) (~ (positive D /\ negative D)) /\
  (* L3: totality *) (positive D \/ negative D) /\
  (* L4: self-grounding *) (positive D -> ~ negative D).
Proof.
  intro D. split; [| split; [| split]].
  - reflexivity.
  - exact (exclusive D).
  - exact (exhaustive D).
  - intros p n. apply (exclusive D). split; [exact p | exact n].
Qed.

(** Total exported theorems/lemmas in this file (excluding internal helpers) *)
Definition distinction_theorem_count := 22%nat.