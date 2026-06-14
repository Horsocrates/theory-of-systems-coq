(** * ERRCoproductEmergence.v — deepening ③: the COPRODUCT is the SEPARATED / reducible pole (the dual
      of entanglement), yet cross-summand relating is genuine emergence over the sum.  This UNIFIES the
      product-side emergence taxonomy (① ERREntanglement / ERREmergenceTaxonomy) with the coproduct (③).

    On the PRODUCT side (①): the baseline is prod_rel; a composite whose Roles do not factor as a
    product is EMERGENT (entangled — parity_roles).  On the COPRODUCT side (here): the baseline is
    sum_rel; a relation on the disjoint union that relates ACROSS summands cannot factor as any sum —
    it is emergent over the coproduct.  Both baselines are minimal; both can be exceeded.

      ★ sum_reducible R — R factors as some sum_rel (relates only within summands).  The coproduct's
        Roles ARE sum_reducible (coproduct_is_reducible) — zero cross-emergence (the separated pole).
      ★ The injections are FULL & FAITHFUL on Roles: a summand embeds exactly (inl_faithful /
        inr_faithful) — the coproduct adds nothing within a part, it only separates the parts.
      ★ CROSS-EMERGENCE is real: the full relation on unit+unit relates inl to inr, so it is NOT
        sum_reducible (full_cross_emergent); cross_system is a genuine SYSTEM exhibiting it
        (cross_system_emergent) — the dual of parity_system.
      ★ DUALITY: both poles can be exceeded — ~ separable parity_roles (product side, cited) alongside
        the cross-emergent witness (coproduct side).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      the COPRODUCT is sum-reducible (no cross-summand relating — the separated pole, dual of
      entanglement); cross-relating EXCEEDS the sum (emergence over the coproduct); BOTH baselines
      (prod_rel and sum_rel) are minimal and exceedable.
    Roles (L4): sum_reducible / cross_emergent (the sum-side taxonomy); coproduct_is_reducible;
      inl_faithful / inr_faithful (faithful embedding); cross_system (the emergent witness); parity
      (product side, cited).
    Elements (L1+P4): the disjoint-union carrier; the relations; the systems.
    P4 diagnostic (could it be otherwise?):
      the coproduct COULD relate across summands (the full relation) but DOES NOT (sum_rel) — the
      separated baseline is a choice; cross-emergence is the realized alternative (cross_system), the
      dual of prod_rel vs parity.
    Honesty wall:
      sum_reducible is the sum-carrier analog of separable (prod-carrier) — they live on DIFFERENT
      carriers (D1+D2 vs D1*D2), so the duality is STRUCTURAL, not a literal instance; cross-emergence
      is shown at the relation level (full) + by a genuine system (cross_system); the product-side
      witness (parity) is cited from ERREntanglement.  Unifies ① and ③.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.    (* (context) *)
From ToS Require Import foundation.ERRCoproduct.       (* sum_rel, fs_coproduct *)
From ToS Require Import foundation.ERREntanglement.    (* separable, parity_roles, parity_not_separable *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  SUM-REDUCIBILITY — the coproduct analog of separability               *)
(* ===================================================================== *)

(** A relation on a disjoint union is SUM-REDUCIBLE if it factors as some sum_rel (it relates only
    within summands).  This is the sum-carrier analog of `separable` on the product carrier. *)
Definition sum_reducible {D1 D2 : Type} (R : (D1 + D2) -> (D1 + D2) -> Prop) : Prop :=
  exists (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop), forall p q, R p q <-> sum_rel R1 R2 p q.

(** CROSS-EMERGENT = not sum-reducible (it relates across summands beyond any sum). *)
Definition cross_emergent {D1 D2 : Type} (R : (D1 + D2) -> (D1 + D2) -> Prop) : Prop :=
  ~ sum_reducible R.

(** ★ Every sum_rel is (trivially) sum-reducible. *)
Lemma sum_rel_reducible : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop),
  sum_reducible (sum_rel R1 R2).
Proof. intros D1 D2 R1 R2. exists R1, R2. intros p q. split; intro H; exact H. Qed.

(** ★★ The COPRODUCT is sum-reducible — the separated pole, zero cross-emergence. *)
Lemma coproduct_is_reducible : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  sum_reducible (get_Roles (fs_coproduct S1 S2 H1 H2)).
Proof. intros. apply sum_rel_reducible. Qed.

(** ★★ Hence the coproduct is NOT cross-emergent. *)
Lemma coproduct_not_cross_emergent : forall {L} (S1 S2 : FunctionalSystem L) H1 H2,
  ~ cross_emergent (get_Roles (fs_coproduct S1 S2 H1 H2)).
Proof. intros L S1 S2 H1 H2 Hce. apply Hce. apply coproduct_is_reducible. Qed.

(* ===================================================================== *)
(*  THE INJECTIONS ARE FULL & FAITHFUL ON ROLES                           *)
(* ===================================================================== *)

(** ★ The left summand embeds EXACTLY: sum_rel restricted to inl is R1 (full & faithful). *)
Lemma inl_faithful : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop) (a a' : D1),
  sum_rel R1 R2 (inl a) (inl a') <-> R1 a a'.
Proof. intros. simpl. split; intro H; exact H. Qed.

(** ★ The right summand embeds EXACTLY. *)
Lemma inr_faithful : forall {D1 D2 : Type} (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop) (b b' : D2),
  sum_rel R1 R2 (inr b) (inr b') <-> R2 b b'.
Proof. intros. simpl. split; intro H; exact H. Qed.

(* ===================================================================== *)
(*  CROSS-EMERGENCE IS REAL — relating across summands                     *)
(* ===================================================================== *)

(** ★★ The FULL relation on unit+unit relates inl to inr, so it is NOT sum-reducible: cross-summand
    relating is genuine emergence over the coproduct (the dual of entanglement). *)
Lemma full_cross_emergent : cross_emergent (fun (_ _ : unit + unit) => True).
Proof.
  intros [R1 [R2 Hiff]]. destruct (Hiff (inl tt) (inr tt)) as [Hfwd _]. exact (Hfwd I).
Qed.

(** A genuine SYSTEM on the disjoint union with the full relation (the dual of parity_system). *)
Definition cross_system : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := EquivalenceConstitution; fs_domain := (unit + unit)%type;
            fs_relations := (fun _ _ => True); fs_functional := _;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => L1_lt_L2 |}.
  unfold EquivalenceConstitution. split; [ | split ].
  - intro x. exact I.
  - intros x y _. exact I.
  - intros x y z _ _. exact I.
Defined.

(** ★★ cross_system is cross-emergent: its Roles relate across summands, exceeding any sum. *)
Lemma cross_system_emergent : ~ sum_reducible (get_Roles cross_system).
Proof. exact full_cross_emergent. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ COPRODUCT & EMERGENCE — the sum/product duality of decomposability:
      (reducible)    every sum_rel is sum-reducible; the coproduct is sum-reducible (separated pole);
      (cross-emerg.) the full relation / cross_system relate across summands — emergent over the sum;
      (duality)      both baselines can be exceeded: parity exceeds prod_rel (entanglement) just as
                     cross_system exceeds sum_rel (cross-emergence).
    The coproduct is the maximally decomposable (separated) pole, the dual of entanglement; yet
    emergence over the sum is real, mirroring the product side. *)
Theorem err_coproduct_emergence :
  (forall (D1 D2 : Type) (R1 : D1 -> D1 -> Prop) (R2 : D2 -> D2 -> Prop), sum_reducible (sum_rel R1 R2))
  /\ (forall (L : Level) (S1 S2 : FunctionalSystem L) H1 H2,
        sum_reducible (get_Roles (fs_coproduct S1 S2 H1 H2)))
  /\ cross_emergent (fun (_ _ : unit + unit) => True)
  /\ ~ sum_reducible (get_Roles cross_system)
  /\ ~ separable parity_roles.
Proof.
  split; [ exact @sum_rel_reducible | ].
  split; [ exact @coproduct_is_reducible | ].
  split; [ exact full_cross_emergent | ].
  split; [ exact cross_system_emergent | exact parity_not_separable ].
Qed.

Print Assumptions err_coproduct_emergence.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Deepens ③ and UNIFIES with ①.  sum_reducible (sum-carrier analog of        *)
(*  separable), cross_emergent (= not sum-reducible).  sum_rel_reducible +     *)
(*  coproduct_is_reducible (the coproduct is the separated pole) +             *)
(*  coproduct_not_cross_emergent.  inl_faithful / inr_faithful (summands embed *)
(*  exactly).  full_cross_emergent + cross_system + cross_system_emergent      *)
(*  (cross-summand relating is real emergence — dual of parity_system).        *)
(*  Capstone err_coproduct_emergence juxtaposes BOTH poles: ~ separable        *)
(*  parity_roles (product side, cited) ∥ cross-emergence (coproduct side).     *)
(*  HONEST: sum_reducible vs separable live on different carriers (D1+D2 vs    *)
(*  D1*D2) — the duality is structural, not a literal instance.               *)
(* ========================================================================= *)
