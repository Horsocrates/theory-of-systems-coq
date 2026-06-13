(** * ERRSystemBridge.v — довесок: the BRIDGE between the project's two notions of "system" —
      the indexed criterion-System L embeds into the E/R/R FunctionalSystem (closes §9.1 of the свод).

    The свод flagged §9.1: the repo has TWO unmerged "System" notions —
      (I)  the indexed System L (Core_ERR Part III): a Criterion (domain + predicate + level-witness)
           plus position-bound and uniqueness — the P1/P2 paradox-blocking core;
      (II) the FunctionalSystem L (Core_ERR §XVII): the E/R/R triple (Elements/Roles/Rules) — the
           canonical E/R/R object.
    They were never related.  This file gives the map (I) -> (II): every indexed System yields an
    E/R/R FunctionalSystem.

      ★ system_to_FS : System L -> FunctionalSystem L.
        Elements := the MEMBERS {x : crit_domain | crit_predicate x};
        Roles    := equality (the canonical DISCRETE relation — the indexed System has no native one);
        Rules    := EquivalenceConstitution (equality is an equivalence);
        P1-grading := the criterion's level-witness (so the criterion's P2 BECOMES the E/R/R P1).

    Honest scope: the bridge is an EMBEDDING, not an equivalence.  The indexed System is structurally
    thinner — it has no native Roles or Rules — so the E/R/R image carries the CANONICAL (discrete)
    Roles and Rules; and the indexed System's position-bound and uniqueness are dropped (residue).
    The E/R/R FunctionalSystem is strictly richer.  But the two notions are now RELATED by a
    structure-respecting map, closing §9.1.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) every indexed System L yields an E/R/R FunctionalSystem (system_to_FS): Elements = members,
          Roles = discrete equality, Rules = equivalence;
      (2) the criterion's P2 (witness << L) BECOMES the E/R/R P1-grading (bridge_grading_valid);
      (3) the bridge is an EMBEDDING, not an equivalence — the E/R/R image is strictly richer (carries
          Roles/Rules the criterion-System lacks); position-bound / uniqueness are residue.
    Roles (L4): system_to_FS = the bridge; crit_predicate -> the members subtype; crit_level_witness
      -> the P1-grading; eq = the canonical Roles.
    Elements (L1+P4): the indexed systems; the criterion; the members subtype.
    P4 diagnostic (could it be otherwise?):
      The criterion-System is structurally thinner (no native Roles/Rules), so its E/R/R image is the
      CANONICAL discrete system on its members; the bridge is forced on Elements (= members) and on
      the grading (P1 = the criterion's P2-witness), free/canonical on Roles/Rules.
    Honesty wall:
      the bridge is LOSSY (the predicate becomes the members subtype; position-bound and uniqueness
      are dropped; Roles/Rules are canonical) — an EMBEDDING of the criterion-System into E/R/R, not
      an isomorphism.  It closes §9.1 honestly: the two notions are RELATED by a map, the E/R/R one
      being richer.  0 axioms.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.

(* Restore implicit {L} on the FunctionalSystem projections (section-local in Core_ERR). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  THE BRIDGE: indexed System L -> E/R/R FunctionalSystem                  *)
(* ===================================================================== *)

(** ★ Every indexed (criterion) System yields an E/R/R FunctionalSystem: Elements = the members
    {x | crit_predicate x}, Roles = equality, Rules = equivalence, P1-grading = the criterion's
    level-witness. *)
Definition system_to_FS {L} (S : System L) : FunctionalSystem L.
Proof.
  refine {| fs_constitution := EquivalenceConstitution;
            fs_domain := sig (crit_predicate L (sys_criterion L S));
            fs_relations := @eq (sig (crit_predicate L (sys_criterion L S)));
            fs_functional := _;
            fs_element_level := fun _ => crit_level_witness L (sys_criterion L S);
            fs_level_valid := fun _ => crit_level_valid L (sys_criterion L S) |}.
  split.
  - intro x. reflexivity.
  - split.
    + intros x y Hxy. symmetry. exact Hxy.
    + intros x y z Hxy Hyz. exact (eq_trans Hxy Hyz).
Defined.

(* ===================================================================== *)
(*  WHAT THE BRIDGE PRESERVES / SENDS                                      *)
(* ===================================================================== *)

(** ★ Elements of the image = the MEMBERS of the criterion-System. *)
Lemma bridge_elements : forall L (S : System L),
  get_Elements (system_to_FS S) = sig (crit_predicate L (sys_criterion L S)).
Proof. intros. reflexivity. Qed.

(** ★ Roles of the image = the canonical DISCRETE relation (equality) — the criterion-System has no
    native relation, so the bridge supplies the minimal one. *)
Lemma bridge_roles : forall L (S : System L),
  get_Roles (system_to_FS S) = @eq (sig (crit_predicate L (sys_criterion L S))).
Proof. intros. reflexivity. Qed.

(** ★ Rules of the image = EquivalenceConstitution (equality is an equivalence). *)
Lemma bridge_rules : forall L (S : System L),
  fs_constitution (system_to_FS S) = EquivalenceConstitution.
Proof. intros. reflexivity. Qed.

(** ★ The criterion's level-witness BECOMES the E/R/R P1-grading. *)
Lemma bridge_grading : forall L (S : System L) (e : get_Elements (system_to_FS S)),
  fs_element_level (system_to_FS S) e = crit_level_witness L (sys_criterion L S).
Proof. intros. reflexivity. Qed.

(** ★★ The criterion's P2 (witness << L) becomes the E/R/R P1-grading VALIDITY: every element of the
    image is graded below L.  So P2 (criterion precedes system) is carried into P1 (hierarchy). *)
Lemma bridge_grading_valid : forall L (S : System L) (e : get_Elements (system_to_FS S)),
  fs_element_level (system_to_FS S) e << L.
Proof. intros L S e. exact (crit_level_valid L (sys_criterion L S)). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE BRIDGE (closes §9.1): every indexed criterion-System L embeds into an E/R/R
    FunctionalSystem L — Elements = members, Roles = discrete equality, Rules = equivalence, and the
    criterion's P2 level-witness becomes the E/R/R P1-grading (valid below L).  An embedding (the
    E/R/R image is richer; position-bound/uniqueness are residue), not an isomorphism — but the two
    "system" notions are now related by a structure-respecting map. *)
Theorem err_system_bridge : forall L (S : System L),
  get_Elements (system_to_FS S) = sig (crit_predicate L (sys_criterion L S))
  /\ get_Roles (system_to_FS S) = @eq (sig (crit_predicate L (sys_criterion L S)))
  /\ fs_constitution (system_to_FS S) = EquivalenceConstitution
  /\ (forall e : get_Elements (system_to_FS S), fs_element_level (system_to_FS S) e << L).
Proof.
  intros L S.
  split; [ exact (bridge_elements L S) | ].
  split; [ exact (bridge_roles L S) | ].
  split; [ exact (bridge_rules L S) | exact (bridge_grading_valid L S) ].
Qed.

Print Assumptions err_system_bridge.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  6 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The bridge System L -> FunctionalSystem L (closes свод §9.1: the two       *)
(*  "system" notions were unmerged).  system_to_FS sends a criterion-System to *)
(*  the E/R/R system on its MEMBERS, with Roles = discrete equality, Rules =   *)
(*  equivalence, and the criterion's P2 level-witness -> the E/R/R P1-grading   *)
(*  (bridge_elements/roles/rules/grading/grading_valid).  Capstone             *)
(*  err_system_bridge.  HONEST: an EMBEDDING, not an isomorphism — the         *)
(*  criterion-System is thinner (no native Roles/Rules; pos_bound/uniqueness   *)
(*  dropped), the E/R/R image is richer.  Two notions now related by a map.    *)
(* ========================================================================= *)
