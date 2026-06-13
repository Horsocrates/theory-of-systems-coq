(** * ERRIrreducible.v — остаток: the E/R/R triad is IRREDUCIBLE — three independent degrees of
      freedom; no aspect is determined by the other two (formalizes the paper's "three aspects, none
      omittable").

    The E/R/R paper claims the three aspects are inseparable ("one cannot have a distinction without
    all three").  The formal shadow of "none omittable" is INDEPENDENCE: each aspect can vary while
    the other two are held fixed, so no aspect is a function of the other two — the triad has three
    genuine degrees of freedom and cannot be reduced to two.

      ★ rules_independent    : Elements & Roles fixed, Rules differ (reuses Кирпич 1's BoolEq systems);
      ★ roles_independent    : Elements & Rules fixed, Roles differ (eq vs the full relation);
      ★ elements_independent : Rules fixed, Elements differ (unit vs bool — a different TYPE).

    Together: the three vary independently, so the triad is irreducible.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) Rules vary with Elements & Roles fixed; (2) Roles vary with Elements & Rules fixed;
      (3) Elements vary with Rules fixed; (4) hence the triad has 3 independent DOF — irreducible.
    Roles (L4): three witness-pairs of systems, each fixing two aspects and varying the third.
    Elements (L1+P4): the domains bool / unit; the relations eq / the full relation; the
      constitutions Trivial / Equivalence.
    P4 diagnostic (could it be otherwise?):
      "none omittable" is formalized as independence: each aspect varies under the other two fixed, so
      none is determined by the others.  Elements-variation is shown by a CHANGE OF TYPE (unit /= bool).
    Honesty wall:
      "irreducible" here = three independent degrees of freedom, NOT the philosophical "a distinction
      logically requires all three".  The witnesses are concrete (so the types align); a generic
      existential over abstract systems would be heterogeneous (get_Roles depends on get_Elements).
      0 axioms.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRRankAsymmetry.  (* BoolEqTrivial, BoolEqEquiv, same_elements, same_roles, different_rules *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* Two more witnesses (BoolEqTrivial = (bool, eq, Trivial) is reused from Кирпич 1). *)

(** Same Elements (bool) and same Rules (Trivial) as BoolEqTrivial, but Roles = the full relation. *)
Definition S_full : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** Same Rules (Trivial) as BoolEqTrivial, but Elements = unit (a different TYPE). *)
Definition S_unit : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := unit;
            fs_relations := (@eq unit); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(* ===================================================================== *)
(*  THE THREE INDEPENDENCES                                                *)
(* ===================================================================== *)

(** ★ RULES vary independently: Elements & Roles fixed, Rules differ (Кирпич 1). *)
Lemma rules_independent :
  get_Elements BoolEqTrivial = get_Elements BoolEqEquiv
  /\ get_Roles BoolEqTrivial = get_Roles BoolEqEquiv
  /\ fs_constitution BoolEqTrivial <> fs_constitution BoolEqEquiv.
Proof. split; [ exact same_elements | split; [ exact same_roles | exact different_rules ] ]. Qed.

(** ★ ROLES vary independently: Elements (bool) & Rules (Trivial) fixed, Roles differ (eq vs the full
    relation — they disagree at (false,true)). *)
Lemma roles_independent :
  get_Elements BoolEqTrivial = get_Elements S_full
  /\ fs_constitution BoolEqTrivial = fs_constitution S_full
  /\ get_Roles BoolEqTrivial <> get_Roles S_full.
Proof.
  split; [ reflexivity | split; [ reflexivity | ] ].
  intro H. pose proof (f_equal (fun R : bool -> bool -> Prop => R false true) H) as E.
  cbn in E. assert (Hft : false = true) by (rewrite E; exact I). discriminate Hft.
Qed.

(** ★ ELEMENTS vary independently: Rules (Trivial) fixed, Elements differ — unit vs bool, a different
    TYPE (unit is a subsingleton, bool is not). *)
Lemma elements_independent :
  fs_constitution S_unit = fs_constitution BoolEqTrivial
  /\ get_Elements S_unit <> get_Elements BoolEqTrivial.
Proof.
  split; [ reflexivity | ].
  intro H.
  assert (Hb : exists a b : get_Elements BoolEqTrivial, a <> b).
  { exists true, false. discriminate. }
  rewrite <- H in Hb.
  destruct Hb as [a [b Hab]]. destruct a, b. apply Hab. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The E/R/R triad is IRREDUCIBLE: each aspect varies while the other two are fixed —
      (Rules)    Elements & Roles fixed, Rules differ;
      (Roles)    Elements & Rules fixed, Roles differ;
      (Elements) Rules fixed, Elements differ (a different type).
    Three independent degrees of freedom; no aspect is determined by the other two; "none omittable"
    made precise. *)
Theorem err_triad_irreducible :
  (get_Elements BoolEqTrivial = get_Elements BoolEqEquiv
     /\ get_Roles BoolEqTrivial = get_Roles BoolEqEquiv
     /\ fs_constitution BoolEqTrivial <> fs_constitution BoolEqEquiv)
  /\ (get_Elements BoolEqTrivial = get_Elements S_full
     /\ fs_constitution BoolEqTrivial = fs_constitution S_full
     /\ get_Roles BoolEqTrivial <> get_Roles S_full)
  /\ (fs_constitution S_unit = fs_constitution BoolEqTrivial
     /\ get_Elements S_unit <> get_Elements BoolEqTrivial).
Proof.
  split; [ exact rules_independent | ].
  split; [ exact roles_independent | exact elements_independent ].
Qed.

Print Assumptions err_triad_irreducible.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  4 Qed, 0 Admitted, 0 axioms.                                             *)
(*  The E/R/R triad is IRREDUCIBLE — three independent degrees of freedom:    *)
(*  rules_independent (Кирпич 1 BoolEq systems), roles_independent (eq vs full        *)
(*  relation), elements_independent (unit vs bool, a different type).  Each    *)
(*  aspect varies with the other two fixed, so none is a function of the       *)
(*  others.  Capstone err_triad_irreducible.  Formalizes the paper claim three *)
(*  aspects none omittable as independence (3 DOF).  HONEST: independence,     *)
(*  not logical necessity; concrete witnesses (types aligned).                *)
(* ========================================================================= *)
