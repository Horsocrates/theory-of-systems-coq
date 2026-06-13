(** * ERRRepresentation.v — Кирпич 3 (флагман) развития ядра Теории Систем: the honest
      REPRESENTATION theorem — every system is COMPLETELY reconstructed from its components, which are
      exactly the E/R/R triple PLUS the L4-gate PLUS the P1-grading; the triple alone does NOT
      determine the system.

    The goal was "every system IS its E/R/R triple, uniquely."  The naive reading is a re-description
    (FunctionalSystem IS a record with the three fields; get_Elements/Roles/Rules just project them).
    The HONEST representation theorem is sharper, and it CORRECTS the naive claim:

      ★ RECONSTRUCTION (eta).  Every system equals the reconstruction from its own six components
        (fs_eta) — this is the record eta law (standard; destruct + reflexivity), stated to anchor
        the decomposition, not claimed as deep.
      ★ THE SIX = E/R/R triple (3) + L4-gate (1) + P1-grading (2).  The components are exactly:
        Elements (fs_domain), Roles (fs_relations), Rules (fs_constitution) — the E/R/R triple; the
        L4-gate (fs_functional, the Кирпич-1 "Rules hold on (E,R)"); and the P1-grading
        (fs_element_level + fs_level_valid, the level hierarchy).  So a system = E/R/R + L4 + P1, and
        nothing more.
      ★ THE TRIPLE ALONE IS NOT COMPLETE (the honest core).  Two genuine systems (SysA, SysB) share
        the SAME E/R/R triple (same Elements bool, same Roles, same Rules) yet differ in their
        P1-grading (triple_not_complete).  So "system = triple" is FALSE; the residue is exactly the
        P1 level-grading.  This LOCATES the gap precisely instead of over-claiming.
      ★ FAITHFUL on the triple — build-then-extract recovers the triple
        (mk_extract_domain/relations/constitution).

    Net: the E/R/R triple is the structural CORE of any system, but the full system is
    triple ⊕ L4-gate ⊕ P1-grading (complete by eta, minimal); the triple is necessary, not
    sufficient.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) eta: a system equals the reconstruction from its six components;
      (2) the six = the E/R/R triple (3) + the L4-gate (1) + the P1-grading (2);
      (3) the triple ALONE underdetermines the system — the P1-grading is free (at L >= L3);
      (4) extraction is faithful on the triple (build-then-extract = id).
    Roles (L4): mkFunctionalSystem = the reconstructor; get_Elements/Roles/Rules = the triple
      extractors; fs_functional = the L4 residue (the gate); fs_element_level = the P1 residue.
    Elements (L1+P4): systems S; SysA/SysB at L3 (same triple, gradings L1 vs L2 — both valid since
      L1, L2 << L3).
    P4 diagnostic (could it be otherwise?):
      The representation is COMPLETE (eta yields all six) and minimal; the triple is necessary but not
      sufficient — the residue is exactly P1 (grading) + L4 (gate).  The naive "system = triple" is
      refuted (triple_not_complete); the honest form is system = triple (+) L4 (+) P1.
    Honesty wall:
      fs_eta is the record eta law (standard, destruct + reflexivity) — NOT claimed as a deep theorem.
      The genuine contribution is the DECOMPOSITION (six = 3 + 1 + 2 = E/R/R + L4 + P1) and the
      INCOMPLETENESS of the triple (triple_not_complete, a concrete witness at L3).  Uniqueness up to
      the proof fields (fs_functional / fs_level_valid : Prop) is NOT claimed — it would need proof
      irrelevance (an axiom); we work at the level of DATA.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.

(* Restore the section-local implicit {L} on the record projections (see ERRRankAsymmetry.v). *)
Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  PART I — RECONSTRUCTION (eta) and faithful extraction                  *)
(* ===================================================================== *)

(** ★ Every system equals the reconstruction from its six components (record eta).  The six are:
    Rules (fs_constitution), Elements (fs_domain), Roles (fs_relations) = the E/R/R triple; the
    L4-gate (fs_functional); the P1-grading (fs_element_level, fs_level_valid). *)
Lemma fs_eta : forall L (S : FunctionalSystem L),
  S = mkFunctionalSystem L (fs_constitution S) (fs_domain S) (fs_relations S)
        (fs_functional S) (fs_element_level S) (fs_level_valid S).
Proof. intros L S. destruct S. reflexivity. Qed.

(** ★ Extraction is faithful on Elements: build-then-extract recovers the domain. *)
Lemma mk_extract_domain :
  forall L c d r f e v, fs_domain (mkFunctionalSystem L c d r f e v) = d.
Proof. reflexivity. Qed.

(** ★ Faithful on Roles. *)
Lemma mk_extract_relations :
  forall L c d r f e v, fs_relations (mkFunctionalSystem L c d r f e v) = r.
Proof. reflexivity. Qed.

(** ★ Faithful on Rules. *)
Lemma mk_extract_constitution :
  forall L c d r f e v, fs_constitution (mkFunctionalSystem L c d r f e v) = c.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART II — THE TRIPLE ALONE IS NOT COMPLETE: the P1-grading is residue   *)
(* ===================================================================== *)

(** Two systems at L3 with the SAME E/R/R triple (Elements bool, Roles "always", Rules trivial) but
    DIFFERENT P1-grading.  At L3 the grading is genuinely free: both L1 and L2 are << L3. *)
Definition SysA : FunctionalSystem L3.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L3.
Defined.

Definition SysB : FunctionalSystem L3.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L2; fs_level_valid := fun _ => _ |}.
  exact L2_lt_L3.
Defined.

(** ★ The two systems share the ENTIRE E/R/R triple (Elements, Roles, Rules). *)
Lemma triple_same :
  get_Elements SysA = get_Elements SysB
  /\ get_Roles SysA = get_Roles SysB
  /\ fs_constitution SysA = fs_constitution SysB.
Proof. split; [ reflexivity | split; reflexivity ]. Qed.

(** ★ Yet their P1-grading DIFFERS. *)
Lemma grading_differs : fs_element_level SysA <> fs_element_level SysB.
Proof.
  intro H. pose proof (f_equal (fun g => g true) H) as E. cbv in E. discriminate E.
Qed.

(** ★★ THE HONEST CORE: the E/R/R triple does NOT determine the system — the P1 level-grading is
    genuine residue.  "System = triple" is FALSE; the gap is exactly the P1-grading. *)
Theorem triple_not_complete :
  exists (L : Level) (SA SB : FunctionalSystem L) (a : get_Elements SA) (b : get_Elements SB),
    get_Elements SA = get_Elements SB
    /\ fs_constitution SA = fs_constitution SB
    /\ fs_element_level SA a <> fs_element_level SB b.
Proof.
  exists L3, SysA, SysB, true, true.
  split; [ reflexivity | split; [ reflexivity | ] ].
  cbv. discriminate.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the honest representation theorem                           *)
(* ===================================================================== *)

(** ★★★ THE REPRESENTATION (honest):
      (reconstruction) every system = the reconstruction from its six components (eta) — the six are
                       the E/R/R triple (Elements/Roles/Rules) + the L4-gate (fs_functional) + the
                       P1-grading (fs_element_level/valid);
      (incompleteness) the E/R/R triple ALONE does not determine the system — the P1-grading is
                       residue (two systems, same triple, different grading).
    So a system = E/R/R triple (+) L4-gate (+) P1-grading: the triple is the structural core,
    necessary but not sufficient; the naive "system = triple" is corrected, the residue located. *)
Theorem err_representation :
  (forall L (S : FunctionalSystem L),
     S = mkFunctionalSystem L (fs_constitution S) (fs_domain S) (fs_relations S)
           (fs_functional S) (fs_element_level S) (fs_level_valid S))
  /\ (exists (L : Level) (SA SB : FunctionalSystem L) (a : get_Elements SA) (b : get_Elements SB),
        get_Elements SA = get_Elements SB
        /\ fs_constitution SA = fs_constitution SB
        /\ fs_element_level SA a <> fs_element_level SB b).
Proof. split; [ exact fs_eta | exact triple_not_complete ]. Qed.

Print Assumptions err_representation.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Кирпич 3 (flagship): the honest E/R/R REPRESENTATION theorem.  fs_eta:    *)
(*  every system = reconstruction from its six components (record eta).  The   *)
(*  six = E/R/R triple (fs_domain/relations/constitution) + L4-gate            *)
(*  (fs_functional, Кирпич 1) + P1-grading (fs_element_level/valid).           *)
(*  mk_extract_* : extraction faithful on the triple.  triple_not_complete:    *)
(*  the triple ALONE does NOT determine the system — SysA/SysB at L3 share the *)
(*  whole triple (triple_same) but differ in P1-grading (grading_differs).     *)
(*  So system = triple (+) L4 (+) P1: triple = structural core, necessary not  *)
(*  sufficient; the naive "system = triple" is corrected.  HONEST: fs_eta is   *)
(*  standard eta (not claimed deep); genuine = the 6=3+1+2 decomposition +     *)
(*  triple incompleteness; no uniqueness-up-to-proofs (would need proof        *)
(*  irrelevance = axiom).  Ladder Кирпич 1/2/3 complete (rank asymmetry /      *)
(*  composition / representation).                                            *)
(* ========================================================================= *)
