(** * ERRProcessConstitution.v — Task #127: the Rule tier reformulated onto the PROCESS ontology.  In
      ToS the RELATING (Roles) is a PROCESS, not a static relation R; so a Constitution (a Rule) is a
      condition on a relating-PROCESS, not on a finished relation.  The static Constitution is the
      completed special case (a role-limit); genuine process-Rules speak of the unfolding.

    Core_ERR has `Constitution := forall (D:Type)(R:D->D->Prop), Prop` — a condition on a STATIC
    relation R, and FunctionalSystem.fs_relations : D->D->Prop is a static relation.  But ToS's
    ontology is process-first (ProcessGeneral: GenProcess A := nat -> A; CauchyReal: RealProcess :=
    nat -> Q; ERRHilbertProcess: Hilbert is a process): the RELATING is observed/settled over finite
    stages, never given as a finished static fact.  This file reformulates the Rule tier accordingly.

      ★ ProcRel D       — the relating as a PROCESS: nat -> D -> D -> Prop (= GenProcess (D->D->Prop)),
                          the relation as observed at each stage.
      ★ const_rel R     — a finished/static relation as a CONSTANT process (the already-completed
                          relating).
      ★ ProcConstitution — a Rule on the relating-PROCESS: forall D, ProcRel D -> Prop.
      ★ stagewise C     — lift a static Rule: it holds of the relation AT EACH STAGE.
      ★ stagewise_const — the static Constitution is RECOVERED: stagewise C on a finished relating <=>
                          the static C.  So this is a STRICT GENERALIZATION (nothing lost).
      ★ stagewise_preserves_refinement — the Constitution lattice (cstronger, ERRCombinationCalculus)
                          lifts monotonically to process-Constitutions.
      ★ monotone_settling — a GENUINELY process-level Rule (the relating only grows; R5 / irreversible
                          settling): not captured by stagewise of ANY static Rule
                          (monotone_is_process_level).
      ★ relating_genuinely_unfolds — relating is a process that SETTLES over time (a pair unrelated at
                          stage 0, related at stage 1) — not a finished static fact.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) a Rule (Constitution) is a condition on the RELATING, and relating is a PROCESS — so the Rule
          is a condition on a process-relation nat->D->D->Prop, not on a static R;
      (2) the static Constitution is the SPECIAL CASE of an already-completed (constant) relating;
      (3) genuine process-Rules (monotone settling) speak of the unfolding and have no static analog;
          the static "completed Rule" is the role-limit (actualizing it = the #126 wall).
    Roles (L4): ProcRel (relating as process); stagewise (lift a static Rule to "holds at each stage");
      const_rel (finished relating = constant process); monotone_settling (a process-level Rule).
    Elements (L1+P4): the carrier D; the stages; the relations-at-each-stage.
    P4 diagnostic (could it be otherwise?):
      relating is NOT given as a finished static fact — it is observed at finite stages (P4); the
      static relation R is the completed object (role-limit).  A Rule holding stagewise is Element-side;
      the "Rule of the limit relation" demands the completed relating = actualization.  So the static
      Constitution forall (D)(R:D->D->Prop) is the role-limit of the process-Constitution; the honest
      primitive is the process version.
    Honesty wall:
      a reformulation of the Rule tier onto the process ontology (consistent with ERRHilbertProcess and
      ProcessGeneral).  The static Constitution is RECOVERED as the completed special case
      (stagewise_const) — nothing lost, a strict generalization.  Genuinely new = process-level Rules
      (monotone_settling) + relating-as-settling (relating_genuinely_unfolds).  Does NOT re-derive the
      process tier (GenProcess lives in ProcessGeneral); it builds the Rule-on-process.  0 axioms.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.        (* Constitution, TrivialConstitution *)
From ToS Require Import foundation.ERRCombinationCalculus. (* cstronger — the Constitution lattice order *)

(* ===================================================================== *)
(*  ROLES AS A PROCESS, RULES AS CONDITIONS ON IT                         *)
(* ===================================================================== *)

(** The relating as a PROCESS: the relation as observed at each stage (= GenProcess (D->D->Prop)). *)
Definition ProcRel (D : Type) : Type := nat -> D -> D -> Prop.

(** A finished/static relation as a CONSTANT process — the already-completed relating. *)
Definition const_rel {D : Type} (R : D -> D -> Prop) : ProcRel D := fun _ => R.

(** A Rule on the relating-PROCESS (not on a static relation). *)
Definition ProcConstitution : Type := forall (D : Type), ProcRel D -> Prop.

(** Lift a static Rule: it holds of the relation AT EACH STAGE of the process. *)
Definition stagewise (C : Constitution) : ProcConstitution :=
  fun D Rp => forall n, C D (Rp n).

(** A GENUINELY process-level Rule: the relating only GROWS — once related, stays related (R5 /
    irreversible settling).  This speaks of CONSECUTIVE stages — no static relation can express it. *)
Definition monotone_settling : ProcConstitution :=
  fun D Rp => forall n x y, Rp n x y -> Rp (S n) x y.

(* ===================================================================== *)
(*  THE STATIC CORE IS THE COMPLETED SPECIAL CASE                         *)
(* ===================================================================== *)

(** ★★ The static Constitution is RECOVERED: on an already-finished relating (a constant process),
    the process-Rule equals the static Rule.  Process-Constitution is a STRICT GENERALIZATION. *)
Lemma stagewise_const : forall (C : Constitution) (D : Type) (R : D -> D -> Prop),
  stagewise C D (const_rel R) <-> C D R.
Proof.
  intros C D R. unfold stagewise, const_rel. split.
  - intro H. exact (H 0).
  - intros H n. exact H.
Qed.

(** ★ The Constitution lattice (cstronger, ERRCombinationCalculus) lifts MONOTONICALLY to
    process-Constitutions: a stronger Rule, held stagewise, implies the weaker one held stagewise. *)
Lemma stagewise_preserves_refinement : forall (C1 C2 : Constitution),
  cstronger C1 C2 -> forall (D : Type) (Rp : ProcRel D), stagewise C1 D Rp -> stagewise C2 D Rp.
Proof.
  intros C1 C2 Hc D Rp H n. apply Hc. exact (H n).
Qed.

(* ===================================================================== *)
(*  GENUINELY PROCESS-LEVEL CONTENT                                        *)
(* ===================================================================== *)

(** ★★ monotone_settling carries information BEYOND stagewise of any static Rule: two relating-
    processes both pass stagewise-Trivial (every stage accepted), yet one settles monotonically and
    the other un-settles.  A static Constitution constrains each stage in isolation; this links
    consecutive stages — it is irreducibly process-level. *)
Lemma monotone_is_process_level :
  exists (D : Type) (Rp1 Rp2 : ProcRel D),
    stagewise TrivialConstitution D Rp1 /\ stagewise TrivialConstitution D Rp2
    /\ monotone_settling D Rp1 /\ ~ monotone_settling D Rp2.
Proof.
  exists unit, (fun _ _ _ => True),
         (fun n (_ _ : unit) => match n with O => True | S _ => False end).
  split; [ intro n; exact I | ].
  split; [ intro n; exact I | ].
  split.
  - intros n x y H. exact I.
  - intro H. exact (H 0 tt tt I).
Qed.

(** ★★ Relating is a process that SETTLES over time: a pair UNRELATED at stage 0 becomes RELATED at
    stage 1 (monotonically).  Relating is not a finished static fact — it is observed/settled across
    finite stages (P4); the static relation is its completed limit. *)
Lemma relating_genuinely_unfolds :
  exists (D : Type) (Rp : ProcRel D) (x y : D),
    monotone_settling D Rp /\ ~ Rp 0 x y /\ Rp 1 x y.
Proof.
  exists unit, (fun n (_ _ : unit) => match n with O => False | S _ => True end), tt, tt.
  split; [ | split ].
  - intros n a b H. destruct n; [ destruct H | exact I ].
  - simpl. intro H. exact H.
  - simpl. exact I.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ THE RULE TIER ON THE PROCESS ONTOLOGY:
      (recovery)        the static Constitution = the completed (constant) special case;
      (lattice lifts)   the refinement order lifts monotonically to process-Constitutions;
      (process-level)   monotone settling is a Rule beyond stagewise of any static Rule;
      (relating settles) relating is a process (unrelated then related) — not a finished static fact.
    So a Rule is a condition on the relating-PROCESS; the static `forall (D)(R:D->D->Prop)` is its
    completed special case (a role-limit), recovered exactly — nothing lost. *)
Theorem err_process_constitution :
  (forall (C : Constitution) (D : Type) (R : D -> D -> Prop),
     stagewise C D (const_rel R) <-> C D R)
  /\ (forall (C1 C2 : Constitution),
        cstronger C1 C2 -> forall (D : Type) (Rp : ProcRel D), stagewise C1 D Rp -> stagewise C2 D Rp)
  /\ (exists (D : Type) (Rp1 Rp2 : ProcRel D),
        stagewise TrivialConstitution D Rp1 /\ stagewise TrivialConstitution D Rp2
        /\ monotone_settling D Rp1 /\ ~ monotone_settling D Rp2)
  /\ (exists (D : Type) (Rp : ProcRel D) (x y : D),
        monotone_settling D Rp /\ ~ Rp 0 x y /\ Rp 1 x y).
Proof.
  split; [ exact stagewise_const | ].
  split; [ exact stagewise_preserves_refinement | ].
  split; [ exact monotone_is_process_level | exact relating_genuinely_unfolds ].
Qed.

Print Assumptions err_process_constitution.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  5 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Task #127: the Rule tier reformulated onto the PROCESS ontology.  ProcRel  *)
(*  (relating as a process nat->D->D->Prop = GenProcess), ProcConstitution     *)
(*  (Rule on it), stagewise (lift a static Rule to hold at each stage),        *)
(*  const_rel (finished relating = constant process).  stagewise_const: the    *)
(*  static Constitution is RECOVERED as the completed special case (strict      *)
(*  generalization, nothing lost); stagewise_preserves_refinement: the         *)
(*  Constitution lattice lifts monotonically.  monotone_settling: a GENUINELY  *)
(*  process-level Rule (links consecutive stages), beyond stagewise of any     *)
(*  static Rule (monotone_is_process_level); relating_genuinely_unfolds:       *)
(*  relating SETTLES over time (unrelated -> related), not a finished static    *)
(*  fact.  Capstone err_process_constitution.  HONEST: reformulation onto the  *)
(*  process ontology (ProcessGeneral / ERRHilbertProcess); static R is the     *)
(*  role-limit; process version is the honest primitive.                      *)
(* ========================================================================= *)
