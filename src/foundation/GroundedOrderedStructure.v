(** * GroundedOrderedStructure.v — Identity & Non-Contradiction as demands of the meta-pair (L4+L5)
    Elements: carriers U (the subjects the meta-pair governs), dependency dep x y
              ("y stands on x": x is ground AND lower level for y), descent chains,
              candidate "identities" ident.
    Roles:    dep carries BOTH meta-roles in one edge — grounding edge (L4/ЗДО) and
              order edge (L5/Порядок); well_founded dep = their JOINT demand: every
              chain of grounds is founded (L4 anti-regress) and the hierarchy stands
              on lower levels (L5). Identity (T) and Non-Contradiction (N) play the
              role of DERIVED DEMANDS on the subjects — theorems, not postulates.
    Rules:    single premise: well-foundedness of dep.  Derived: irreflexivity
              (nothing is its own ground — the same figure as P1), asymmetry,
              acyclicity through all mediations (clos_trans), no identity across an
              edge (T: relata must stay distinct and self-same), distinct endpoints,
              finiteness of every descent.
    Status:   answers the book question (Архитектура Размышления, гл. 1, преамбула к
              пяти законам): can T+N be derived from the meta-pair ЗДО+Порядок?
              TRANSCENDENTALLY YES — as the demands the meta-pair makes on whatever
              it governs; NOT as a calculus-derivation of A=A (mutual constitution:
              to state L4+L5 one already uses determinate terms — Leibniz equality
              pre-exists in the formal framework itself; cf. HORTLO-18 §A.3.1 note,
              where L1 enters P1's proof exactly as "one determinate entity across
              its two roles").
    P4 diagnostic (could it be otherwise under the same rules?):
              (i) encoding the meta-pair as well_founded is STRONGER than bare
              strictness (irreflexive+transitive): bare strictness yields the
              N-shaped theorems but NOT finite descent; well-foundedness is the
              honest price of L4's anti-regress core — declared openly, not hidden.
              (ii) Leibniz eq pre-exists the formalism — so the file derives
              T/N-SHAPED demands on subjects, not the laws themselves from axioms.
              (iii) the compat hypothesis on ident is the DEFINITION of "an identity
              that respects the structure", not a hidden axiom.
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Relations.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Arith.
From Stdlib Require Import Wf_nat.

(* ================================================================== *)
(*  THE META-PAIR, ABSTRACTLY                                          *)
(*                                                                     *)
(*  dep x y reads: "y stands on x" — x is a ground of y (L4 edge) and  *)
(*  x lies strictly below y in the hierarchy (L5 edge). One relation,  *)
(*  two meta-roles. well_founded dep is the joint demand of the pair:  *)
(*  no chain of grounds regresses forever (L4), every level stands on  *)
(*  founded lower levels (L5).                                         *)
(* ================================================================== *)

Section MetaPair.

  Variable U : Type.
  Variable dep : U -> U -> Prop.
  Hypothesis WF : well_founded dep.

  (* ---------------------------------------------------------------- *)
  (*  N-shaped demands: exclusivity of the order positions             *)
  (* ---------------------------------------------------------------- *)

  (** ★ Nothing among the subjects is its own ground / its own lower level.
      The same figure as P1 (Hierarchy): the organizer cannot be among the
      organized in the same respect.  Non-Contradiction read on positions. *)
  Theorem no_self_ground : forall x : U, ~ dep x x.
  Proof.
    apply (well_founded_ind WF (fun x => ~ dep x x)).
    intros x IH Hxx. exact (IH x Hxx Hxx).
  Qed.

  (** ★ The two sides of an edge exclude each other: nothing stands on what
      stands on it.  Being on both sides of the boundary at once is barred. *)
  Theorem ground_asym : forall x y : U, dep x y -> ~ dep y x.
  Proof.
    apply (well_founded_ind WF (fun x => forall y, dep x y -> ~ dep y x)).
    intros x IH y Hxy Hyx. exact (IH y Hyx x Hyx Hxy).
  Qed.

  (** ★ No cycles even through arbitrarily many mediating links:
      the transitive closure of dep is irreflexive. *)
  Theorem no_mediated_cycle : forall x : U, ~ clos_trans U dep x x.
  Proof.
    pose proof (wf_clos_trans U dep WF) as WFt.
    apply (well_founded_ind WFt (fun x => ~ clos_trans U dep x x)).
    intros x IH Hxx. exact (IH x Hxx Hxx).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  T-shaped demand: stability of the relata                         *)
  (*                                                                   *)
  (*  Take ANY candidate "identity" on the subjects. The only thing we *)
  (*  ask of it is that it respect the structure: identified items     *)
  (*  bear the same dependency edges.  Then no such identity can ever  *)
  (*  relate a member to what it stands on: an A "identified" with its *)
  (*  own ground would have to stand below itself.  The relata of      *)
  (*  every edge must remain distinct and self-same across the act —   *)
  (*  Identity as a demand of the meta-pair.                           *)
  (* ---------------------------------------------------------------- *)

  Section Identity.

    Variable ident : U -> U -> Prop.
    Hypothesis ident_compat :
      forall x x' y, ident x x' -> dep x y -> dep x' y.

    (** ★ A structure-respecting identity cannot cross a dependency edge. *)
    Theorem identity_cannot_cross_edges :
      forall x y : U, dep x y -> ~ ident x y.
    Proof.
      intros x y Hdep Hid.
      exact (no_self_ground y (ident_compat x y y Hid Hdep)).
    Qed.

  End Identity.

  (** ★ Leibniz equality respects any structure — so the endpoints of every
      edge are distinct entities.  (The instance pattern: eq is the least
      structure-respecting identity, and even it cannot cross an edge.) *)
  Theorem ground_neq : forall x y : U, dep x y -> x <> y.
  Proof.
    apply (identity_cannot_cross_edges (@eq U)).
    intros a a' b Heq Hd. subst a'. exact Hd.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Finite descent (the P4 flavour of the joint demand)              *)
  (* ---------------------------------------------------------------- *)

  (** ★ No infinite descending chain of grounds/levels exists. *)
  Theorem no_infinite_descent :
    forall f : nat -> U, ~ (forall n : nat, dep (f (S n)) (f n)).
  Proof.
    intros f Hf.
    assert (H : forall x : U, forall n : nat, f n = x -> False).
    { apply (well_founded_ind WF (fun x => forall n, f n = x -> False)).
      intros x IH n Hfn.
      assert (Hd : dep (f (S n)) x) by (rewrite <- Hfn; exact (Hf n)).
      exact (IH (f (S n)) Hd (S n) eq_refl). }
    exact (H (f 0) 0 eq_refl).
  Qed.

End MetaPair.

(* ================================================================== *)
(*  SYNTHESIS — the demands of the meta-pair, bundled                  *)
(* ================================================================== *)

(** ★★★ Whatever the meta-pair governs (any well-founded grounding order)
    must satisfy: no self-grounding, asymmetry, distinct relata on every
    edge, no mediated cycles, finite descent.  T and N are not optional
    extras on top of L4+L5 — they are what L4+L5 demand of their subjects. *)
Theorem meta_pair_demands :
  forall (U : Type) (dep : U -> U -> Prop),
    well_founded dep ->
    (forall x, ~ dep x x)
    /\ (forall x y, dep x y -> ~ dep y x)
    /\ (forall x y, dep x y -> x <> y)
    /\ (forall x, ~ clos_trans U dep x x)
    /\ (forall f : nat -> U, ~ (forall n, dep (f (S n)) (f n))).
Proof.
  intros U dep WF.
  repeat split.
  - exact (no_self_ground U dep WF).
  - exact (ground_asym U dep WF).
  - exact (ground_neq U dep WF).
  - exact (no_mediated_cycle U dep WF).
  - exact (no_infinite_descent U dep WF).
Qed.

(** ★ Contrapositive display: a single loop already destroys the meta-pair.
    Where something is its own ground, there is no founded structure at all. *)
Theorem cycle_breaks_foundedness :
  forall (U : Type) (dep : U -> U -> Prop),
    (exists x, dep x x) -> ~ well_founded dep.
Proof.
  intros U dep [x Hx] WF.
  exact (no_self_ground U dep WF x Hx).
Qed.

(* ================================================================== *)
(*  INHABITATION WITNESS — the demands are satisfiable                 *)
(*                                                                     *)
(*  Levels as nat, dep = strictly-below: the canonical model of the    *)
(*  meta-pair.  All demands hold there, so they are consistent.        *)
(* ================================================================== *)

Theorem levels_no_self : forall n : nat, ~ (n < n)%nat.
Proof. exact (no_self_ground nat lt lt_wf). Qed.

Theorem levels_asym : forall m n : nat, (m < n)%nat -> ~ (n < m)%nat.
Proof. exact (ground_asym nat lt lt_wf). Qed.

Theorem levels_finite_descent :
  forall f : nat -> nat, ~ (forall n : nat, (f (S n) < f n)%nat).
Proof. exact (no_infinite_descent nat lt lt_wf). Qed.
