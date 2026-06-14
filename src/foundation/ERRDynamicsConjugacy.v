(** * ERRDynamicsConjugacy.v — deepening the dynamics (thread ②, further): CONJUGACY — when are two
      dynamics "the same up to a relabeling"?

    ERRDynamics/Arrow/GroupBasin developed a single dynamics.  This file relates DIFFERENT dynamics:
    two are CONJUGATE if a bijective relabeling of states intertwines their step.  Conjugacy is the
    dynamical notion of "same system, different names".

      ★ conjugacy φ ψ f f' — a state-bijection (φ with inverse ψ) that INTERTWINES the step:
        φ (f x) = f' (φ x).  Conjugate f f' = such a relabeling exists.
      ★ Conjugacy is an EQUIVALENCE RELATION (Conjugate_refl / _sym / _trans) — "sameness of dynamics".
      ★ It PRESERVES orbit structure: the whole evolution intertwines (conjugacy_evolve), equilibria
        map to equilibria (conjugacy_preserves_equilibrium), periods are preserved
        (conjugacy_preserves_period).  These are conjugacy INVARIANTS.
      ★ NOT all dynamics are conjugate — flip (no fixed point) is NOT conjugate to collapse (which has
        the fixed point `true`): a genuine invariant ("has an equilibrium") separates them
        (flip_not_conjugate_collapse).  So "sameness" is a real, non-trivial classification.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      two dynamics are THE SAME iff a bijective state-relabeling INTERTWINES their step; this sameness
      is an EQUIVALENCE relation and preserves all orbit structure (equilibria, periods, evolution);
      distinct invariants ⇒ NON-conjugate.
    Roles (L4): conjugacy (the relabeling + intertwining); Conjugate (the relation); the invariant-
      preservation lemmas; flip_not_conjugate_collapse (the separation).
    Elements (L1+P4): the states; the relabeling maps φ/ψ; the dynamics.
    P4 diagnostic (could it be otherwise?):
      the relabeling is a CONTINGENT bijection; whether two dynamics are conjugate is DECIDED by their
      invariants — flip and collapse CANNOT be relabeled into each other (collapse has a fixed point,
      flip has none).  So sameness is a genuine classification, not "everything is the same".
    Honesty wall:
      SET-conjugacy = a state-bijection intertwining the step (NOT topological — no continuity; and NOT
      the full E/R/R-iso — Roles-preservation is the natural enrichment, deliberately not required so
      that sym/trans stay light).  Invariants shown = equilibria / periods (the orbit structure);
      the separation uses "has a fixed point"; ONE concrete non-conjugate pair (not a classification
      theorem).  Reuses ERRDynamics (evolve/equilibrium/collapse) + ERRDynamicsArrow (flip).  0 axioms.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* err_map *)
From ToS Require Import foundation.ERRDynamics.       (* InsideOperator, evolve, equilibrium, collapse *)
From ToS Require Import foundation.ERRDynamicsArrow.  (* flip *)

(* ===================================================================== *)
(*  CONJUGACY — a state-relabeling that intertwines the step              *)
(* ===================================================================== *)

(** A conjugacy from f to f': a bijection (φ, ψ) of state spaces intertwining the dynamics. *)
Definition conjugacy {L} {S S' : FunctionalSystem L}
  (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
  (f : InsideOperator S) (f' : InsideOperator S') : Prop :=
  (forall x, psi (phi x) = x)
  /\ (forall y, phi (psi y) = y)
  /\ (forall x, phi (err_map f x) = err_map f' (phi x)).

(** Two dynamics are CONJUGATE if some relabeling intertwines them. *)
Definition Conjugate {L} {S S' : FunctionalSystem L}
  (f : InsideOperator S) (f' : InsideOperator S') : Prop :=
  exists phi psi, conjugacy phi psi f f'.

(* ===================================================================== *)
(*  CONJUGACY PRESERVES ORBIT STRUCTURE (the invariants)                  *)
(* ===================================================================== *)

(** ★★ The whole evolution intertwines: φ maps the f-trajectory to the f'-trajectory. *)
Lemma conjugacy_evolve : forall {L} {S S' : FunctionalSystem L}
  (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
  (f : InsideOperator S) (f' : InsideOperator S'),
  conjugacy phi psi f f' -> forall n x, phi (evolve f x n) = evolve f' (phi x) n.
Proof.
  intros L S S' phi psi f f' Hc. destruct Hc as [_ [_ Hint]].
  intro n. induction n as [|k IH]; intro x.
  - reflexivity.
  - change (evolve f x (Datatypes.S k)) with (err_map f (evolve f x k)).
    change (evolve f' (phi x) (Datatypes.S k)) with (err_map f' (evolve f' (phi x) k)).
    rewrite Hint, IH. reflexivity.
Qed.

(** ★★ An equilibrium maps to an equilibrium under the relabeling. *)
Lemma conjugacy_preserves_equilibrium : forall {L} {S S' : FunctionalSystem L}
  (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
  (f : InsideOperator S) (f' : InsideOperator S') (x : get_Elements S),
  conjugacy phi psi f f' -> equilibrium f x -> equilibrium f' (phi x).
Proof.
  intros L S S' phi psi f f' x Hc Heq. destruct Hc as [_ [_ Hint]].
  unfold equilibrium in *. rewrite <- Hint, Heq. reflexivity.
Qed.

(** ★★ A period is preserved: if x returns after p steps, so does φ x. *)
Lemma conjugacy_preserves_period : forall {L} {S S' : FunctionalSystem L}
  (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
  (f : InsideOperator S) (f' : InsideOperator S') (x : get_Elements S) (p : nat),
  conjugacy phi psi f f' -> evolve f x p = x -> evolve f' (phi x) p = phi x.
Proof.
  intros L S S' phi psi f f' x p Hc Hper.
  pose proof (conjugacy_evolve phi psi f f' Hc p x) as Hev.
  rewrite Hper in Hev. symmetry. exact Hev.
Qed.

(* ===================================================================== *)
(*  CONJUGACY IS AN EQUIVALENCE RELATION                                   *)
(* ===================================================================== *)

(** ★ Reflexive: every dynamics is conjugate to itself (identity relabeling). *)
Lemma Conjugate_refl : forall {L} {S : FunctionalSystem L} (f : InsideOperator S), Conjugate f f.
Proof.
  intros L S f. exists (fun x => x), (fun x => x).
  repeat split; intros; reflexivity.
Qed.

(** ★★ Symmetric: the inverse relabeling intertwines the dynamics the other way. *)
Lemma Conjugate_sym : forall {L} {S S' : FunctionalSystem L}
  (f : InsideOperator S) (f' : InsideOperator S'),
  Conjugate f f' -> Conjugate f' f.
Proof.
  intros L S S' f f' [phi [psi [Hpf [Hfp Hint]]]].
  exists psi, phi. split; [ exact Hfp | split; [ exact Hpf | ] ].
  intro y.
  assert (H1 : err_map f (psi y) = psi (err_map f' y)).
  { rewrite <- (Hpf (err_map f (psi y))). rewrite Hint, Hfp. reflexivity. }
  symmetry. exact H1.
Qed.

(** ★★ Transitive: relabelings compose. *)
Lemma Conjugate_trans : forall {L} {S S' S'' : FunctionalSystem L}
  (f : InsideOperator S) (f' : InsideOperator S') (f'' : InsideOperator S''),
  Conjugate f f' -> Conjugate f' f'' -> Conjugate f f''.
Proof.
  intros L S S' S'' f f' f'' [p1 [q1 [Ha [Hb Hc]]]] [p2 [q2 [Hd [He Hf]]]].
  exists (fun x => p2 (p1 x)), (fun z => q1 (q2 z)). split; [ | split ].
  - intro x. rewrite Hd, Ha. reflexivity.
  - intro z. rewrite Hb, He. reflexivity.
  - intro x. rewrite Hc, Hf. reflexivity.
Qed.

(* ===================================================================== *)
(*  A SEPARATION — not all dynamics are conjugate                          *)
(* ===================================================================== *)

(** flip has NO fixed point (an involution fixes nothing on bool). *)
Lemma flip_no_fixed_point : forall x, ~ equilibrium flip x.
Proof.
  intros x H. unfold equilibrium in H. cbn [err_map] in H. destruct x; discriminate H.
Qed.

(** collapse HAS a fixed point: `true`. *)
Lemma collapse_has_fixed_point : equilibrium collapse true.
Proof. unfold equilibrium. reflexivity. Qed.

(** ★★★ flip is NOT conjugate to collapse: "has an equilibrium" is a conjugacy invariant, and collapse
    has one while flip has none.  Sameness of dynamics is a genuine, non-trivial classification. *)
Lemma flip_not_conjugate_collapse : ~ Conjugate flip collapse.
Proof.
  intro H. apply Conjugate_sym in H. destruct H as [phi [psi Hc]].
  exact (flip_no_fixed_point (phi true)
           (conjugacy_preserves_equilibrium phi psi collapse flip true Hc collapse_has_fixed_point)).
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ CONJUGACY — sameness of dynamics:
      (equivalence)  Conjugate is reflexive, symmetric, transitive;
      (invariant)    a conjugacy carries equilibria to equilibria (orbit structure preserved);
      (separation)   flip is NOT conjugate to collapse — a genuine invariant tells them apart.
    "Same dynamics up to a relabeling" is an equivalence that preserves orbit structure and genuinely
    classifies (not everything is the same). *)
Theorem err_dynamics_conjugacy :
  (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S), Conjugate f f)
  /\ (forall (L : Level) (S S' : FunctionalSystem L) (f : InsideOperator S) (f' : InsideOperator S'),
        Conjugate f f' -> Conjugate f' f)
  /\ (forall (L : Level) (S S' S'' : FunctionalSystem L)
            (f : InsideOperator S) (f' : InsideOperator S') (f'' : InsideOperator S''),
        Conjugate f f' -> Conjugate f' f'' -> Conjugate f f'')
  /\ (forall (L : Level) (S S' : FunctionalSystem L)
            (phi : get_Elements S -> get_Elements S') (psi : get_Elements S' -> get_Elements S)
            (f : InsideOperator S) (f' : InsideOperator S') (x : get_Elements S),
        conjugacy phi psi f f' -> equilibrium f x -> equilibrium f' (phi x))
  /\ ~ Conjugate flip collapse.
Proof.
  split; [ exact @Conjugate_refl | ].
  split; [ exact @Conjugate_sym | ].
  split; [ exact @Conjugate_trans | ].
  split; [ exact @conjugacy_preserves_equilibrium | exact flip_not_conjugate_collapse ].
Qed.

Print Assumptions err_dynamics_conjugacy.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  10 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Deepens ERRDynamics (thread ②): CONJUGACY = sameness of dynamics up to a   *)
(*  state-relabeling.  conjugacy (φ,ψ bijection intertwining the step),        *)
(*  Conjugate (the relation).  EQUIVALENCE: Conjugate_refl/_sym/_trans.        *)
(*  INVARIANTS: conjugacy_evolve (whole evolution intertwines),                *)
(*  conjugacy_preserves_equilibrium, conjugacy_preserves_period.  SEPARATION:  *)
(*  flip_no_fixed_point + collapse_has_fixed_point => flip_not_conjugate_      *)
(*  collapse (a genuine invariant tells them apart).  Capstone                 *)
(*  err_dynamics_conjugacy.  HONEST: set-conjugacy (state bijection + step-    *)
(*  intertwine), not topological (no continuity) nor full E/R/R-iso (Roles-    *)
(*  preservation = the natural enrichment, omitted to keep sym/trans light);   *)
(*  invariants = orbit structure; one concrete non-conjugate pair.            *)
(* ========================================================================= *)
