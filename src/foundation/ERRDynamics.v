(** * ERRDynamics.v — system DYNAMICS / evolution: a system evolves by ITERATING its own inside-
      operator.  The trajectory is a PROCESS; evolution preserves the constitution; time acts as a
      monoid; fixed points are equilibria; and evolution is generically IRREVERSIBLE (the L5 arrow).

    The E/R/R core so far is STATIC (composition, properties, emergence).  This file gives it
    DYNAMICS, tying together the operator (ERROperator #125), the process ontology
    (ERRProcessConstitution #127), and irreversibility (foundation/L5_Arrow.v).

      ★ a DYNAMICS = an inside-operator f : InsideOperator S (an endo of S); evolve f x0 n = the state
        after n steps (iterate (err_map f) n x0).
      ★ trajectory f x0 = the evolution as a PROCESS (nat -> states): a GenProcess (#127) — each step
        finite/actual (P4), the long run a role-limit.
      ★ evolution PRESERVES the constitution: related states stay related along the evolution
        (evolution_preserves_roles, from err_pres).
      ★ time is a MONOID: evolve (m+n) = evolve m after evolve n (evolve_compose).
      ★ EQUILIBRIUM = a fixed point of f; it is invariant under evolution (equilibrium_stays).
      ★ REVERSIBLE = f has a two-sided inverse operator; generically FALSE — a collapsing dynamics
        loses distinctions irreversibly (collapse_irreversible), the formal shadow of the L5 arrow.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      a system EVOLVES by iterating its own inside-operator; the trajectory is a PROCESS (P4: each step
      finite/actual, the long run a role-limit); evolution PRESERVES the constitution (Roles-preserving
      per step); time acts as a MONOID; fixed points are EQUILIBRIA (invariant); reversible iff the
      operator is invertible, else IRREVERSIBLE (the L5 arrow — a collapse cannot be unmade).
    Roles (L4): evolve / iterate (the dynamics); trajectory (the process); equilibrium (a fixed point);
      reversible (invertibility); collapse (the irreversible witness).
    Elements (L1+P4): the system S; its states; the operator.
    P4 diagnostic (could it be otherwise?):
      evolution is a PROCESS — each step is finite/actual (P4); the trajectory unfolds over time, never
      a completed object; the long run (attractor) is a role-limit.  Reversibility is NOT guaranteed —
      a collapsing dynamics irreversibly loses distinctions (L5_Arrow): the past state is not
      recoverable.  So evolution is generically one-way (the arrow of time = L5).
    Honesty wall:
      dynamics = iteration of an inside-operator (an endo-morphism); the trajectory is a DISCRETE
      process (not a continuous flow); reversibility = operator invertibility; irreversibility is
      witnessed by a concrete collapse (the L5_Arrow shadow, cited).  Equilibria = fixed points (NOT
      the analytic Banach fixed-point of FixedPoint.v — that is the metric tier).  Ties ERROperator
      (#125) + ERRProcessConstitution (#127) + L5_Arrow.  0 axioms.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, err_map, err_pres, mkERRMorphism *)

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  DYNAMICS = ITERATION OF AN INSIDE-OPERATOR                             *)
(* ===================================================================== *)

(** An inside-operator (endo of S) — the dynamics step (ERROperator #125). *)
Definition InsideOperator {L : Level} (S : FunctionalSystem L) : Type := ERRMorphism S S.

(** Function iteration. *)
Fixpoint iterate {A : Type} (g : A -> A) (n : nat) (x : A) : A :=
  match n with O => x | S k => g (iterate g k x) end.

(** The state after n steps of the dynamics f from x0. *)
Definition evolve {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x0 : get_Elements S) (n : nat) : get_Elements S := iterate (err_map f) n x0.

(** The evolution as a PROCESS (nat -> states) — a GenProcess (ERRProcessConstitution #127). *)
Definition trajectory {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x0 : get_Elements S) : nat -> get_Elements S := fun n => evolve f x0 n.

(** A state is an EQUILIBRIUM of f if the dynamics leaves it unchanged (a fixed point). *)
Definition equilibrium {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (x : get_Elements S) : Prop := err_map f x = x.

(** A dynamics is REVERSIBLE if it has a two-sided inverse operator. *)
Definition reversible {L} {S : FunctionalSystem L} (f : InsideOperator S) : Prop :=
  exists g : InsideOperator S,
    (forall x, err_map g (err_map f x) = x) /\ (forall x, err_map f (err_map g x) = x).

(* ===================================================================== *)
(*  BASIC LAWS                                                             *)
(* ===================================================================== *)

(** ★ The trajectory is a PROCESS: starts at x0, advances one step at a time. *)
Lemma trajectory_is_process : forall {L} (S : FunctionalSystem L) (f : InsideOperator S) (x0 : get_Elements S),
  trajectory f x0 0 = x0
  /\ (forall n, trajectory f x0 (Datatypes.S n) = err_map f (trajectory f x0 n)).
Proof. intros L S f x0. split; [ reflexivity | intro n; reflexivity ]. Qed.

(** ★★ Time acts as a MONOID: evolving (m+n) steps = evolving n then m. *)
Lemma evolve_compose : forall {L} (S : FunctionalSystem L) (f : InsideOperator S)
  (x0 : get_Elements S) (m n : nat),
  trajectory f x0 (m + n) = trajectory f (trajectory f x0 n) m.
Proof.
  intros L S f x0 m n. unfold trajectory, evolve. induction m as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ★★ Evolution PRESERVES the constitution: related states stay related along the evolution. *)
Lemma evolution_preserves_roles : forall {L} (S : FunctionalSystem L) (f : InsideOperator S)
  (n : nat) (x y : get_Elements S),
  get_Roles S x y -> get_Roles S (evolve f x n) (evolve f y n).
Proof.
  intros L S f n. unfold evolve. induction n as [|k IH]; intros x y H.
  - simpl. exact H.
  - simpl. apply (err_pres f). apply IH. exact H.
Qed.

(** ★★ An EQUILIBRIUM is invariant under the dynamics: it stays put at every step. *)
Lemma equilibrium_stays : forall {L} (S : FunctionalSystem L) (f : InsideOperator S)
  (x : get_Elements S),
  equilibrium f x -> forall n, evolve f x n = x.
Proof.
  intros L S f x Heq n. unfold evolve. induction n as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. exact Heq.
Qed.

(* ===================================================================== *)
(*  IRREVERSIBILITY — the L5 arrow                                         *)
(* ===================================================================== *)

(** A bool-state system with the full relation (any two states related). *)
Definition SB : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := bool;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** A COLLAPSING dynamics: it sends every state to `true` (it merges the two states). *)
Definition collapse : InsideOperator SB :=
  @mkERRMorphism L2 SB SB (fun _ => true) (fun x y _ => I).

(** ★★ The collapse is IRREVERSIBLE: no operator undoes it (it would have to send `true` back to both
    `false` and `true`).  The formal shadow of the L5 arrow — a distinction unmade is not recoverable. *)
Lemma collapse_irreversible : ~ reversible collapse.
Proof.
  intros [g [Hgf _]].
  pose proof (Hgf false) as Hf. pose proof (Hgf true) as Ht.
  simpl in Hf, Ht. rewrite Ht in Hf. discriminate Hf.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ SYSTEM DYNAMICS: a system evolves by iterating its inside-operator —
      (process)      the trajectory is a process (starts, steps);
      (monoid)       time composes: evolve (m+n) = evolve m after evolve n;
      (constitution) evolution preserves Roles (related stay related);
      (equilibrium)  a fixed point is invariant under evolution;
      (irreversible) a collapsing dynamics has no inverse — the L5 arrow.
    Evolution is a process, constitution-preserving, monoidal in time, with equilibria as fixed points
    and a genuine arrow (irreversibility). *)
Theorem err_dynamics :
  (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x0 : get_Elements S),
     trajectory f x0 0 = x0 /\ (forall n, trajectory f x0 (Datatypes.S n) = err_map f (trajectory f x0 n)))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x0 : get_Elements S) (m n : nat),
        trajectory f x0 (m + n) = trajectory f (trajectory f x0 n) m)
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (n : nat) (x y : get_Elements S),
        get_Roles S x y -> get_Roles S (evolve f x n) (evolve f y n))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (x : get_Elements S),
        equilibrium f x -> forall n, evolve f x n = x)
  /\ ~ reversible collapse.
Proof.
  split; [ exact @trajectory_is_process | ].
  split; [ exact @evolve_compose | ].
  split; [ exact @evolution_preserves_roles | ].
  split; [ exact @equilibrium_stays | exact collapse_irreversible ].
Qed.

Print Assumptions err_dynamics.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  6 Qed, 0 Admitted, 0 axioms.                                             *)
(*  System DYNAMICS = iterating an inside-operator (ERROperator #125).         *)
(*  evolve / trajectory (the evolution as a process, ERRProcessConstitution    *)
(*  #127); trajectory_is_process (starts/steps); evolve_compose (time is a     *)
(*  monoid); evolution_preserves_roles (constitution preserved, via err_pres); *)
(*  equilibrium / equilibrium_stays (fixed points are invariant); reversible / *)
(*  collapse_irreversible (a collapsing dynamics has no inverse — the L5 arrow,*)
(*  cf. foundation/L5_Arrow.v).  Capstone err_dynamics.  HONEST: discrete      *)
(*  process (not continuous flow); equilibria = fixed points (not the analytic *)
(*  Banach FixedPoint.v); irreversibility witnessed by a concrete collapse.    *)
(* ========================================================================= *)
