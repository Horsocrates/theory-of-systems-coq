(** * ERRDynamicsArrow.v — deepening the dynamics (thread ②): a dynamics has TWO ARROWS, and its long
      run is a ROLE-LIMIT.

    ERRDynamics gave a system DYNAMICS (evolve / trajectory / equilibrium / collapse_irreversible).
    This file deepens it along the two axes named for the thread:

      ★ TWO ARROWS.  The STATE arrow is CONTINGENT: it may be reversible (flip, a period-2 involution)
        or irreversible (collapse, from ERRDynamics).  The TIME / STAGE arrow is the L5 arrow
        (foundation/L5_Arrow.v): it is irreversible UNCONDITIONALLY — even a periodic dynamics whose
        STATE returns (evolve flip x0 2 = x0) never returns in TIME (arrow_never_returns).  Recurrence
        is a fact about STATES, never about time.

      ★ RECURRENCE is the Element side.  A periodic orbit CLOSES: it returns at every multiple of its
        period (periodic_closes) — a finite cycle, the dynamical face of "returns <=> rational"
        (cf. CircleRotation.v).

      ★ THE ATTRACTOR is a ROLE-LIMIT (the finitization boundary H1, RoleLimitSpecies.v).  The orbit's
        size at each finite stage is an actual rational; its long run is classified: BOUNDED = an
        attractor regime (Species I — halve contracts to its fixed point) vs ESCAPE (Species II —
        double runs away).  The two regimes are mutually EXCLUSIVE (attractor_excludes_escape).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      evolution rides an irreversible STAGE-arrow (L5) whether or not the state-step is invertible;
      RECURRENCE is a property of STATES (a periodic orbit closes), never of TIME; the orbit's long run
      is a ROLE-LIMIT — bounded (attractor, Species I) or escaping (Species II).
    Roles (L4): flip / collapse (the two state-arrows — reversible vs not); arrow_forward (the
      time-arrow); periodic / periodic_closes (state recurrence); bounded_orbit / escaping_orbit
      (the role-limit regimes); attractor_excludes_escape (exclusivity).
    Elements (L1+P4): stages (nat); states; the size of a state (a rational at each finite stage —
      actual; the long-run limit never actual).
    P4 diagnostic (could it be otherwise?):
      the STATE could return (period 2 — flip) or collapse (collapse); but the STAGE could NOT return —
      arrow_never_returns is FORCED (that is exactly what makes it time, the L5 arrow).  The attractor
      is a role-limit: each finite size is actual (P4), boundedness is a claim over ALL stages.
    Honesty wall:
      discrete dynamics (not a continuous flow).  The EXHAUSTIVE "every orbit is bounded-or-escaping"
      is the L3 disjunction (RoleLimitSpecies.species_dichotomy) — deliberately NOT re-proved here, so
      this file stays 0-axiom; we prove the two sides INHABITED (concrete halve / double witnesses,
      reusing halfpow_regular / pow2_singular verbatim) and mutually EXCLUSIVE (regular_not_singular,
      constructive).  flip is a period-2 involution (the simplest reversible dynamics); the role-limit
      witnesses live on a ℚ-carrier system.  Ties ERRDynamics + L5_Arrow + RoleLimitSpecies.  0 axioms.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map *)
From ToS Require Import foundation.ERRDynamics.       (* InsideOperator, evolve, trajectory, reversible, SB, collapse, collapse_irreversible, evolve_compose *)
From ToS Require Import foundation.L5_Arrow.          (* arrow_forward, arrow_never_returns *)
From ToS Require Import RoleLimitSpecies.             (* RegularLimit, SingularLimit, regular_not_singular, halfpow, halfpow_regular, pow2, pow2_singular *)
From Stdlib Require Import QArith Lia.

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  RECURRENCE — the Element side (a periodic orbit closes)               *)
(* ===================================================================== *)

(** A dynamics is PERIODIC at x0 with period p if it returns to x0 after p>0 steps. *)
Definition periodic {L} {Sys : FunctionalSystem L} (f : InsideOperator Sys)
  (x0 : get_Elements Sys) (p : nat) : Prop :=
  (0 < p)%nat /\ evolve f x0 p = x0.

(** ★★ A periodic orbit CLOSES: it returns to x0 at every multiple of its period — a finite cycle
    (the dynamical "returns <=> rational", the Element side). *)
Lemma periodic_closes : forall {L} (Sys : FunctionalSystem L) (f : InsideOperator Sys)
  (x0 : get_Elements Sys) (p : nat),
  periodic f x0 p -> forall k, trajectory f x0 (k * p) = x0.
Proof.
  intros L Sys f x0 p [Hp Hper] k. induction k as [|k IH].
  - reflexivity.
  - replace (S k * p)%nat with (p + k * p)%nat by lia.
    rewrite evolve_compose. rewrite IH. exact Hper.
Qed.

(* ===================================================================== *)
(*  THE STATE ARROW — reversible (flip) or irreversible (collapse)        *)
(* ===================================================================== *)

(** A REVERSIBLE dynamics on SB: flip = the boolean involution (negb). *)
Definition flip : InsideOperator SB :=
  @mkERRMorphism L2 SB SB negb (fun x y _ => I).

(** ★ flip is REVERSIBLE: it is its own two-sided inverse (negb is an involution). *)
Lemma flip_reversible : reversible flip.
Proof. exists flip. split; intro x; destruct x; reflexivity. Qed.

(** ★ flip has PERIOD 2: two steps return every state to itself. *)
Lemma flip_period2 : forall x0, evolve flip x0 2 = x0.
Proof. intro x0. unfold evolve. simpl. destruct x0; reflexivity. Qed.

(** ★ The flip orbit CLOSES at every even step (Element-side recurrence). *)
Lemma flip_orbit_closes : forall k, trajectory flip true (k * 2) = true.
Proof.
  intro k. apply (periodic_closes SB flip true 2).
  split; [ lia | apply flip_period2 ].
Qed.

(* ===================================================================== *)
(*  THE TWO ARROWS — state may return, TIME never does (the L5 arrow)     *)
(* ===================================================================== *)

(** ★★★ The two arrows.  Even for the reversible, periodic flip, the STATE returns after 2 steps
    (evolve flip x0 2 = x0) while the TIME / STAGE arrow NEVER returns (arrow_never_returns).  The
    irreversible time-arrow (L5) underlies every dynamics — including reversible ones.  Recurrence is
    a fact about states, never about time. *)
Lemma state_recurs_time_does_not :
  (forall x0, evolve flip x0 2 = x0) /\ (forall K, arrow_forward K <> K).
Proof. split; [ exact flip_period2 | exact arrow_never_returns ]. Qed.

(* ===================================================================== *)
(*  THE ATTRACTOR IS A ROLE-LIMIT (H1) — a ℚ-carrier dynamics             *)
(* ===================================================================== *)

Open Scope Q_scope.

(** A ℚ-carrier system (states = rationals; trivial constitution, full relation). *)
Definition SQ : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := Q;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** A CONTRACTING dynamics (halving) — its attractor is the fixed point 0. *)
Definition halve : InsideOperator SQ :=
  @mkERRMorphism L2 SQ SQ (fun q => (1#2) * q) (fun x y _ => I).

(** An EXPANDING dynamics (doubling) — it runs away. *)
Definition double : InsideOperator SQ :=
  @mkERRMorphism L2 SQ SQ (fun q => 2 * q) (fun x y _ => I).

(** An orbit is BOUNDED (attractor regime, Species I) / ESCAPING (Species II) according to the
    long run of its size (here the size IS the state, a rational). *)
Definition bounded_orbit {L} {Sys : FunctionalSystem L} (f : InsideOperator Sys)
  (x0 : get_Elements Sys) (size : get_Elements Sys -> Q) : Prop :=
  RegularLimit (fun n => size (trajectory f x0 n)).

Definition escaping_orbit {L} {Sys : FunctionalSystem L} (f : InsideOperator Sys)
  (x0 : get_Elements Sys) (size : get_Elements Sys -> Q) : Prop :=
  SingularLimit (fun n => size (trajectory f x0 n)).

(** The halving trajectory from 1 IS the canonical Species-I sequence (1/2)^n. *)
Lemma traj_halve : forall n, trajectory halve 1 n = halfpow n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - change (trajectory halve 1 (S k)) with ((1#2) * trajectory halve 1 k).
    rewrite IH. reflexivity.
Qed.

(** The doubling trajectory from 1 IS the canonical Species-II sequence 2^n. *)
Lemma traj_double : forall n, trajectory double 1 n = pow2 n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - change (trajectory double 1 (S k)) with (2 * trajectory double 1 k).
    rewrite IH. reflexivity.
Qed.

(** ★★ The contracting orbit is BOUNDED — an attractor (Species I). *)
Lemma halve_orbit_bounded : bounded_orbit halve 1 (fun q => q).
Proof.
  unfold bounded_orbit. cbv beta.
  destruct halfpow_regular as [M HM]. exists M. intro n.
  rewrite traj_halve. apply HM.
Qed.

(** ★★ The expanding orbit ESCAPES (Species II). *)
Lemma double_orbit_escapes : escaping_orbit double 1 (fun q => q).
Proof.
  unfold escaping_orbit. cbv beta. intro M.
  destruct (pow2_singular M) as [n Hn]. exists n.
  rewrite traj_double. exact Hn.
Qed.

(** ★★ The two regimes are mutually EXCLUSIVE: an attractor orbit cannot also escape (constructive —
    this side needs no L3). *)
Lemma attractor_excludes_escape : forall {L} (Sys : FunctionalSystem L) (f : InsideOperator Sys)
  (x0 : get_Elements Sys) (size : get_Elements Sys -> Q),
  bounded_orbit f x0 size -> ~ escaping_orbit f x0 size.
Proof. intros L Sys f x0 size Hb He. exact (regular_not_singular _ Hb He). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ DYNAMICS DEEPENED — two arrows + role-limit:
      (state irreversible)  collapse has no inverse (the contingent irreversible state-arrow);
      (state reversible)    flip is its own inverse (the contingent reversible state-arrow);
      (two arrows)          flip's STATE returns (period 2) yet TIME never does (the L5 arrow);
      (attractor)           the contracting orbit is bounded — Species I (H1);
      (escape)              the expanding orbit runs away — Species II (H1);
      (exclusive)           bounded and escaping are mutually exclusive (constructive).
    The state-arrow is contingent (reversible or not); the time-arrow is the unconditional L5 arrow;
    the long run is a role-limit (attractor vs escape). *)
Theorem err_dynamics_deepened :
  (~ reversible collapse)
  /\ reversible flip
  /\ ((forall x0, evolve flip x0 (2)%nat = x0) /\ (forall K, arrow_forward K <> K))
  /\ bounded_orbit halve 1 (fun q => q)
  /\ escaping_orbit double 1 (fun q => q)
  /\ (forall N, RegularLimit N -> ~ SingularLimit N).
Proof.
  split; [ exact collapse_irreversible | ].
  split; [ exact flip_reversible | ].
  split; [ exact state_recurs_time_does_not | ].
  split; [ exact halve_orbit_bounded | ].
  split; [ exact double_orbit_escapes | exact regular_not_singular ].
Qed.

Print Assumptions err_dynamics_deepened.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Deepens ERRDynamics (thread ②) along its two named axes.                  *)
(*  TWO ARROWS: flip (reversible involution) vs collapse (irreversible) =      *)
(*  the contingent STATE-arrow; arrow_never_returns (L5_Arrow) = the           *)
(*  unconditional TIME-arrow.  state_recurs_time_does_not: a periodic STATE    *)
(*  returns (evolve flip x0 2 = x0) but TIME never does.  RECURRENCE is the     *)
(*  Element side: periodic_closes (orbit returns at every multiple),           *)
(*  flip_orbit_closes (even steps).  THE ATTRACTOR is a ROLE-LIMIT (H1):        *)
(*  on a ℚ-carrier, halve_orbit_bounded (contraction -> Species I attractor,   *)
(*  via halfpow_regular) vs double_orbit_escapes (expansion -> Species II, via  *)
(*  pow2_singular); attractor_excludes_escape (constructive exclusivity).       *)
(*  Capstone err_dynamics_deepened.  HONEST: discrete dynamics; the EXHAUSTIVE  *)
(*  bounded-or-escaping disjunction is the L3 species_dichotomy (cited, not     *)
(*  re-proved) — this file proves both sides inhabited + exclusive, 0-axiom.    *)
(* ========================================================================= *)
