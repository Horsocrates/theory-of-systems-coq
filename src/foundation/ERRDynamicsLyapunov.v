(** * ERRDynamicsLyapunov.v — deepening the dynamics (thread ②, further): a LYAPUNOV function (a
      ℚ-valued energy that never increases) certifies the bounded/attractor regime; STRICT descent
      rules out spurious recurrence.

    A Lyapunov function is the classical certificate of stability: a quantity that the dynamics never
    increases.  Over our ordered field ℚ:

      ★ Lyapunov f V — V does not increase under the step (V (f x) <= V x).  Then along the orbit V is
        MONOTONE non-increasing (lyapunov_nonincreasing) and BOUNDED by the start (lyapunov_bounded).
      ★ Lyapunov certifies the BOUNDED regime — the V-sequence is a RegularLimit (Species I of the
        finitization boundary H1): lyapunov_regular.  This is the attractor regime.
      ★ StrictLyapunov f V — additionally V strictly DECREASES off equilibria.  Then a non-equilibrium
        point NEVER returns (not_equilibrium_no_return): strict descent forbids spurious cycles.
      ★ Witness: collapse with the indicator energy Vcol descends to its attractor `true`; the
        non-equilibrium `false` never returns.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      an ENERGY non-increasing under the step certifies monotone DESCENT + BOUNDEDNESS (the attractor
      regime, Species I of H1); STRICT descent off equilibria forbids non-equilibrium RECURRENCE.
    Roles (L4): Lyapunov / StrictLyapunov (the certificate); lyapunov_nonincreasing / _bounded /
      _regular (descent + bound + Species I); not_equilibrium_no_return; the collapse witness.
    Elements (L1+P4): the states; the ℚ-energy V; the operator.
    P4 diagnostic (could it be otherwise?):
      the energy is a CONTINGENT certificate; when one exists, the dynamics is confined to the bounded
      regime (Species I) — each V (evolve n) is finite/actual (P4), the infimum a role-limit.
    Honesty wall:
      "attractor" = BOUNDEDNESS (RegularLimit, Species I) + monotone descent, NOT a proof of
      convergence to a specific point (that needs metric completeness = the role-limit); strict ⟹
      no-return is the CONSTRUCTIVE contrapositive (a non-equilibrium never returns), avoiding LEM;
      witness = collapse (bool carrier, so no lra/Qabs friction).  Reuses ERRDynamics (evolve /
      equilibrium / collapse) + RoleLimitSpecies (RegularLimit, classic-free use).  0 axioms.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* err_map *)
From ToS Require Import foundation.ERRDynamics.       (* InsideOperator, evolve, equilibrium, collapse *)
From ToS Require Import RoleLimitSpecies.             (* RegularLimit *)
From Stdlib Require Import QArith Lia.

Open Scope Q_scope.

(** A small ground fact (the indicator energy uses it). *)
Lemma q0_le_1 : 0 <= 1.
Proof. apply Qlt_le_weak. rewrite Qlt_alt. reflexivity. Qed.

(* ===================================================================== *)
(*  LYAPUNOV FUNCTIONS — a non-increasing energy                          *)
(* ===================================================================== *)

(** A Lyapunov function for f: a ℚ-energy that the step never increases. *)
Definition Lyapunov {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q) : Prop := forall x, V (err_map f x) <= V x.

(** One step does not increase the energy. *)
Lemma lyapunov_step : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q),
  Lyapunov f V -> forall x n, V (evolve f x (Datatypes.S n)) <= V (evolve f x n).
Proof.
  intros L S f V Hlyap x n.
  change (evolve f x (Datatypes.S n)) with (err_map f (evolve f x n)). apply Hlyap.
Qed.

(** ★★ The energy is BOUNDED along the orbit by its starting value. *)
Lemma lyapunov_bounded : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q),
  Lyapunov f V -> forall x n, V (evolve f x n) <= V x.
Proof.
  intros L S f V Hlyap x n. induction n as [|k IH].
  - change (evolve f x 0) with x. apply Qle_refl.
  - apply Qle_trans with (V (evolve f x k)); [ apply lyapunov_step; assumption | exact IH ].
Qed.

(** ★★ The energy is MONOTONE non-increasing along the orbit. *)
Lemma lyapunov_nonincreasing : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q),
  Lyapunov f V -> forall x m n, (m <= n)%nat -> V (evolve f x n) <= V (evolve f x m).
Proof.
  intros L S f V Hlyap x m n Hle. induction Hle as [|n Hle IH].
  - apply Qle_refl.
  - apply Qle_trans with (V (evolve f x n)); [ apply lyapunov_step; assumption | exact IH ].
Qed.

(** ★★★ A Lyapunov function certifies the BOUNDED regime: the energy sequence is a RegularLimit
    (Species I of the finitization boundary H1) — the attractor regime. *)
Lemma lyapunov_regular : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q),
  Lyapunov f V -> forall x, RegularLimit (fun n => V (evolve f x n)).
Proof.
  intros L S f V Hlyap x. exists (V x). intro n. cbv beta.
  apply lyapunov_bounded; exact Hlyap.
Qed.

(* ===================================================================== *)
(*  STRICT LYAPUNOV — rules out spurious recurrence                        *)
(* ===================================================================== *)

(** A STRICT Lyapunov function: non-increasing, and strictly decreasing OFF equilibria. *)
Definition StrictLyapunov {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q) : Prop :=
  Lyapunov f V /\ (forall x, ~ equilibrium f x -> V (err_map f x) < V x).

(** ★★★ Strict descent forbids spurious cycles: a NON-equilibrium point never returns. *)
Lemma not_equilibrium_no_return : forall {L} {S : FunctionalSystem L} (f : InsideOperator S)
  (V : get_Elements S -> Q),
  StrictLyapunov f V -> forall x, ~ equilibrium f x -> forall p, evolve f x (Datatypes.S p) <> x.
Proof.
  intros L S f V [Hweak Hstrict] x Hne p Heq.
  assert (Hle1 : V (evolve f x (Datatypes.S p)) <= V (evolve f x (1%nat))).
  { apply lyapunov_nonincreasing; [ exact Hweak | lia ]. }
  change (evolve f x (1%nat)) with (err_map f x) in Hle1.
  assert (Hlt : V (err_map f x) < V x) by (apply Hstrict; exact Hne).
  rewrite Heq in Hle1.
  apply (Qlt_irrefl (V x)). apply Qle_lt_trans with (V (err_map f x)); assumption.
Qed.

(* ===================================================================== *)
(*  WITNESS — collapse descends to its attractor `true`                    *)
(* ===================================================================== *)

(** The indicator energy: 0 at the attractor `true`, 1 elsewhere. *)
Definition Vcol (b : bool) : Q := if b then 0 else 1.

(** ★ collapse is a Lyapunov dynamics for Vcol (it descends toward `true`). *)
Lemma collapse_lyapunov : Lyapunov collapse Vcol.
Proof.
  intro x. change (err_map collapse x) with true.
  destruct x; [ apply Qle_refl | apply q0_le_1 ].
Qed.

(** false is not an equilibrium of collapse. *)
Lemma collapse_false_not_equilibrium : ~ equilibrium collapse false.
Proof. unfold equilibrium. change (err_map collapse false) with true. discriminate. Qed.

(** ★★ collapse is a STRICT Lyapunov dynamics (strict descent off its equilibrium `true`). *)
Lemma collapse_strict : StrictLyapunov collapse Vcol.
Proof.
  split; [ exact collapse_lyapunov | ].
  intros x Hne. change (err_map collapse x) with true. destruct x.
  - exfalso. apply Hne. unfold equilibrium. reflexivity.
  - rewrite Qlt_alt. reflexivity.
Qed.

(** ★★ Hence the non-equilibrium `false` NEVER returns under collapse. *)
Lemma collapse_false_never_returns : forall p, evolve collapse false (Datatypes.S p) <> false.
Proof.
  apply (not_equilibrium_no_return collapse Vcol collapse_strict false collapse_false_not_equilibrium).
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ LYAPUNOV STABILITY:
      (descent)     a Lyapunov energy is monotone non-increasing along the orbit;
      (bounded)     it is bounded by its starting value;
      (attractor)   it certifies the bounded regime — a RegularLimit (Species I, H1);
      (no cycles)   a strict Lyapunov energy forbids non-equilibrium recurrence;
      (witness)     collapse descends to its attractor `true`; `false` never returns.
    A non-increasing energy certifies descent and confinement to the bounded (attractor) regime; strict
    descent forbids spurious recurrence. *)
Theorem err_dynamics_lyapunov :
  (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (V : get_Elements S -> Q),
     Lyapunov f V -> forall x m n, (m <= n)%nat -> V (evolve f x n) <= V (evolve f x m))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (V : get_Elements S -> Q),
     Lyapunov f V -> forall x n, V (evolve f x n) <= V x)
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (V : get_Elements S -> Q),
     Lyapunov f V -> forall x, RegularLimit (fun n => V (evolve f x n)))
  /\ (forall (L : Level) (S : FunctionalSystem L) (f : InsideOperator S) (V : get_Elements S -> Q),
     StrictLyapunov f V -> forall x, ~ equilibrium f x -> forall p, evolve f x (Datatypes.S p) <> x)
  /\ (Lyapunov collapse Vcol
      /\ StrictLyapunov collapse Vcol
      /\ (forall p, evolve collapse false (Datatypes.S p) <> false)).
Proof.
  split; [ exact @lyapunov_nonincreasing | ].
  split; [ exact @lyapunov_bounded | ].
  split; [ exact @lyapunov_regular | ].
  split; [ exact @not_equilibrium_no_return | ].
  split; [ exact collapse_lyapunov
         | split; [ exact collapse_strict | exact collapse_false_never_returns ] ].
Qed.

Print Assumptions err_dynamics_lyapunov.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Deepens thread ②: LYAPUNOV stability.  Lyapunov f V (energy non-increasing *)
(*  under the step); lyapunov_step / _bounded / _nonincreasing (monotone        *)
(*  descent + bound by start); lyapunov_regular (the energy sequence is a       *)
(*  RegularLimit — Species I of H1, the attractor regime).  StrictLyapunov      *)
(*  (strict off equilibria) => not_equilibrium_no_return (non-equilibria never  *)
(*  recur, constructive contrapositive — no LEM).  WITNESS: Vcol indicator,     *)
(*  collapse_lyapunov + collapse_strict + collapse_false_never_returns (collapse *)
(*  descends to attractor `true`, `false` never returns).  Capstone             *)
(*  err_dynamics_lyapunov.  HONEST: attractor = boundedness (RegularLimit) +    *)
(*  descent, not point-convergence (needs completeness = role-limit); bool      *)
(*  witness avoids lra/Qabs friction.                                          *)
(* ========================================================================= *)
