(** * ERRDynamicsGroupBasin.v — deepening the dynamics (thread ②, further): the TWO TEMPORAL
      DIRECTIONS of a dynamics — BACKWARD (reversibility = a group action) and FORWARD (the basin of
      an attractor).

    ERRDynamicsArrow gave the two ARROWS (state vs time) and the attractor as a role-limit.  This file
    asks the two temporal questions of a dynamics:

      ★ BACKWARD — can we undo it?  A REVERSIBLE dynamics makes every power invertible: g^n is a
        two-sided inverse of f^n (reversible_iterate_inverse), so the powers form a GROUP action
        (reversible_power_invertible).  The orbit is then FINITE (periodic — flip, the Element side,
        a finite cyclic group) or an INFINITE ℤ-orbit (aperiodic — shift on ℤ, the role-limit side:
        shift_aperiodic, the orbit never returns).  Reversibility undoes the STATE; the L5 time-arrow
        (ERRDynamicsArrow) still forbids stage-return.

      ★ FORWARD — where do orbits end up?  The BASIN of an attractor.  A COLLAPSE has a TOTAL arrival
        basin: every state reaches `true` (collapse_basin_total).  A CONTRACTION (halve) shows the P4
        gem: its attractor 0 is APPROACHED by convergence (bounded, Species I) but ARRIVED at by
        nothing — (1/2)^n · x0 == 0 iff x0 == 0 (halve_arrival_only_zero).  The attractor is a
        role-limit: actualized only at the fixed point itself (halve_one_approaches_never_arrives).

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      a reversible dynamics' powers form a GROUP (every f^n invertible); its orbit RETURNS (finite —
      Element) or NEVER returns (infinite ℤ-orbit — role-limit); a contraction's attractor is
      APPROACHED (convergence, all starts) but ARRIVED at by nothing but the fixed point.
    Roles (L4): reversible / the iterate-inverse (the group); reaches / the basin (forward);
      shift / flip / collapse / halve (the witness dynamics).
    Elements (L1+P4): stages (nat); states (bool / ℤ / ℚ); the operators.
    P4 diagnostic (could it be otherwise?):
      the state-orbit could be finite (flip returns) OR infinite (shift never returns) — both real;
      the contraction's attractor 0 could be ARRIVED at only FROM 0 — every other start merely
      converges (a role-limit, never actual in finite time).  So "reaching" the attractor is, for a
      contraction, a role-limit, not an Element-side event.
    Honesty wall:
      discrete dynamics; reversibility = a two-sided inverse OPERATOR; the group is the iterate-inverse
      (g^n ∘ f^n = id, reversible_power_invertible), NOT a full ℤ-indexed group object; convergence is
      shown as boundedness (Species I, reusing halve_orbit_bounded), arrival as Qeq-exactness; the
      EXHAUSTIVE periodic-or-aperiodic split is not claimed (two witnesses, not a dichotomy theorem).
      Reuses ERRDynamics + ERRDynamicsArrow (flip / halve / bounded_orbit) + RoleLimitSpecies
      (halfpow).  0 axioms.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import foundation.ERRComposition.   (* ERRMorphism, mkERRMorphism, err_map *)
From ToS Require Import foundation.ERRDynamics.       (* InsideOperator, evolve, iterate, reversible, SB, collapse *)
From ToS Require Import foundation.ERRDynamicsArrow.  (* flip, flip_reversible, flip_period2, halve, bounded_orbit, halve_orbit_bounded *)
From ToS Require Import RoleLimitSpecies.             (* halfpow *)
From Stdlib Require Import QArith ZArith Lia.

Arguments fs_constitution {L}.
Arguments fs_domain {L}.
Arguments fs_relations {L}.
Arguments fs_functional {L}.
Arguments fs_element_level {L}.
Arguments fs_level_valid {L}.

(* ===================================================================== *)
(*  BACKWARD — reversibility is a GROUP action (every power invertible)    *)
(* ===================================================================== *)

(** Iteration commutes one step: f^(S k) x = f^k (f x). *)
Lemma iterate_commute : forall {A : Type} (h : A -> A) (k : nat) (x : A),
  iterate h (S k) x = iterate h k (h x).
Proof.
  intros A h k. induction k as [|j IH]; intro x.
  - reflexivity.
  - change (iterate h (S (S j)) x) with (h (iterate h (S j) x)).
    change (iterate h (S j) (h x)) with (h (iterate h j (h x))).
    rewrite (IH x). reflexivity.
Qed.

(** ★★ The iterate-inverse: if g undoes f one step, then g^n undoes f^n — every POWER of a reversible
    dynamics is invertible (the group law). *)
Lemma reversible_iterate_inverse : forall {L} {Sys : FunctionalSystem L}
  (f g : InsideOperator Sys),
  (forall x, err_map g (err_map f x) = x) ->
  forall n x, iterate (err_map g) n (iterate (err_map f) n x) = x.
Proof.
  intros L Sys f g Hinv n. induction n as [|k IH]; intro x.
  - reflexivity.
  - rewrite (iterate_commute (err_map f) k x).
    change (iterate (err_map g) (S k) (iterate (err_map f) k (err_map f x)))
      with (err_map g (iterate (err_map g) k (iterate (err_map f) k (err_map f x)))).
    rewrite IH. apply Hinv.
Qed.

(** ★★★ A REVERSIBLE dynamics is a GROUP action: the n-step map f^n is invertible for every n. *)
Lemma reversible_power_invertible : forall {L} (Sys : FunctionalSystem L) (f : InsideOperator Sys),
  reversible f -> forall n, exists h, forall x, h (evolve f x n) = x.
Proof.
  intros L Sys f [g [Hgf _]] n. exists (iterate (err_map g) n). intro x.
  unfold evolve. exact (reversible_iterate_inverse f g Hgf n x).
Qed.

(* ===================================================================== *)
(*  FORWARD — the basin of an attractor                                    *)
(* ===================================================================== *)

(** A state x0 REACHES xstar if the evolution eventually equals xstar and stays (its basin). *)
Definition reaches {L} {Sys : FunctionalSystem L} (f : InsideOperator Sys)
  (x0 xstar : get_Elements Sys) : Prop :=
  exists N, forall n, (N <= n)%nat -> evolve f x0 n = xstar.

(** ★★ The collapse has a TOTAL arrival basin: every state reaches `true` (after one step). *)
Lemma collapse_basin_total : forall x0, reaches collapse x0 true.
Proof.
  intro x0. exists 1%nat. intros n Hn. destruct n as [|k]; [ lia | reflexivity ].
Qed.

(* ===================================================================== *)
(*  An INFINITE ℤ-orbit — a reversible APERIODIC dynamics (shift)          *)
(* ===================================================================== *)

Open Scope Z_scope.

(** A ℤ-carrier system (states = integers). *)
Definition SZ : FunctionalSystem L2.
Proof.
  refine {| fs_constitution := TrivialConstitution; fs_domain := Z;
            fs_relations := (fun _ _ => True); fs_functional := I;
            fs_element_level := fun _ => L1; fs_level_valid := fun _ => _ |}.
  exact L1_lt_L2.
Defined.

(** The SHIFT (successor) and its inverse (predecessor) — a reversible dynamics. *)
Definition shift : InsideOperator SZ := @mkERRMorphism L2 SZ SZ Z.succ (fun x y _ => I).
Definition unshift : InsideOperator SZ := @mkERRMorphism L2 SZ SZ Z.pred (fun x y _ => I).

(** The shift advances by n: evolve shift x n = x + n. *)
Lemma evolve_shift_val : forall n (x : Z), evolve shift x n = x + Z.of_nat n.
Proof.
  induction n as [|k IH]; intro x.
  - change (evolve shift x 0) with x. change (Z.of_nat 0) with 0%Z.
    rewrite Z.add_0_r. reflexivity.
  - change (evolve shift x (S k)) with (Z.succ (evolve shift x k)).
    rewrite IH. lia.
Qed.

(** ★ shift is REVERSIBLE (predecessor undoes successor and vice versa). *)
Lemma shift_reversible : reversible shift.
Proof.
  exists unshift. split; intro x; cbn [err_map];
    [ apply Z.pred_succ | apply Z.succ_pred ].
Qed.

(** ★★ shift is APERIODIC: it NEVER returns — the orbit is an infinite ℤ-orbit (the role-limit side
    of reversible dynamics, vs flip's finite periodic orbit). *)
Lemma shift_aperiodic : forall (x0 : Z) n, (0 < n)%nat -> evolve shift x0 n <> x0.
Proof.
  intros x0 n Hn Heq. rewrite evolve_shift_val in Heq. lia.
Qed.

Close Scope Z_scope.

(* ===================================================================== *)
(*  The CONTRACTION's attractor — approached, never arrived (the P4 gem)   *)
(* ===================================================================== *)

Open Scope Q_scope.

(** The half-power is strictly positive at every stage. *)
Lemma halfpow_pos : forall n, 0 < halfpow n.
Proof.
  assert (H2 : 0 < (1#2)) by (rewrite Qlt_alt; reflexivity).
  induction n as [|k IH]; simpl.
  - rewrite Qlt_alt; reflexivity.
  - apply Qmult_lt_0_compat; [ exact H2 | exact IH ].
Qed.

(** The halving evolution in closed form: evolve halve x0 n == (1/2)^n * x0. *)
Lemma evolve_halve_val : forall n (x0 : Q), evolve halve x0 n == halfpow n * x0.
Proof.
  induction n as [|k IH]; intro x0.
  - change (evolve halve x0 0) with x0. change (halfpow 0) with 1. ring.
  - change (evolve halve x0 (S k)) with ((1#2) * evolve halve x0 k).
    rewrite IH. change (halfpow (S k)) with ((1#2) * halfpow k). ring.
Qed.

(** ★★ The contraction ARRIVES at its attractor 0 ONLY from 0 itself: (1/2)^n * x0 == 0 forces
    x0 == 0.  Every other start merely CONVERGES (a role-limit, never actual in finite time). *)
Lemma halve_arrival_only_zero : forall (x0 : Q) n, evolve halve x0 n == 0 -> x0 == 0.
Proof.
  intros x0 n H. rewrite evolve_halve_val in H.
  destruct (Qmult_integral _ _ H) as [Hc | Hx].
  - exfalso. assert (Hp := halfpow_pos n). rewrite Hc in Hp. exact (Qlt_irrefl 0 Hp).
  - exact Hx.
Qed.

(** ★★★ The P4 gem: from x0 = 1 the orbit is BOUNDED (Species I — it converges to the attractor 0)
    yet NEVER equals 0 (it only approaches).  The attractor is a role-limit: approached, never
    arrived. *)
Lemma halve_one_approaches_never_arrives :
  (forall n, ~ (evolve halve 1 n == 0)) /\ bounded_orbit halve 1 (fun q => q).
Proof.
  split.
  - intros n H. apply halve_arrival_only_zero in H.
    rewrite Qeq_alt in H. discriminate H.
  - exact halve_orbit_bounded.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ DYNAMICS — the two temporal directions:
      (group)        a reversible dynamics' powers are all invertible (a group action);
      (finite orbit) flip is reversible and periodic (returns in 2 — the Element side);
      (infinite orbit) shift is reversible and aperiodic (never returns — the role-limit side);
      (total basin)  collapse's arrival basin is total (everything reaches `true`);
      (role-limit attractor) the contraction approaches 0 but never arrives (approached, not actual).
    Backward: reversibility is a group, orbit finite-or-infinite.  Forward: the basin — a collapse
    arrives, a contraction only converges. *)
Theorem err_dynamics_group_basin :
  (forall (L : Level) (Sys : FunctionalSystem L) (f : InsideOperator Sys),
     reversible f -> forall n, exists h, forall x, h (evolve f x n) = x)
  /\ (reversible flip /\ (forall x0, evolve flip x0 (2)%nat = x0))
  /\ (reversible shift /\ (forall x0 n, (0 < n)%nat -> evolve shift x0 n <> x0))
  /\ (forall x0, reaches collapse x0 true)
  /\ ((forall n, ~ (evolve halve 1 n == 0)) /\ bounded_orbit halve 1 (fun q => q)).
Proof.
  split; [ exact @reversible_power_invertible | ].
  split; [ split; [ exact flip_reversible | exact flip_period2 ] | ].
  split; [ split; [ exact shift_reversible | exact shift_aperiodic ] | ].
  split; [ exact collapse_basin_total | exact halve_one_approaches_never_arrives ].
Qed.

Print Assumptions err_dynamics_group_basin.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  12 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Deepens ERRDynamicsArrow (thread ②) along its two temporal directions.    *)
(*  BACKWARD (group): iterate_commute + reversible_iterate_inverse (g^n undoes *)
(*  f^n) => reversible_power_invertible (every power invertible = a group      *)
(*  action).  Orbit finite (flip periodic, Element) vs infinite (shift on ℤ:   *)
(*  evolve_shift_val, shift_reversible, shift_aperiodic = never returns,       *)
(*  role-limit).  FORWARD (basin): reaches; collapse_basin_total (collapse's   *)
(*  arrival basin is total); the contraction's attractor is a role-limit —     *)
(*  evolve_halve_val (closed form (1/2)^n*x0), halve_arrival_only_zero (0      *)
(*  reached only from 0), halve_one_approaches_never_arrives (from 1: bounded  *)
(*  Species I but never equals 0 — approached, not arrived).  Capstone         *)
(*  err_dynamics_group_basin.  HONEST: discrete; group = iterate-inverse (not  *)
(*  a ℤ-indexed group object); convergence = boundedness; arrival = Qeq; two   *)
(*  orbit witnesses (not a periodic-or-aperiodic dichotomy theorem).           *)
(* ========================================================================= *)
