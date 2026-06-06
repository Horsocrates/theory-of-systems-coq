(** * ScaleHierarchySynthesis.v — CAPSTONE of the scale-hierarchy / cascade direction: the two arenas
      (the Navier-Stokes ENERGY cascade, ShellCascadeNS.v/CascadeBoundary.v, and the renormalization-group
      COUPLING flow, RGCascadeReal.v) are ONE abstraction -- a monotone scale flow over Q with the
      Element / role-limit boundary at its closure.

   Both arenas are MONOTONE SCALE PROCESSES f : nat -> Q:
     -- NS energy arena: the truncated enstrophy Omega_N = total_ns_enstrophy a N is NON-DECREASING
        (enstrophy_monotone).  Its closure (N -> infinity) is bounded (Element / regular) or unbounded
        (role-limit / the alpha=2 wall) -- undecided.
     -- RG coupling arena, sub-critical (0<=t<=1): the flow rg_iterate t n is NON-INCREASING toward the
        trivial fixed point 0 -- convergent (Element).
     -- RG coupling arena, super-critical (t>=1): the flow rg_iterate t n is NON-DECREASING -- runs away
        (role-limit / the continuum limit).

   THE UNIFICATION.  In BOTH arenas the Element / role-limit boundary is the SAME object: the CLOSURE of a
   monotone scale flow -- bounded/convergent = Element, runaway = role-limit.  The NS alpha=2 wall and the
   RG continuum limit are the same kind of role-limit (the closure of a monotone scale process over Q).
   This is the first concrete instance of "dynamizing the ToS hierarchy": the level order, previously only
   static, now carries a monotone inter-level flow whose closure is classified by the H1 boundary.

   HONEST SCOPE.  A synthesis of two already-proved arenas under one abstraction (monotone scale flow +
   Element/role-limit closure).  It does NOT decide any closure (boundedness of the enstrophy, convergence
   of the runaway) -- those ARE the role-limits, located NOT crossed.  Level: synthesis + observation.
   See Книги/Физика/ПЛАН-Иерархии-и-Каскады.md §8 for the far-horizon vision this instantiates.

   Elements: the two scale processes (Omega_N, rg_iterate); the two FlowSides.
   Roles:    the two arenas (energy / coupling) as instances of one monotone scale flow.
   Rules:    a scale flow is monotone in its regime; the boundary = its closure (bounded=Element /
             runaway=role-limit); both arenas obey it.

   ============ E/R/R разбор ============
     Rules (L5): scale-flow монотонен; граница = замыкание (Element если сходится, role-limit если убегает).
     Roles (L4): две арены (энергия/связь) = инстансы; две стороны (ConvergentElement/RunawayRoleLimit).
     Elements  : процессы Omega_N, rg_iterate; конечны на каждом шаге; замыкание = role-limit.
   ДИАГНОСТИКА (P4): обе арены = монотонные scale-процессы; граница Element/role-limit единообразно =
   ЗАМЫКАНИЕ монотонного потока. Стена alpha=2 и континуумный предел РГ = ОДИН role-limit. Первая
   «динамизация иерархии ToS». Локализуем, не пересекаем.

   STATUS: 5 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ShellCascadeNS.
From ToS Require Import foundation.CascadeBoundary.
From ToS Require Import foundation.RGCascadeReal.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The abstraction: a monotone scale flow and its two closure sides       *)
(* ===================================================================== *)

(** A scale flow is a process over scales (one value per level). *)
Definition ScaleFlow := nat -> Q.

Definition flow_nondecreasing (f : ScaleFlow) : Prop := forall n, f n <= f (S n).
Definition flow_nonincreasing (f : ScaleFlow) : Prop := forall n, f (S n) <= f n.

(** The two sides of a scale flow's closure: Element (convergent) vs role-limit (runaway). *)
Inductive FlowSide := ConvergentElement | RunawayRoleLimit.

Lemma flow_h1_disjoint : ConvergentElement <> RunawayRoleLimit.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  The two arenas are monotone scale flows                                *)
(* ===================================================================== *)

(** NS ENERGY arena: the truncated enstrophy is a non-decreasing scale flow. *)
Lemma cascade_enstrophy_is_flow : forall a,
  flow_nondecreasing (fun N => total_ns_enstrophy a N).
Proof. intros a n. apply enstrophy_monotone. Qed.

(** RG COUPLING arena (sub-critical): the flow is non-increasing -> the trivial fixed point (Element). *)
Lemma rg_subcritical_is_flow : forall t,
  0 <= t -> t <= 1 -> flow_nonincreasing (fun n => rg_iterate t n).
Proof. intros t Ht0 Ht1 n. apply rg_sub_decreasing; assumption. Qed.

(** RG COUPLING arena (super-critical): the flow is non-decreasing -> runs away (role-limit). *)
Lemma rg_supercritical_is_flow : forall t,
  1 <= t -> flow_nondecreasing (fun n => rg_iterate t n).
Proof. intros t Ht n. apply rg_super_increasing; assumption. Qed.

(* ===================================================================== *)
(*  Capstone: two arenas, one monotone-scale-flow abstraction, one boundary *)
(* ===================================================================== *)

(** The scale-hierarchy synthesis -- the two arenas are one abstraction:
      (energy)     the NS enstrophy is a non-decreasing scale flow (closure bounded=Element / runaway=wall);
      (coupling-)  the RG sub-critical flow is non-increasing -> convergent (Element);
      (coupling+)  the RG super-critical flow is non-decreasing -> runaway (role-limit);
      (boundary)   the Element and role-limit closure sides are disjoint (H1 sorts).
    In both arenas the Element/role-limit boundary is the CLOSURE of a monotone scale flow over Q -- the
    alpha=2 wall and the RG continuum limit are the same kind of role-limit.  The level hierarchy, made
    dynamical: one inter-level flow, one finitization boundary. *)
Theorem scale_hierarchy_synthesis :
  (forall a, flow_nondecreasing (fun N => total_ns_enstrophy a N))
  /\ (forall t, 0 <= t -> t <= 1 -> flow_nonincreasing (fun n => rg_iterate t n))
  /\ (forall t, 1 <= t -> flow_nondecreasing (fun n => rg_iterate t n))
  /\ (ConvergentElement <> RunawayRoleLimit).
Proof.
  split; [exact cascade_enstrophy_is_flow |].
  split; [exact rg_subcritical_is_flow |].
  split; [exact rg_supercritical_is_flow | exact flow_h1_disjoint].
Qed.
