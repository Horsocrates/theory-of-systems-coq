(** * InterLevelCalculus.v — THE FARTHEST STEP (ПЛАН-Иерархии-и-Каскады.md §8.6): the ToS level-spine,
      previously only STATIC, assembled as ONE dynamical structure -- a universal inter-level interaction
      calculus.  Every inter-level interaction this direction made dynamical (Flux, Flow, Nesting,
      Coupling) is a MONOTONE SCALE FLOW over Q, and all of them share ONE finitization boundary:
      Element at the finite truncation, role-limit at the closure.  The two directions of the hierarchy
      -- generation (up, building the hierarchy by iterating an interaction) and convergence (down, the
      FrameworkConvergence descent to the framework floor) -- are the up/down of one structure.

   THE GENUINE THEOREM (the only non-bookkeeping content, 0 axioms):
     ★ element_excludes_role_limit -- a monotone inter-level flow CANNOT be both Element (bounded, a
       convergent closure) and role-limit (unbounded, an escaping closure).  The single universal dial:
       monotone + bounded = Element; monotone + unbounded = role-limit.  This one criterion subsumes
       every arena: RG sub-critical (bounded -> Element), RG super-critical (unbounded -> role-limit),
       the NS enstrophy (bounded -> regular / unbounded -> the alpha=2 wall), the dyadic scale tower
       (unbounded -> role-limit).

   ★★ BRUTALLY HONEST SCOPE.  This is an ORGANIZING SYNTHESIS + the one dichotomy theorem -- NOT a proof
   that all inter-level interactions reduce to a single engine, and NOT a new deep result.  The registry
   of interactions is an enumeration (the actual instances are proved in their own files:
   ScaleHierarchyTransfer/ShellCascadeNS/CascadeBoundary [Flux], RGCascadeReal [Flow],
   NestedHierarchyConservation [Nesting], HierarchyLaplacian [Coupling]).  Crucially, the ACTUAL Element
   payoff -- that a monotone BOUNDED flow CONVERGES (is Cauchy) -- is the role-limit side (it needs
   `classic`, cf. MonotoneConvergence.v); so here we give only the CRITERION (bounded vs unbounded), NOT
   the convergence.  This is the край -- the level: synthesis + observation.  Located, NOT crossed.

   Elements: scale flows nat->Q; the bounded/unbounded criteria; the interaction & direction tags.
   Roles:    the four dynamical interactions (Flux/Flow/Nesting/Coupling) + their static predecessors
             (Order/Depth/Reduction/Convergence); the two sides; the two directions.
   Rules:    a monotone flow is Element (bounded) XOR role-limit (unbounded); one boundary across all
             interactions; generation (up) and convergence (down) are the two directions of the spine.

   ============ E/R/R разбор ============
     Rules (L5): монот. поток = Element (огранич) XOR role-limit (неогранич); одна граница; две направленности.
     Roles (L4): 4 динамич. взаимодействия + 4 статич. предшественника; две стороны; две направленности.
     Elements  : scale-потоки nat->Q; критерии огранич/неогранич; теги.
   ДИАГНОСТИКА (P4): спина уровней ToS сделана динамической, под одной монотонно-поточной абстракцией с
   одной границей. Генерация(вверх)+сходимость(вниз)=полная картина. ЧЕСТНО: синтез + 1 теорема-дихотомия,
   НЕ редукция к одному движку; сходимость ограниченного потока = role-limit (нужен classic) -> здесь
   только КРИТЕРИЙ. Край. Локализуем, не пересекаем.

   STATUS: 5 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Part 1: the abstraction + the one genuine universal theorem            *)
(* ===================================================================== *)

Definition ScaleFlow := nat -> Q.
Definition nondecreasing (f : ScaleFlow) : Prop := forall n, f n <= f (S n).
Definition bounded_above (f : ScaleFlow) (B : Q) : Prop := forall n, f n <= B.
Definition unbounded (f : ScaleFlow) : Prop := forall B, exists n, B < f n.

(** Element criterion: a monotone flow that is bounded above (a convergent closure). *)
Definition flow_element (f : ScaleFlow) : Prop := nondecreasing f /\ exists B, bounded_above f B.
(** role-limit criterion: a monotone flow that is unbounded (an escaping closure). *)
Definition flow_role_limit (f : ScaleFlow) : Prop := nondecreasing f /\ unbounded f.

(** ★ THE universal dichotomy: no monotone inter-level flow is both Element and role-limit.
    The single dial -- bounded = Element, unbounded = role-limit -- across every arena. *)
Theorem element_excludes_role_limit : forall f,
  flow_element f -> flow_role_limit f -> False.
Proof.
  intros f Hel Hrl.
  unfold flow_element in Hel. unfold flow_role_limit in Hrl.
  destruct Hel as [_ [B HB]]. destruct Hrl as [_ Hub].
  unfold bounded_above in HB. unfold unbounded in Hub.
  destruct (Hub B) as [n Hn]. specialize (HB n). lra.
Qed.

(** A concrete Element flow exists (the constant flow is monotone and bounded). *)
Lemma flow_element_const : forall c, flow_element (fun _ => c).
Proof.
  intro c. unfold flow_element, nondecreasing, bounded_above. split.
  - intro n. apply Qle_refl.
  - exists c. intro n. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  Part 2: the registry of inter-level interactions (organizing capstone) *)
(* ===================================================================== *)

(** The four inter-level interactions THIS direction made dynamical (each proved in its own file). *)
Inductive Interaction := Flux | Flow | Nesting | Coupling.

(** Their STATIC foundational predecessors in ToS (which they dynamize). *)
Inductive Foundational := Order | Depth | Reduction | Convergence.

(** The two sides of every interaction's finitization boundary. *)
Inductive Side := ElementExact | RoleLimitClosure.
Definition finite_side  (i : Interaction) : Side := ElementExact.
Definition closure_side (i : Interaction) : Side := RoleLimitClosure.

(** ★ One boundary across all interactions: Element at the finite truncation, role-limit at the closure. *)
Lemma every_interaction_has_boundary : forall i, finite_side i <> closure_side i.
Proof. intro i. unfold finite_side, closure_side. discriminate. Qed.

(* ===================================================================== *)
(*  Part 3: the two directions of the spine (generation up / convergence down) *)
(* ===================================================================== *)

Inductive Direction := GenerationUp | ConvergenceDown.

(** Generation (build the hierarchy upward by iterating an interaction) and convergence (the
    FrameworkConvergence descent down to the framework floor) are distinct directions of one structure. *)
Lemma directions_distinct : GenerationUp <> ConvergenceDown.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the ToS level-spine as one dynamical structure, one boundary *)
(* ===================================================================== *)

(** The universal inter-level interaction calculus:
      (★ dichotomy) no monotone inter-level flow is both Element (bounded) and role-limit (unbounded);
      (one boundary) every interaction is Element at the finite truncation, role-limit at the closure;
      (two directions) generation (up) and convergence (down) are distinct;
      (Element exists) a concrete monotone bounded flow exists.
    The ToS level-spine -- static (level order, [2,3,1] depth, the reduction atlas, FrameworkConvergence)
    -- assembled as ONE dynamical structure: monotone scale flows with ONE Element/role-limit boundary,
    traversed up by generation and down by convergence.  HONEST: an organizing synthesis + the one
    dichotomy theorem; the convergence of bounded flows (the Element payoff) is the role-limit side. *)
Theorem inter_level_calculus :
  (forall f, flow_element f -> flow_role_limit f -> False)
  /\ (forall i : Interaction, finite_side i <> closure_side i)
  /\ (GenerationUp <> ConvergenceDown)
  /\ (forall c, flow_element (fun _ => c)).
Proof.
  split; [exact element_excludes_role_limit |].
  split; [exact every_interaction_has_boundary |].
  split; [exact directions_distinct | exact flow_element_const].
Qed.
