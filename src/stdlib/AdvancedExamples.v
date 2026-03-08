(** * AdvancedExamples.v -- Cross-Module Examples

    Theory of Systems -- Verified Standard Library (Batch 5)

    Cross-module demonstrations connecting:
    - VectorSpace + Tensor (algebraic structure)
    - ODE + ControlTheory (dynamical systems)
    - GameTheory + AuctionTheory (strategic interaction)
    - MultiAgent + Graph (distributed systems)
    - ConvexAnalysis (optimization)

    Five fixed-point application themes:
    1. Pipeline (ProcessGeneral)
    2. Bellman (ControlTheory)
    3. Picard (ODE)
    4. Nash (GameTheory)
    5. Consensus (MultiAgent)

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.

(* Import all Batch 5 modules *)
From ToS Require Import LinearAlgebra.
From ToS Require Import ProcessGeneral.
From ToS Require Import stdlib.VectorSpace.
From ToS Require Import stdlib.Tensor.
From ToS Require Import stdlib.ODE.
From ToS Require Import stdlib.ConvexAnalysis.
From ToS Require Import stdlib.GameTheory.
From ToS Require Import stdlib.AuctionTheory.
From ToS Require Import stdlib.ControlTheory.
From ToS Require Import stdlib.MultiAgent.

(* ================================================================= *)
(** ** Section 1: ODE -- Concrete Euler computations                   *)
(* ================================================================= *)

(** Theorem 1: Three steps of the constant ODE f(t,x)=1, x0=0, h=1/10.
    Using euler_constant_explicit from ODE.v: x_n = x0 + n*h*c.
    At n=3: x_3 = 0 + 3*(1/10)*1 = 3/10. *)
Theorem euler_constant_step3 :
  euler_steps ode_constant_1 3%nat == 3#10.
Proof.
  unfold ode_constant_1. simpl. ring.
Qed.

(* ================================================================= *)
(** ** Section 2: GameTheory -- Prisoner's Dilemma structure            *)
(* ================================================================= *)

(** Theorem 2: The Prisoner's Dilemma exhibits the classic tension:
    mutual defection is a Nash equilibrium but is NOT Pareto optimal.
    This combines pd_defect_is_nash and pd_defect_not_pareto into a
    single cross-cutting statement. *)
Theorem pd_dilemma_tension :
  is_nash prisoners_dilemma pd_defect /\
  ~ pareto_optimal prisoners_dilemma pd_defect.
Proof.
  split.
  - exact pd_defect_is_nash.
  - exact pd_defect_not_pareto.
Qed.

(* ================================================================= *)
(** ** Section 3: MultiAgent -- Uniform consensus under averaging      *)
(* ================================================================= *)

(** Theorem 3: A uniform state is a fixed point of two_agent_avg:
    if all agents have value c, averaging yields c for agents 0 and 1. *)
Theorem uniform_consensus_avg : forall (c : Q),
  two_agent_avg (uniform_state c) 0%nat == c /\
  two_agent_avg (uniform_state c) 1%nat == c.
Proof.
  intros c. unfold two_agent_avg, uniform_state. simpl. split; lra.
Qed.

(* ================================================================= *)
(** ** Section 4: ConvexAnalysis -- Sum of quadratics                   *)
(* ================================================================= *)

(** Theorem 4: The sum of two quadratics with nonneg coefficients is convex.
    Uses quadratic_convex_nonneg_coeff and sum_of_convex from ConvexAnalysis.v. *)
Theorem quadratic_sum_convex : forall a b,
  0 <= a -> 0 <= b ->
  convex_function (fun x => a * x * x + b * x * x) all_Q.
Proof.
  intros a b Ha Hb.
  apply sum_of_convex.
  - apply quadratic_convex_nonneg_coeff. exact Ha.
  - apply quadratic_convex_nonneg_coeff. exact Hb.
Qed.

(* ================================================================= *)
(** ** Section 5: ODE -- Zero-rhs stays at initial condition           *)
(* ================================================================= *)

(** Theorem 5: A constant-zero Lipschitz ODE (f=0) keeps the Euler
    trajectory at x0 for all n. Combines constant_f_lipschitz (the rhs
    is Lipschitz with L=0) and euler_steps_zero_rhs (trajectory stays). *)
Theorem constant_zero_lipschitz_stays :
  lipschitz_in_x (fun _ _ : Q => 0) 0 /\
  forall x0 h n,
    let sys := mkODE (fun _ _ => 0) x0 h in
    euler_steps sys n == x0.
Proof.
  split.
  - exact (constant_f_lipschitz 0).
  - intros x0 h n. apply euler_steps_zero_rhs.
Qed.

(* ================================================================= *)
(** ** Section 6: ControlTheory -- 2-step scalar LTI computation       *)
(* ================================================================= *)

(** Theorem 6: For the system sys_half (a=1/2, b=0) with zero input
    and initial condition x0, the state at step 2 is (1/4)*x0.
    Uses scalar_half_zero_input_2 from ControlTheory.v. *)
Theorem scalar_lti_step_2_concrete : forall x0,
  scalar_zero_input sys_half x0 2%nat == (1#4) * x0.
Proof.
  intros x0. apply scalar_half_zero_input_2.
Qed.

(* ================================================================= *)
(** ** Section 7: ProcessGeneral -- Euler as GenProcess                 *)
(* ================================================================= *)

(** Theorem 7: The euler_process wrapping is faithful: it returns
    exactly the same value as euler_steps at every step, i.e.,
    it IS a GenProcess. This is a typing/wrapping verification. *)
Theorem euler_process_faithful : forall sys n,
  euler_process sys n = euler_steps sys n.
Proof.
  intros sys n. reflexivity.
Qed.

(* ================================================================= *)
(** ** Section 8: ProcessGeneral -- scalar LTI as GenProcess            *)
(* ================================================================= *)

(** Theorem 8: scalar_process wrapping is faithful: it agrees with
    scalar_evolve at every step. *)
Theorem scalar_lti_process_faithful : forall sys x0 u t,
  scalar_process sys x0 u t = scalar_evolve sys x0 u t.
Proof.
  intros sys x0 u t. reflexivity.
Qed.

(* ================================================================= *)
(** ** Section 9: MultiAgent -- Consensus after averaging              *)
(* ================================================================= *)

(** Theorem 9: After a two_agent_avg step, agents 0 and 1 have
    the same value. This directly witnesses is_consensus. *)
Theorem consensus_after_avg : forall (s : AgentState),
  two_agent_avg s 0%nat == two_agent_avg s 1%nat.
Proof.
  intros s. unfold two_agent_avg. simpl. lra.
Qed.

(* ================================================================= *)
(** ** Section 10: ODE + ODE -- Picard matches Euler for constant ODE  *)
(* ================================================================= *)

(** Theorem 10: For a constant ODE f(t,x) = c with step size h,
    the Picard iterate at t=h equals the Euler step-1 value.
    Picard: x0 + c*h.  Euler step 1: x0 + h*c. They agree. *)
Theorem picard_const_matches_euler_step1 : forall x0 h c,
  let sys := mkODE (fun _ _ => c) x0 h in
  picard_step_const x0 c h == euler_steps sys 1%nat.
Proof.
  intros x0 h c. unfold picard_step_const, euler_steps, euler_time. simpl. ring.
Qed.

(* ================================================================= *)
(** ** Section 11: AuctionTheory -- 2-bidder Vickrey concrete           *)
(* ================================================================= *)

(** Theorem 11: In a 2-bidder Vickrey auction with bids [10; 7],
    the winner is bidder 0 (highest bidder) and the payment is 7
    (second-highest bid). *)
Theorem vickrey_2bidders_10_7 :
  winner [10; 7] = 0%nat /\
  second_price_payment [10; 7] == 7.
Proof.
  split.
  - (* winner *)
    unfold winner, max_bid_idx. simpl.
    destruct (Qlt_le_dec 10 7) as [Hlt | Hle].
    + lra.
    + reflexivity.
  - (* payment *)
    unfold second_price_payment.
    assert (Hw : winner [10; 7] = 0%nat).
    { unfold winner, max_bid_idx. simpl.
      destruct (Qlt_le_dec 10 7) as [Hlt | Hle]; [lra | reflexivity]. }
    rewrite Hw.
    unfold max_excluding. simpl.
    destruct (Qlt_le_dec 0 7) as [Hlt | Hle].
    + reflexivity.
    + lra.
Qed.

(* ================================================================= *)
(** ** Section 12: Tensor -- Trace of 1x1 matrix                       *)
(* ================================================================= *)

(** Theorem 12: The trace of a 1x1 matrix [[x]] is x.
    Uses trace_singleton from Tensor.v. *)
Theorem trace_1x1_is_element : forall x,
  trace_raw [[x]] == x.
Proof.
  intros x. apply trace_singleton.
Qed.

(* ================================================================= *)
(** ** Section 13: ControlTheory + ODE -- Euler and LTI agree          *)
(* ================================================================= *)

(** Theorem 13: For a scalar LTI system x_{k+1} = a*x_k (b=0, u=0),
    the evolution at step 1 equals a*x0, which matches the Euler step
    for ODE f(t,x) = (a-1)*x/h with step size h when h=1. Concretely
    for a=1/2: LTI step 1 = (1/2)*x0, Euler step 1 with f(t,x) =
    -(1/2)*x and h=1 also yields (1/2)*x0. *)
Theorem lti_euler_agreement_step1 : forall x0,
  scalar_zero_input sys_half x0 1%nat ==
  euler_steps (mkODE (fun _ x => -(1#2) * x) x0 1) 1%nat.
Proof.
  intros x0.
  unfold scalar_zero_input, sys_half. simpl. ring.
Qed.

(* ================================================================= *)
(** ** Summary                                                         *)
(* ================================================================= *)

(**
  PROVEN (13 Qed):

  1.  euler_constant_step3          -- ODE: 3 steps of constant ODE
  2.  pd_dilemma_tension            -- GameTheory: Nash + not Pareto
  3.  uniform_consensus_avg         -- MultiAgent: uniform fixed point
  4.  quadratic_sum_convex          -- ConvexAnalysis: sum of quadratics
  5.  constant_zero_lipschitz_stays -- ODE: Lipschitz + zero-rhs stays
  6.  scalar_lti_step_2_concrete   -- ControlTheory: 2-step concrete
  7.  euler_process_faithful        -- ProcessGeneral + ODE wrapping
  8.  scalar_lti_process_faithful   -- ProcessGeneral + ControlTheory
  9.  consensus_after_avg           -- MultiAgent: post-avg agreement
  10. picard_const_matches_euler_step1 -- ODE: Picard = Euler for const
  11. vickrey_2bidders_10_7         -- AuctionTheory: concrete Vickrey
  12. trace_1x1_is_element          -- Tensor: trace of 1x1 matrix
  13. lti_euler_agreement_step1     -- ControlTheory + ODE agreement

  Cross-module connections demonstrated:
  - ODE.v <-> ControlTheory.v (dynamical systems)
  - ODE.v <-> ProcessGeneral.v (GenProcess wrapping)
  - ControlTheory.v <-> ProcessGeneral.v (GenProcess wrapping)
  - GameTheory.v (Nash + Pareto interaction)
  - AuctionTheory.v (concrete Vickrey computation)
  - MultiAgent.v (consensus + averaging)
  - ConvexAnalysis.v (sum of convex functions)
  - Tensor.v (trace computation)
  - VectorSpace.v (imported, available for further examples)

  AXIOMS: 0 (all proofs constructive)
*)

(** TOTAL: 13 Qed, 0 Admitted, 0 axioms *)
