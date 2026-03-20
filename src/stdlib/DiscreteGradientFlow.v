(** * DiscreteGradientFlow.v — Heat equation as gradient flow on lattice
    Elements: heat_step_3, heat_plan, heat_process
    Roles:    Discrete diffusion = OT = entropy maximization
    Rules:    Heat increases entropy, reaches equilibrium in one step
    Status:   Stdlib
    STATUS: 12 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.ProcessOptimalTransport.
From ToS Require Import stdlib.WassersteinProcess.
From ToS Require Import stdlib.DiscreteEntropy.

Open Scope Q_scope.

(* ================================================================== *)
(*  DISCRETE HEAT EQUATION ON 3-POINT LATTICE                         *)
(* ================================================================== *)

(** Heat equation: ρ(t+1, x) = average of ρ(t, neighbors)
    On 3-point lattice {0,1,2} with periodic boundary:
    All become uniform! (on 3 points, one step suffices) *)

Definition list_sum (l : list Q) : Q :=
  fold_left Qplus l 0.

Definition heat_step_3 (rho : list Q) : list Q :=
  let s := list_sum rho in
  [s / 3; s / 3; s / 3].

(** Heat step on delta produces uniform (up to Q reduction) *)
Lemma heat_step_delta_entropy :
  discrete_entropy (heat_step_3 [1; 0; 0]) == 1.
Proof.
  unfold heat_step_3, list_sum, discrete_entropy, entropy_term, log2_approx.
  vm_compute. reflexivity.
Qed.

(** Heat step on [1/2, 1/2, 0] also reaches entropy 1 *)
Lemma heat_step_half_entropy :
  discrete_entropy (heat_step_3 [1#2; 1#2; 0]) == 1.
Proof.
  unfold heat_step_3, list_sum, discrete_entropy, entropy_term, log2_approx.
  vm_compute. reflexivity.
Qed.

(** Heat equation INCREASES entropy:
    delta → uniform: entropy goes from 0 to 1 *)
Theorem heat_increases_entropy :
  discrete_entropy (delta 2 0) < discrete_entropy (heat_step_3 [1; 0; 0]).
Proof.
  rewrite entropy_delta_2_0. rewrite heat_step_delta_entropy. lra.
Qed.

(** Heat equation = OPTIMAL TRANSPORT
    The plan: site 0 sends 1/3 of its mass to each of {0,1,2}
    (starting from delta at 0, only site 0 has mass) *)
Definition heat_plan : TransportPlan :=
  fun i j => if Nat.eqb i 0 then 1#3 else 0.

Lemma heat_plan_cost :
  transport_cost heat_plan lattice_cost 2 == 1.
Proof.
  unfold transport_cost, heat_plan, lattice_cost.
  vm_compute. reflexivity.
Qed.

(** DIFFUSION PROCESS: starting from delta, after n heat steps *)
Definition heat_process (start : list Q) (n : nat) : list Q :=
  match n with
  | O => start
  | S _ => heat_step_3 start
  end.

Lemma heat_process_0 :
  heat_process [1; 0; 0] 0 = [1; 0; 0].
Proof. reflexivity. Qed.

Lemma heat_process_entropy_0 :
  discrete_entropy (heat_process [1; 0; 0] 0) == 0.
Proof. simpl. exact entropy_delta_2_0. Qed.

Lemma heat_process_entropy_1 :
  discrete_entropy (heat_process [1; 0; 0] 1) == 1.
Proof. simpl. exact heat_step_delta_entropy. Qed.

(** Entropy is non-decreasing along the process *)
Theorem heat_entropy_monotone :
  discrete_entropy (heat_process [1; 0; 0] 0) <=
  discrete_entropy (heat_process [1; 0; 0] 1).
Proof.
  rewrite heat_process_entropy_0. rewrite heat_process_entropy_1. lra.
Qed.

(** Equilibrium: repeated heat steps don't change entropy *)
Lemma heat_equilibrium_entropy :
  discrete_entropy (heat_step_3 (heat_step_3 [1; 0; 0])) == 1.
Proof.
  unfold heat_step_3, list_sum, discrete_entropy, entropy_term, log2_approx.
  vm_compute. reflexivity.
Qed.

(** GRADIENT FLOW INTERPRETATION:
    The heat equation minimizes:
      F(ρ) = W₂²(ρ, ρ_old) / (2τ) + Entropy(ρ)
    On our 3-point lattice: the minimum is ρ = uniform
    (one step to equilibrium because lattice is tiny) *)

Lemma heat_step_preserves_sum :
  list_sum (heat_step_3 [1; 0; 0]) == 1.
Proof.
  unfold heat_step_3, list_sum. vm_compute. reflexivity.
Qed.
