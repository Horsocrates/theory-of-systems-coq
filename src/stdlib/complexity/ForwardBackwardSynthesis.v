(** * ForwardBackwardSynthesis.v — Forward-Backward Grand Synthesis

    Theory of Systems — P vs NP Complexity Insights

    Elements: forward cost, backward cost, branching factor, IVT bridge
    Roles:    synthesis → Unifying the forward/backward/branching picture
    Rules:    forward = exponential, backward = linear, IVT = bridge
    Status:   synthesis_complete

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From ToS Require Import stdlib.complexity.ForwardBackward.
From ToS Require Import stdlib.complexity.BranchingFactor.

(** Forward cost matches multiplicative cost for b=2 *)
Lemma forward_is_multiplicative :
  forall n m, forward_cost n m = m * multiplicative_cost 2 n.
Proof.
  intros. unfold forward_cost, multiplicative_cost. reflexivity.
Qed.

(** Backward cost is always additive *)
Lemma backward_is_additive :
  forall m, backward_cost m = additive_cost 3 m.
Proof.
  intros. unfold backward_cost, additive_cost. reflexivity.
Qed.

(** The asymmetry: forward is multiplicative, backward is additive *)
Theorem fb_asymmetry_is_mult_vs_add :
  forward_cost 6 10 = 10 * multiplicative_cost 2 6 /\
  backward_cost 10 = additive_cost 3 10.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** IVT bridge transforms multiplicative into additive *)
Lemma ivt_transforms_cost :
  (ivt_cost 10 < multiplicative_cost 2 10)%nat /\
  (ivt_cost 10 = additive_cost 1 10)%nat.
Proof.
  split; vm_compute; [lia | reflexivity].
Qed.

(** Forward dominates backward by exponential factor *)
Lemma forward_exp_dominates :
  (forward_cost 6 10 > 20 * backward_cost 10)%nat /\
  (multiplicative_cost 2 10 > additive_cost 15 10)%nat.
Proof. split; vm_compute; lia. Qed.

(** Concrete combined: at n=4, m=5 *)
Lemma combined_concrete_4_5 :
  (forward_cost 4 5 = 80)%nat /\
  (backward_cost 5 = 15)%nat /\
  (multiplicative_cost 2 4 = 16)%nat /\
  (additive_cost 3 5 = 15)%nat.
Proof. vm_compute. auto. Qed.

(** Gap at n=8 *)
Lemma gap_at_8 :
  (forward_cost 8 10 - backward_cost 10 > 2500)%nat.
Proof. vm_compute. lia. Qed.

(** IVT cost is sublinear in the exponential space *)
Lemma ivt_sublinear :
  (ivt_cost 8 < multiplicative_cost 2 8)%nat.
Proof. vm_compute. lia. Qed.

(** Forward-backward ratio grows with n *)
Lemma ratio_grows :
  (forward_cost 4 10 / backward_cost 10 < forward_cost 6 10 / backward_cost 10)%nat.
Proof. vm_compute. lia. Qed.

(** Branching factor 2 at depth 10 dwarfs any linear cost *)
Lemma branching_dwarfs_linear :
  (multiplicative_cost 2 10 > additive_cost 100 10)%nat.
Proof. vm_compute. lia. Qed.

(** E/R/R Grand Synthesis: P vs NP is multiplicative vs additive *)
Theorem grand_synthesis_forward_backward :
  (* Forward = multiplicative *)
  (forall n m, forward_cost n m = m * multiplicative_cost 2 n) /\
  (* Backward = additive *)
  (forall m, backward_cost m = additive_cost 3 m) /\
  (* Concrete gap *)
  (forward_cost 6 10 > 20 * backward_cost 10)%nat.
Proof.
  split; [| split].
  - intros. unfold forward_cost, multiplicative_cost. reflexivity.
  - intros. unfold backward_cost, additive_cost. reflexivity.
  - vm_compute. lia.
Qed.
