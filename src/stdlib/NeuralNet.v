(** * NeuralNet.v -- Simple Neural Networks as ToS Systems

    Theory of Systems -- Verified Standard Library (Batch 6)

    Elements: weights (list Q), biases (Q), activations (Q)
    Roles:    weight -> Connection, bias -> Offset, activation -> Gate
    Rules:    affine transform + ReLU (constitution), forward propagation
    Status:   active | inactive | saturated | dead

    Connection: PInterval_CROWN.v -- relu verification
    Connection: Statistics.v -- weighted_sum for neuron computation

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Require Import Coq.micromega.Lqa.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import stdlib.Statistics.

(* ========================================================================= *)
(* CORE DEFINITIONS                                                          *)
(* ========================================================================= *)

(** ReLU activation: max(0, x) *)
Definition relu (x : Q) : Q := Qmax 0 x.

(** Linear neuron: weighted_sum(inputs, weights) + bias *)
Definition neuron_linear (weights : list Q) (inputs : list Q) (bias : Q) : Q :=
  weighted_sum inputs weights + bias.

(** ReLU neuron: relu(linear(weights, inputs, bias)) *)
Definition neuron_relu (weights : list Q) (inputs : list Q) (bias : Q) : Q :=
  relu (neuron_linear weights inputs bias).

(** A layer is a list of (weights, bias) pairs *)
Definition Layer := list (list Q * Q).

(** Forward pass through a layer with ReLU activation *)
Definition layer_forward (layer : Layer) (inputs : list Q) : list Q :=
  map (fun wb => neuron_relu (fst wb) inputs (snd wb)) layer.

(** Forward pass through a layer without activation (linear only) *)
Definition layer_linear (layer : Layer) (inputs : list Q) : list Q :=
  map (fun wb => neuron_linear (fst wb) inputs (snd wb)) layer.

(** Two-layer network: hidden (ReLU) -> output (linear) *)
Definition two_layer_forward (hidden output : Layer) (inputs : list Q) : list Q :=
  layer_linear output (layer_forward hidden inputs).

(** Piecewise-linear sigmoid approximation *)
Definition sigmoid_approx (x : Q) : Q :=
  if Qle_bool x (-2) then 0
  else if Qle_bool 2 x then 1
  else (1#4) * x + (1#2).

(* ========================================================================= *)
(* THEOREMS: relu                                                            *)
(* ========================================================================= *)

(** relu is always non-negative *)
Lemma relu_nonneg : forall x : Q, 0 <= relu x.
Proof.
  intro x. unfold relu. apply Q.le_max_l.
Qed.

(** relu of a non-negative value is the value itself *)
Lemma relu_pos : forall x : Q, 0 <= x -> relu x == x.
Proof.
  intros x Hx. unfold relu. apply Q.max_r. exact Hx.
Qed.

(** relu of a non-positive value is zero *)
Lemma relu_neg : forall x : Q, x <= 0 -> relu x == 0.
Proof.
  intros x Hx. unfold relu. apply Q.max_l. exact Hx.
Qed.

(** relu(0) = 0 *)
Lemma relu_zero : relu 0 == 0.
Proof.
  unfold relu. apply Q.max_l. apply Qle_refl.
Qed.

(** relu is idempotent: relu(relu(x)) = relu(x) *)
Lemma relu_idempotent : forall x : Q, relu (relu x) == relu x.
Proof.
  intro x. apply relu_pos. apply relu_nonneg.
Qed.

(* ========================================================================= *)
(* THEOREMS: neuron_linear                                                   *)
(* ========================================================================= *)

(** Linear neuron with empty weights and inputs returns bias *)
Lemma neuron_linear_nil : forall b : Q, neuron_linear [] [] b == b.
Proof.
  intro b. unfold neuron_linear. simpl. ring.
Qed.

(** Linear neuron with single weight and input *)
Lemma neuron_linear_singleton : forall w x b : Q,
  neuron_linear [w] [x] b == x * w + b.
Proof.
  intros w x b. unfold neuron_linear. simpl. ring.
Qed.

(** Linear neuron with two weights and inputs *)
Lemma neuron_linear_two : forall w1 w2 x1 x2 b : Q,
  neuron_linear [w1; w2] [x1; x2] b == x1 * w1 + x2 * w2 + b.
Proof.
  intros w1 w2 x1 x2 b. unfold neuron_linear. simpl. ring.
Qed.

(* ========================================================================= *)
(* THEOREMS: neuron_relu                                                     *)
(* ========================================================================= *)

(** ReLU neuron output is always non-negative *)
Lemma neuron_relu_nonneg : forall ws xs b,
  0 <= neuron_relu ws xs b.
Proof.
  intros ws xs b. unfold neuron_relu. apply relu_nonneg.
Qed.

(** ReLU neuron with empty weights/inputs = relu(bias) *)
Lemma neuron_relu_nil : forall b : Q, neuron_relu [] [] b == relu b.
Proof.
  intro b. unfold neuron_relu, neuron_linear. simpl.
  unfold relu.
  destruct (Q.max_spec 0 (0 + b)) as [[Hlt Hmax] | [Hle Hmax]];
  destruct (Q.max_spec 0 b) as [[Hlt2 Hmax2] | [Hle2 Hmax2]];
  rewrite Hmax; rewrite Hmax2; lra.
Qed.

(* ========================================================================= *)
(* THEOREMS: layer_forward / layer_linear                                    *)
(* ========================================================================= *)

(** Empty layer produces empty output *)
Lemma layer_forward_nil : forall inputs : list Q,
  layer_forward [] inputs = [].
Proof.
  intro inputs. unfold layer_forward. simpl. reflexivity.
Qed.

(** Layer output length equals number of neurons *)
Lemma layer_forward_length : forall (layer : Layer) (inputs : list Q),
  length (layer_forward layer inputs) = length layer.
Proof.
  intros layer inputs. unfold layer_forward. rewrite map_length. reflexivity.
Qed.

(** Linear layer output length equals number of neurons *)
Lemma layer_linear_length : forall (layer : Layer) (inputs : list Q),
  length (layer_linear layer inputs) = length layer.
Proof.
  intros layer inputs. unfold layer_linear. rewrite map_length. reflexivity.
Qed.

(* ========================================================================= *)
(* THEOREMS: two_layer_forward                                               *)
(* ========================================================================= *)

(** Two-layer network with empty hidden layer *)
Lemma two_layer_forward_nil_hidden : forall (out : Layer) (ins : list Q),
  two_layer_forward [] out ins = layer_linear out [].
Proof.
  intros out ins. unfold two_layer_forward. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* THEOREMS: sigmoid_approx                                                  *)
(* ========================================================================= *)

(** Sigmoid approximation saturates to 0 for x <= -2 *)
Lemma sigmoid_approx_low : forall x : Q,
  x <= -(2) -> sigmoid_approx x == 0.
Proof.
  intros x Hx. unfold sigmoid_approx.
  destruct (Qle_bool x (-2)) eqn:Hb.
  - lra.
  - exfalso.
    assert (Hle : Qle_bool x (-2) = true).
    { apply Qle_bool_iff. exact Hx. }
    rewrite Hle in Hb. discriminate.
Qed.

(** Sigmoid approximation saturates to 1 for x >= 2 *)
Lemma sigmoid_approx_high : forall x : Q,
  2 <= x -> sigmoid_approx x == 1.
Proof.
  intros x Hx. unfold sigmoid_approx.
  destruct (Qle_bool x (-2)) eqn:Hb1.
  - apply Qle_bool_iff in Hb1. lra.
  - destruct (Qle_bool 2 x) eqn:Hb2.
    + lra.
    + exfalso.
      assert (Hle : Qle_bool 2 x = true).
      { apply Qle_bool_iff. exact Hx. }
      rewrite Hle in Hb2. discriminate.
Qed.

(** Sigmoid approximation at 0 is 1/2 *)
Lemma sigmoid_approx_mid : sigmoid_approx 0 == 1#2.
Proof.
  unfold sigmoid_approx. simpl. lra.
Qed.

(* ========================================================================= *)
(* THEOREMS: concrete computations                                           *)
(* ========================================================================= *)

(** Concrete neuron: [1;1] inputs [2;3] bias 0 => relu(5) = 5 *)
Lemma concrete_neuron_pos :
  neuron_relu [1; 1] [2; 3] 0 == 5.
Proof.
  unfold neuron_relu, neuron_linear, relu. simpl.
  destruct (Q.max_spec 0 (2 * 1 + (3 * 1 + 0) + 0)) as [[Hlt Hmax] | [Hle Hmax]];
  rewrite Hmax; lra.
Qed.
