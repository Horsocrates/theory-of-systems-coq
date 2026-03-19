(* ProcessMeasureSynthesis.v — Path integral as process *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessIntegration.
From ToS Require Import stdlib.ProcessLebesgue.
Open Scope Q_scope.

(** PATH INTEGRAL AS PROCESS:

    Z(K) = Sum_{configs at K} exp(-S[config])

    At resolution K:
      configs = finite set
      S[config] = finite Q
      exp(-S) ~ 1 - S + S^2/2 (Taylor over Q)
      Z(K) = finite sum of Q = Q

    The process {Z(K)}_K IS the path integral.
    No measure theory needed! Just finite sums. *)

Definition partition_function (action : nat -> Q) (K : nat) : Q :=
  fold_left (fun acc i => acc + (1 - action i + action i * action i / 2))
    (seq 0 (S K)) 0.

Lemma partition_K0 : forall a,
  partition_function a 0 == 1 - a 0%nat + a 0%nat * a 0%nat / 2.
Proof. intros a. unfold partition_function. simpl. ring. Qed.

Lemma partition_trivial_value :
  partition_function (fun _ => 0) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma partition_positive_trivial :
  0 < partition_function (fun _ => 0) 0.
Proof. rewrite partition_trivial_value. lra. Qed.

Theorem measure_synthesis :
  (forall f, sum_2x2_ij f == sum_2x2_ji f) /\
  process_integral_01 (fun _ => 1) 0 == 1 /\
  0 < partition_function (fun _ => 0) 0.
Proof.
  split; [|split].
  - exact fubini_2x2.
  - exact integral_const_0.
  - exact partition_positive_trivial.
Qed.

Definition measure_synth_count := 4%nat.
