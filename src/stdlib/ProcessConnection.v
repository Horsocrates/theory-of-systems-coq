(* ProcessConnection.v — Connection and parallel transport *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
From ToS Require Import process.ProcessRegge.
From ToS Require Import stdlib.ReggeDictionary.
Open Scope Q_scope.

Definition transport_angle (deficit : Q) : Q := deficit.

Lemma transport_flat : transport_angle 0 == 0.
Proof. reflexivity. Qed.

Lemma transport_val5 : transport_angle (22#21) == 22 # 21.
Proof. reflexivity. Qed.

Lemma holonomy_single : loop_holonomy [22#21] == 22 # 21.
Proof. unfold loop_holonomy. simpl. lra. Qed.

Lemma holonomy_two : loop_holonomy [22#21; 22#21] == 44 # 21.
Proof. unfold loop_holonomy. simpl. lra. Qed.

Lemma holonomy_flat_loop : loop_holonomy [0; 0; 0] == 0.
Proof. unfold loop_holonomy. simpl. lra. Qed.

Lemma deviation_positive_curvature :
  0 < geodesic_deviation (22#21) 1.
Proof. unfold geodesic_deviation. lra. Qed.

Theorem connection_foundation :
  transport_angle 0 == 0 /\
  loop_holonomy [0; 0; 0] == 0 /\
  0 < geodesic_deviation (22#21) 1.
Proof.
  split; [|split].
  - exact transport_flat.
  - exact holonomy_flat_loop.
  - exact deviation_positive_curvature.
Qed.

Definition connection_count := 7%nat.
