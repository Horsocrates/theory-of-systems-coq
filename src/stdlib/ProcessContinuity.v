(* ProcessContinuity.v — Continuous maps on process spaces *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.ProcessSpace.
Open Scope Q_scope.

Definition ProcessMap := RealProcess -> RealProcess.

Definition process_map_lipschitz (F : ProcessMap) (L : Q) (N : nat) : Prop :=
  forall f g, process_dist (F f) (F g) N <= L * process_dist f g N.

Definition process_contraction (F : ProcessMap) (c : Q) (N : nat) : Prop :=
  0 < c /\ c < 1 /\ process_map_lipschitz F c N.

Lemma id_lipschitz : forall N,
  process_map_lipschitz (fun f => f) 1 N.
Proof. intros N f g. lra. Qed.

Lemma const_map_lipschitz : forall h N,
  process_map_lipschitz (fun _ => h) 0 N.
Proof.
  intros h N f g. rewrite process_dist_self. lra.
Qed.

Lemma zero_lipschitz : forall N,
  process_map_lipschitz (fun _ => const_process 0) 0 N.
Proof. intros. apply const_map_lipschitz. Qed.

Theorem continuity_foundation :
  (forall N, process_map_lipschitz (fun f => f) 1 N) /\
  (forall h N, process_map_lipschitz (fun _ => h) 0 N).
Proof. split; [exact id_lipschitz | exact const_map_lipschitz]. Qed.

Definition continuity_count := 5%nat.
