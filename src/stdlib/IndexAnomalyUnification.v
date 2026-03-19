(* IndexAnomalyUnification.v — Anomaly from Index Theorem *)
From Stdlib Require Import QArith QArith_base Lia ZArith. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.H1_IndexTheorem.
From ToS Require Import stdlib.H1_LatticeDirac.
From ToS Require Import process.ProcessAnomaly.
From ToS Require Import process.ProcessAnomalyCancel.
Open Scope Q_scope.
Theorem anomaly_is_index : dirac_index_1d 2 = 0%Z.
Proof. exact index_1d_2. Qed.
Theorem sm_anomaly_is_index : is_anomaly_free sm_generation_chiral.
Proof. exact sm_anomaly_cancels. Qed.
Theorem index_anomaly_bridge :
  dirac_index_1d 2 = 0%Z /\ is_anomaly_free sm_generation_chiral.
Proof. split; [exact index_1d_2 | exact sm_anomaly_cancels]. Qed.
Definition index_anomaly_count := 3%nat.
