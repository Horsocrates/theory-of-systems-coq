From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import stdlib.T2_PhaseDiagram.
Open Scope Q_scope.
Definition order_parameter := polyakov_loop.
Lemma confined_phase : order_parameter 1 == 0. Proof. exact polyakov_confined. Qed.
Lemma deconfined_phase : 0 < order_parameter 4. Proof. exact polyakov_deconfined. Qed.
Definition critical_beta : Q := 2.
Lemma critical_is_boundary : order_parameter critical_beta == 0.
Proof. unfold critical_beta. exact polyakov_at_2. Qed.
Theorem bifurcation : order_parameter 1 == 0 /\ 0 < order_parameter 4 /\ order_parameter 2 == 0.
Proof. split; [|split]; [exact confined_phase|exact deconfined_phase|exact polyakov_at_2]. Qed.
Definition t2_bif_count := 4%nat.
