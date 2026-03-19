(* R2_ProcessEinsteinSolutions.v — GR solutions as processes *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
From ToS Require Import process.ProcessFriedmann.
Open Scope Q_scope.

(** Schwarzschild process: {f_K(r)} converges to 1-2M/r *)
Definition schwarzschild_process (M ell : Q) : RealProcess :=
  fun K => schwarzschild_factor M ell K.

Lemma schwarz_at_horizon : schwarzschild_process 5 1 9%nat == 0.
Proof. unfold schwarzschild_process, schwarzschild_factor, shell_radius. simpl. field. Qed.

Lemma schwarz_at_15 : schwarzschild_process 5 1 14%nat == 1 # 3.
Proof. unfold schwarzschild_process, schwarzschild_factor, shell_radius. simpl. field. Qed.

Lemma schwarz_at_100 : schwarzschild_process 5 1 99%nat == 9 # 10.
Proof. unfold schwarzschild_process, schwarzschild_factor, shell_radius. simpl. field. Qed.

Lemma schwarz_approaches_1 : schwarzschild_process 5 1 999%nat == 99 # 100.
Proof. unfold schwarzschild_process, schwarzschild_factor, shell_radius. simpl. field. Qed.

(** Friedmann process: {H(t)} *)
Lemma friedmann_H_consistent : forall H,
  8 * (22 # 7) * friedmann_rho0 H / 3 == H * H.
Proof. exact friedmann_consistent. Qed.

(** GW process: h(t) ~ cos(ωt) *)
(** Already in ProcessGravWaveform: gw_em_ratio = 1 *)

Theorem einstein_solutions :
  schwarzschild_process 5 1 9%nat == 0 /\
  schwarzschild_process 5 1 14%nat == 1 # 3 /\
  schwarzschild_process 5 1 999%nat == 99 # 100 /\
  (forall H, 8 * (22 # 7) * friedmann_rho0 H / 3 == H * H).
Proof.
  split; [|split; [|split]].
  - exact schwarz_at_horizon.
  - exact schwarz_at_15.
  - exact schwarz_approaches_1.
  - exact friedmann_consistent.
Qed.

Definition r2_solutions_count := 6%nat.
