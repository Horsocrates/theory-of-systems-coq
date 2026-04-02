(** * BigBangProcess.v -- Big bang as first graph distinction
    Elements: initial graph (2 vertices), initial energy/density
    Roles:    big bang = first distinction; no singularity
    Rules:    finite initial density; arrow of time from growth
    STATUS:   8 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: April 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(*  DEFINITIONS                                                      *)
(* ================================================================ *)

(** Initial graph: the minimum distinction (2 vertices, 1 edge) *)
Definition initial_graph_size : nat := 2%nat.

(** Initial vacuum energy: E_vac = 1/2 per mode, C_2 has 2 modes *)
Definition initial_energy : Q := 1.

(** Initial density: energy / vertices *)
Definition initial_density : Q :=
  initial_energy / inject_Z (Z.of_nat initial_graph_size).

(** Density at time N *)
Definition density_at (E : Q) (N : nat) : Q :=
  E / inject_Z (Z.of_nat N).

(** Entropy proxy: number of modes = number of vertices *)
Definition entropy_proxy (N : nat) : nat := N.

(* ================================================================ *)
(*  THEOREM 1: No singularity -- initial density is finite           *)
(* ================================================================ *)

Theorem no_singularity :
  initial_density == 1 # 2.
Proof.
  unfold initial_density, initial_energy, initial_graph_size. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 2: Big bang is first distinction (N=2)                   *)
(* ================================================================ *)

Theorem big_bang_is_first_distinction :
  initial_graph_size = 2%nat.
Proof.
  unfold initial_graph_size. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 3: Initial density is positive                           *)
(* ================================================================ *)

Theorem initial_density_positive :
  initial_density > 0.
Proof.
  unfold initial_density, initial_energy, initial_graph_size. simpl.
  vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 4: Density decreases with expansion (fixed energy)       *)
(* ================================================================ *)

Theorem density_decreases :
  density_at 1 2%nat > density_at 1 10%nat.
Proof.
  unfold density_at. simpl. vm_compute. reflexivity.
Qed.

(* ================================================================ *)
(*  THEOREM 5: Entropy (modes) increases with expansion              *)
(* ================================================================ *)

Theorem entropy_increases :
  (entropy_proxy 10%nat > entropy_proxy 2%nat)%nat.
Proof.
  unfold entropy_proxy. lia.
Qed.

(* ================================================================ *)
(*  THEOREM 6: Arrow of time from monotone growth                    *)
(* ================================================================ *)

Theorem arrow_from_growth :
  forall N : nat, (entropy_proxy (S N) > entropy_proxy N)%nat.
Proof.
  intro N. unfold entropy_proxy. lia.
Qed.

(* ================================================================ *)
(*  THEOREM 7: Initial energy finite                                 *)
(* ================================================================ *)

Theorem initial_energy_finite :
  initial_energy == 1.
Proof.
  unfold initial_energy. reflexivity.
Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem big_bang_process_synthesis :
  (* No singularity *)
  initial_density == 1 # 2 /\
  (* First distinction *)
  initial_graph_size = 2%nat /\
  (* Density positive *)
  initial_density > 0 /\
  (* Density decreases *)
  density_at 1 2%nat > density_at 1 10%nat /\
  (* Entropy increases *)
  (entropy_proxy 10%nat > entropy_proxy 2%nat)%nat.
Proof.
  split. { exact no_singularity. }
  split. { exact big_bang_is_first_distinction. }
  split. { exact initial_density_positive. }
  split. { exact density_decreases. }
  exact entropy_increases.
Qed.
