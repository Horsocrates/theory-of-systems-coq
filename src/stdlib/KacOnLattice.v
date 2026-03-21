(** * KacOnLattice.v -- "Can you hear the shape of the lattice?"
    Elements: M_upper, M_lower, isospectral pair
    Roles:    Same trace process (spectrum), different Green's functions (shape)
    Rules:    Trace determines eigenvalues, full G determines matrix
    Status:   Stdlib
    STATUS: 10 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.GreenFunction.

Open Scope Q_scope.

(* ================================================================== *)
(*  ISOSPECTRAL PAIR: same trace, different structure                   *)
(* ================================================================== *)

(** M₁ = [[2,1],[0,1]]: upper triangular, eigenvalues {2,1} *)
Definition M_upper : Mat2 := fun i j =>
  match i, j with
  | O, O => 2 | O, S O => 1 | S O, S O => 1 | _, _ => 0
  end.

(** M₂ = [[1,0],[1,2]]: lower triangular, eigenvalues {1,2} *)
Definition M_lower : Mat2 := fun i j =>
  match i, j with
  | O, O => 1 | S O, O => 1 | S O, S O => 2 | _, _ => 0
  end.

(** Same trace at K=1: tr = 3 *)
Lemma same_trace_1 : trace_process M_upper 1 == trace_process M_lower 1.
Proof. vm_compute. reflexivity. Qed.

(** Same trace at K=2: tr = 5 *)
Lemma same_trace_2 : trace_process M_upper 2 == trace_process M_lower 2.
Proof. vm_compute. reflexivity. Qed.

(** Same trace at K=3: tr(M₁³) = tr(M₂³) *)
Lemma same_trace_3 : trace_process M_upper 3 == trace_process M_lower 3.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  DIFFERENT GREEN'S FUNCTIONS                                        *)
(* ================================================================== *)

(** G_{01}(1) differs: M_upper has edge 0→1, M_lower doesn't *)
Lemma green_upper_01 : green M_upper 0%nat 1%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma green_lower_01 : green M_lower 0%nat 1%nat 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** G_{10}(1) differs the other way *)
Lemma green_upper_10 : green M_upper 1%nat 0%nat 1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma green_lower_10 : green M_lower 1%nat 0%nat 1 == 1.
Proof. vm_compute. reflexivity. Qed.

(** The off-diagonal Green's functions distinguish the matrices *)
Lemma different_green_01 :
  ~ (green M_upper 0%nat 1%nat 1 == green M_lower 0%nat 1%nat 1).
Proof.
  rewrite green_upper_01, green_lower_01.
  unfold Qeq. simpl. lia.
Qed.

(* ================================================================== *)
(*  KAC'S ANSWER                                                       *)
(* ================================================================== *)

(** You can hear the FREQUENCIES from the trace (partition function).
    You need FULL Green's function to hear the SHAPE. *)

Theorem kac_on_lattice :
  (* Same traces (same spectrum) *)
  trace_process M_upper 1 == trace_process M_lower 1 /\
  trace_process M_upper 2 == trace_process M_lower 2 /\
  (* Different structures (different off-diagonal Green's function) *)
  ~ (green M_upper 0%nat 1%nat 1 == green M_lower 0%nat 1%nat 1).
Proof.
  split; [|split].
  - exact same_trace_1.
  - exact same_trace_2.
  - exact different_green_01.
Qed.
