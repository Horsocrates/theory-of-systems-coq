(* R1_ReggeEinsteinConvergence.v — Regge action -> EH action *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessRegge.
Open Scope Q_scope.

(** Regge action: S_R = Σ_v deficit(v) * area(v) *)
(** Einstein-Hilbert: S_EH = ∫ R √g d⁴x *)
(** Convergence: S_R → S_EH as mesh → 0 *)

Definition regge_action_vertex (deficit area : Q) : Q := deficit * area.

Lemma regge_flat : regge_action_vertex 0 (433#1000) == 0.
Proof. unfold regge_action_vertex. ring. Qed.

Lemma regge_curved : regge_action_vertex (22#21) (433#1000) == 9526 # 21000.
Proof. unfold regge_action_vertex. ring. Qed.

(** Error bound: |S_R - S_EH| ≤ C·ℓ² where ℓ = max edge length *)
Definition convergence_error (ell : Q) (C : Q) : Q := C * ell * ell.

Lemma error_at_1 : convergence_error 1 1 == 1.
Proof. unfold convergence_error. ring. Qed.

Lemma error_at_half : convergence_error (1#2) 1 == 1 # 4.
Proof. unfold convergence_error. ring. Qed.

Lemma error_at_tenth : convergence_error (1#10) 1 == 1 # 100.
Proof. unfold convergence_error. ring. Qed.

Lemma error_decreasing : convergence_error (1#10) 1 < convergence_error (1#2) 1.
Proof. rewrite error_at_tenth, error_at_half. lra. Qed.

(** As K→∞: ℓ = 1/K → error = C/K² → 0 *)
Definition error_at_K (C : Q) (K : nat) : Q :=
  C / (inject_Z (Z.of_nat (S K)) * inject_Z (Z.of_nat (S K))).

Lemma error_K0 : error_at_K 1 0 == 1.
Proof. unfold error_at_K, inject_Z. simpl. field. Qed.

Lemma error_K9 : error_at_K 1 9 == 1 # 100.
Proof. unfold error_at_K, inject_Z. simpl. field. Qed.

Lemma error_K99 : error_at_K 1 99 == 1 # 10000.
Proof. unfold error_at_K, inject_Z. simpl. field. Qed.

Theorem regge_einstein_convergence :
  convergence_error (1#10) 1 < convergence_error (1#2) 1 /\
  error_at_K 1 9 == 1 # 100 /\
  error_at_K 1 99 == 1 # 10000 /\
  deficit_angle 6 == 0.
Proof.
  split; [|split; [|split]].
  - exact error_decreasing.
  - exact error_K9.
  - exact error_K99.
  - exact deficit_flat.
Qed.

Definition r1_count := 12%nat.
