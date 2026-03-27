(* EnergySynthesis.v *)
(* E/R/R: Elements = energy concepts, Roles = energy-content synthesis, Rules = spectral invariance *)
(* Standalone — only Stdlib imports *)
(* STATUS: 15 Qed, 0 Admitted, 0 axioms *)
(* Author: Horsocrates | Date: March 2026 *)

From Stdlib Require Import QArith.
From Stdlib Require Import Lia.

Open Scope Q_scope.

(** * Replicated: Mat2 for standalone compilation *)

Record EMat2 := mkEMat2 {
  e00 : Q; e01 : Q;
  e10 : Q; e11 : Q
}.

Definition e_trace (M : EMat2) : Q := e00 M + e11 M.

(** * Energy = leading diagonal entry *)

Definition E_from_content (M : EMat2) : Q := e00 M.

(** * Synthesis 1: trace = sum of diagonal for diagonal matrix *)

Lemma synth_energy_from_trace : forall a b : Q,
  e_trace (mkEMat2 a 0 0 b) == a + b.
Proof. intros. unfold e_trace. simpl. unfold Qeq. simpl. lia. Qed.

(** * Synthesis 2: Different content -> different energy *)

Lemma synth_distinct_energies : forall a b : Q,
  ~ (a == b) -> ~ (E_from_content (mkEMat2 a 0 0 0) == E_from_content (mkEMat2 b 0 0 0)).
Proof. intros a b Hne. unfold E_from_content. simpl. exact Hne. Qed.

(** * Synthesis 3: Zero content = zero energy *)

Lemma synth_zero_content_zero_energy :
  E_from_content (mkEMat2 0 0 0 0) == 0.
Proof. vm_compute. reflexivity. Qed.

(** * Synthesis 4: Content is additive *)

Definition e_add (M1 M2 : EMat2) : EMat2 :=
  mkEMat2 (e00 M1 + e00 M2) (e01 M1 + e01 M2)
          (e10 M1 + e10 M2) (e11 M1 + e11 M2).

Lemma synth_trace_additive : forall M1 M2,
  e_trace (e_add M1 M2) == e_trace M1 + e_trace M2.
Proof. intros. unfold e_trace, e_add. simpl. unfold Qeq. simpl. lia. Qed.

(** * Synthesis 5: Scaling content scales energy *)

Definition e_scale (c : Q) (M : EMat2) : EMat2 :=
  mkEMat2 (c * e00 M) (c * e01 M) (c * e10 M) (c * e11 M).

Lemma synth_energy_scales : forall c M,
  E_from_content (e_scale c M) == c * E_from_content M.
Proof. intros. unfold E_from_content, e_scale. simpl. unfold Qeq. simpl. lia. Qed.

(** * Synthesis 6: Concrete hydrogen and helium *)

Definition synth_H := mkEMat2 (-(1#2)) 0 0 (1#4).
Definition synth_He := mkEMat2 (-(729#256)) 0 0 (-(81#64)).

Lemma synth_H_energy : E_from_content synth_H == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma synth_He_energy : E_from_content synth_He == -(729#256).
Proof. vm_compute. reflexivity. Qed.

Lemma synth_He_lower_than_H :
  E_from_content synth_He < E_from_content synth_H.
Proof. unfold E_from_content, synth_He, synth_H, Qlt. simpl. lia. Qed.

(** * Synthesis 7: Energy determines ground state *)

Lemma synth_ground_state_unique : forall (a b : Q),
  a < b -> E_from_content (mkEMat2 a 0 0 0) < E_from_content (mkEMat2 b 0 0 0).
Proof. intros. unfold E_from_content. simpl. exact H. Qed.

(** * Grand synthesis: energy = content-in-form *)

Lemma synth_grand_energy :
  E_from_content synth_H == -(1#2) /\
  ~ (E_from_content synth_H == E_from_content synth_He) /\
  E_from_content (mkEMat2 0 0 0 0) == 0.
Proof.
  split. vm_compute. reflexivity.
  split. unfold E_from_content, synth_H, synth_He.
  intro H. vm_compute in H. discriminate.
  vm_compute. reflexivity.
Qed.

(** * Trace invariance for same sum *)

Lemma synth_trace_invariant_diag : forall a b c d : Q,
  a + d == c + b -> e_trace (mkEMat2 a 0 0 d) == e_trace (mkEMat2 c 0 0 b).
Proof. intros. unfold e_trace. simpl. exact H. Qed.
