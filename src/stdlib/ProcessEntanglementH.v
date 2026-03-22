(* ProcessEntanglementH.v *)
(* Entanglement Detection in Process Hilbert Space *)
(* E: Bell state, separability criterion, product states *)
(* R: Structural role — entanglement as non-factorizability *)
(* R: a*d != b*c detects entangled 2-qubit states *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import stdlib.ProcessHilbert.

(** Bell state |Phi+> = |00> + |11> (unnormalized) *)
Definition bell_plus : PState := [1; 0; 0; 1].

(** Product state |+>|+> = |00> + |01> + |10> + |11> *)
Definition separable_state : PState := [1; 1; 1; 1].

(** Product state |0>|1> *)
Definition product_01 : PState := [0; 1; 0; 0].

(** Separability criterion for 2-qubit state [a; b; c; d]:
    separable iff a*d == b*c (rank-1 condition on 2x2 matrix) *)
Definition is_separable (psi : PState) : Prop :=
  match psi with
  | a :: b :: c :: d :: nil => a * d == b * c
  | _ => False
  end.

(** ---- Bell state is entangled ---- *)

Lemma bell_not_separable_val :
  let a := 1 in let b := 0 in let c := 0 in let d := 1 in
  a * d == 1 /\ b * c == 0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma bell_entangled : ~ is_separable bell_plus.
Proof.
  simpl. intro H. vm_compute in H. discriminate.
Qed.

(** ---- Product states are separable ---- *)

Lemma product_separable : is_separable separable_state.
Proof. simpl. vm_compute. reflexivity. Qed.

Lemma product_01_separable : is_separable product_01.
Proof. simpl. vm_compute. reflexivity. Qed.

(** ---- Inner products of Bell state ---- *)

Lemma bell_norm : norm_sq bell_plus == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma separable_norm : norm_sq separable_state == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma bell_separable_inner : inner bell_plus separable_state == 2.
Proof. vm_compute. reflexivity. Qed.

(** ---- Entanglement detection is decidable for concrete states ---- *)

Lemma entanglement_decidable :
  ~ is_separable bell_plus /\ is_separable separable_state.
Proof.
  split. exact bell_entangled. exact product_separable.
Qed.

(** ---- Another entangled state ---- *)

Definition bell_minus : PState := [1; 0; 0; -(1)].

Lemma bell_minus_entangled : ~ is_separable bell_minus.
Proof.
  simpl. intro H. vm_compute in H. discriminate.
Qed.

(** Synthesis *)
Theorem process_entanglement_synthesis :
  ~ is_separable bell_plus /\
  is_separable separable_state /\
  norm_sq bell_plus == 2.
Proof.
  split. exact bell_entangled.
  split. exact product_separable.
  exact bell_norm.
Qed.
