(* ProcessHilbert.v *)
(* Process Hilbert Space: States as Lists over Q *)
(* E: PState = list Q, inner product, Born probabilities *)
(* R: Structural role — quantum states as rational vectors *)
(* R: Norm, orthogonality, Born rule, embedding preservation *)

From Stdlib Require Import QArith Qabs List.
Import ListNotations.
Open Scope Q_scope.

(** Process State = list of rational amplitudes *)
Definition PState := list Q.

(** Inner product: recursive dot product *)
Fixpoint inner (psi phi : PState) : Q :=
  match psi, phi with
  | a :: psi', b :: phi' => a * b + inner psi' phi'
  | _, _ => 0
  end.

(** Norm squared *)
Definition norm_sq (psi : PState) : Q := inner psi psi.

(** Standard basis states *)
Definition ket_0 : PState := [1; 0].
Definition ket_1 : PState := [0; 1].
Definition ket_plus : PState := [1; 1].

(** Born probability: |<a|psi>|^2 / <psi|psi> *)
Definition born_prob (a psi : PState) : Q :=
  (inner a psi) * (inner a psi) / norm_sq psi.

(** Embedding: extend to higher dimension by appending 0 *)
Definition embed (psi : PState) : PState := psi ++ [0].

(** ---- Basic inner product lemmas ---- *)

Lemma inner_00 : inner ket_0 ket_0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma inner_11 : inner ket_1 ket_1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma inner_01 : inner ket_0 ket_1 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma inner_plus_0 : inner ket_plus ket_0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma inner_plus_plus : inner ket_plus ket_plus == 2.
Proof. vm_compute. reflexivity. Qed.

(** ---- Born rule ---- *)

Lemma born_plus_0 : born_prob ket_0 ket_plus == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma born_plus_1 : born_prob ket_1 ket_plus == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma born_total : born_prob ket_0 ket_plus + born_prob ket_1 ket_plus == 1.
Proof. vm_compute. reflexivity. Qed.

(** ---- Embedding ---- *)

Lemma embed_ket_0 : embed ket_0 = [1; 0; 0].
Proof. reflexivity. Qed.

Lemma embed_ket_1 : embed ket_1 = [0; 1; 0].
Proof. reflexivity. Qed.

Lemma inner_nil_r : forall psi, inner psi [] == 0.
Proof.
  induction psi as [|a psi' IH].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Lemma inner_nil_l : forall phi, inner [] phi == 0.
Proof. destruct phi; reflexivity. Qed.

Lemma inner_app_zero : forall psi phi,
  inner (psi ++ [0]) (phi ++ [0]) == inner psi phi.
Proof.
  induction psi as [|a psi' IH].
  - intros phi. simpl. destruct phi as [|b phi'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros phi. destruct phi as [|b phi'].
    + simpl. ring_simplify. apply inner_nil_r.
    + simpl. rewrite IH. ring.
Qed.

Lemma embed_preserves_inner : forall psi phi,
  inner (embed psi) (embed phi) == inner psi phi.
Proof. intros. unfold embed. apply inner_app_zero. Qed.

Lemma embed_preserves_norm : forall psi,
  norm_sq (embed psi) == norm_sq psi.
Proof. intros. unfold norm_sq. apply embed_preserves_inner. Qed.

(** ---- Qutrit states ---- *)

Definition ket_0_3 : PState := [1; 0; 0].
Definition ket_1_3 : PState := [0; 1; 0].
Definition ket_2_3 : PState := [0; 0; 1].
Definition ghz_3 : PState := [1; 0; 1].

Lemma qutrit_orthogonal : inner ket_0_3 ket_1_3 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ghz_norm : norm_sq ghz_3 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma ghz_born_0 : born_prob ket_0_3 ghz_3 == (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma ghz_born_1 : born_prob ket_1_3 ghz_3 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma ghz_born_2 : born_prob ket_2_3 ghz_3 == (1#2).
Proof. vm_compute. reflexivity. Qed.

(** Synthesis *)
Theorem process_hilbert_synthesis :
  inner ket_0 ket_1 == 0 /\
  born_prob ket_0 ket_plus + born_prob ket_1 ket_plus == 1 /\
  (forall psi phi, inner (embed psi) (embed phi) == inner psi phi) /\
  norm_sq ghz_3 == 2.
Proof.
  split. exact inner_01.
  split. exact born_total.
  split. exact embed_preserves_inner.
  exact ghz_norm.
Qed.
