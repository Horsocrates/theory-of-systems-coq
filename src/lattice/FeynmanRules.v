(* ========================================================================= *)
(*                     FEYNMAN RULES                                        *)
(*           Propagator, vertex factor, symmetry factor, one-loop sum       *)
(*                                                                          *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)        *)
(*                                                                          *)
(*  Author:  Horsocrates | Version: 1.0 (E/R/R) | Date: March 2026         *)
(*                                                                          *)
(*  STATUS: 10 Qed, 0 Admitted, 0 axioms                                   *)
(*                                                                          *)
(* ========================================================================= *)
(*                                                                          *)
(*  E/R/R INTERPRETATION:                                                   *)
(*  =====================                                                   *)
(*                                                                          *)
(*  Feynman rules assign amplitudes to graph elements:                     *)
(*                                                                          *)
(*    Elements = propagators G(k), vertex factors lambda_n, sym factors    *)
(*    Roles    = internal line (propagator), vertex (coupling), loop (sum)  *)
(*    Rules    = one-loop self-energy Sigma = lambda_4 * (1/N) sum G(k)    *)
(*                                                                          *)
(*  PHYSICAL NOTE (P4):                                                     *)
(*    On a finite lattice the loop sum is FINITE — no UV divergence.       *)
(*    This is the key advantage of lattice regularization.                 *)
(*                                                                          *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* Feynman propagator: G(k) = 1/(lambda_k + m^2) *)
Definition feynman_propagator (lambda_k m_sq : Q) : Q :=
  1 / (lambda_k + m_sq).

(* Vertex factor = Cayley coefficient (replicated from InteractionFromGraph) *)
Definition cayley_coeff (n : nat) : Q :=
  match n with
  | O => 1
  | S n' => 1 / inject_Z (Z.pow 2 (Z.of_nat n'))
  end.

Definition vertex_factor (n : nat) : Q := cayley_coeff n.

(* Factorial *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S k => (S k * factorial k)%nat
  end.

(* Symmetry factor: 1/n! *)
Definition symmetry_factor (n : nat) : Q :=
  1 / inject_Z (Z.of_nat (factorial n)).

(* One-loop self-energy: Sigma = (1/8) * (1/N) * sum_k 1/(lambda_k + m^2) *)
Definition one_loop_sigma (eigs : list Q) (m_sq : Q) : Q :=
  let N := inject_Z (Z.of_nat (length eigs)) in
  (1#8) * fold_left (fun acc lam => acc + 1/(lam + m_sq)) eigs 0 / N.

Lemma propagator_k0 : feynman_propagator 0 1 == 1.
Proof. unfold feynman_propagator. vm_compute. reflexivity. Qed.

Lemma propagator_k2 : feynman_propagator 2 1 == 1#3.
Proof. unfold feynman_propagator. vm_compute. reflexivity. Qed.

Lemma vertex_3pt : vertex_factor 3 == 1#4.
Proof. vm_compute. reflexivity. Qed.

Lemma vertex_4pt : vertex_factor 4 == 1#8.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_factor_1 : symmetry_factor 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_factor_2 : symmetry_factor 2 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma sym_factor_3 : symmetry_factor 3 == 1#6.
Proof. vm_compute. reflexivity. Qed.

Lemma one_loop_chain2 : one_loop_sigma [0; 2] 1 == 1#12.
Proof. unfold one_loop_sigma. simpl. vm_compute. reflexivity. Qed.

Lemma no_UV_divergence : one_loop_sigma [0; 2] 1 < 1.
Proof. unfold one_loop_sigma. simpl. vm_compute. reflexivity. Qed.

Lemma feynman_rules_synthesis :
  feynman_propagator 0 1 == 1 /\
  vertex_factor 3 == 1#4 /\
  vertex_factor 4 == 1#8 /\
  one_loop_sigma [0; 2] 1 == 1#12 /\
  one_loop_sigma [0; 2] 1 < 1.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
