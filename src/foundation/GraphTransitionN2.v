(** * GraphTransitionN2.v — From the distinction graph to an indivisible
      stochastic transition: the case N = 2 carried through

    E/R/R reading (done before coding; audit of Part I of the Mathematics
    volume, chapter I.7, place 3, 2026-11-13):

    Elements: the two nodes of the smallest distinction graph; the weight
              theta of its single antisymmetric link.
    Roles:    the generator M_2 theta (antisymmetric matrix of the graph);
              its Cayley transform U (the orthogonal "amplitude" matrix);
              the transition matrix Gamma = |U|^2 (probabilities).
    Rules:    graph -> generator -> Cayley transform -> entrywise square.
    Proved, for EVERY rational theta:
              (1) cayley_2 theta IS the Cayley transform of M_2 theta:
                  U (I - M/2) = I + M/2;
              (2) U is orthogonal (both ways);
              (3) the transition matrix Gamma is unistochastic, hence doubly
                  stochastic;
              and for theta = 1:
              (4) the two-step transition is again unistochastic, yet it is
                  NOT the product of the one-step transitions (49/625 against
                  337/625): the process is indivisible.
    P4 diagnostic ("could it be otherwise?"): 2 x 2 matrices over Q; nothing
              infinite. Forced: (1)-(4) for N = 2. NOT claimed: the general N;
              the correspondence with Barandes' axioms as a whole — that
              correspondence is stated in prose (ConnectionClosesGap.v keeps
              it in comments); here one chain of it is carried from the graph
              to indivisibility by theorems.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.

From ToS Require Import foundation.UnistochasticFromGraph.
From ToS Require foundation.GraphUnitary.

Open Scope Q_scope.

(* ========================================================================= *)
(*  1. cayley_2 theta is the Cayley transform of the graph matrix M_2 theta  *)
(* ========================================================================= *)

Definition Id2 (i j : nat) : Q := if Nat.eqb i j then 1 else 0.

Definition I_minus_half (theta : Q) : Mat :=
  fun i j => Id2 i j - GraphUnitary.M_2 theta i j / 2.

Definition I_plus_half (theta : Q) : Mat :=
  fun i j => Id2 i j + GraphUnitary.M_2 theta i j / 2.

Theorem cayley_2_is_cayley_transform : forall theta i j,
  (i < 2)%nat -> (j < 2)%nat ->
  mat_prod (GraphUnitary.cayley_2 theta) (I_minus_half theta) 2 i j
  == I_plus_half theta i j.
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia;
    unfold mat_prod, I_minus_half, I_plus_half, Id2, GraphUnitary.M_2,
           GraphUnitary.cayley_2; simpl; field;
    apply GraphUnitary.four_plus_sq_neq_0.
Qed.

(* ========================================================================= *)
(*  2. The Cayley matrix of the graph is orthogonal for every theta          *)
(* ========================================================================= *)

Theorem cayley_2_orthogonal : forall theta,
  is_orthogonal (GraphUnitary.cayley_2 theta) 2.
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia;
    unfold mat_prod, mat_trans, GraphUnitary.cayley_2; simpl; field;
    apply GraphUnitary.four_plus_sq_neq_0.
Qed.

Theorem cayley_2_transpose_orthogonal : forall theta,
  is_transpose_orthogonal (GraphUnitary.cayley_2 theta) 2.
Proof.
  intros theta i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia;
    unfold mat_prod, mat_trans, GraphUnitary.cayley_2; simpl; field;
    apply GraphUnitary.four_plus_sq_neq_0.
Qed.

(* ========================================================================= *)
(*  3. The transition matrix Gamma(theta) = |U(theta)|^2 is unistochastic,   *)
(*     hence doubly stochastic — for every theta                             *)
(* ========================================================================= *)

Definition Gamma_graph (theta : Q) : Mat := gamma_of (GraphUnitary.cayley_2 theta).

Theorem graph_transition_unistochastic : forall theta,
  is_unistochastic (Gamma_graph theta) 2.
Proof.
  intro theta. exists (GraphUnitary.cayley_2 theta). split; [| split].
  - apply cayley_2_orthogonal.
  - apply cayley_2_transpose_orthogonal.
  - intros i j. reflexivity.
Qed.

Corollary graph_transition_doubly_stochastic : forall theta,
  is_doubly_stochastic (Gamma_graph theta) 2.
Proof.
  intro theta. apply unistochastic_implies_DS. apply graph_transition_unistochastic.
Qed.

(** At theta = 1 this is the matrix U2 of UnistochasticFromGraph.v. *)
Lemma cayley_2_at_1_is_U2 : forall i j, GraphUnitary.cayley_2 1 i j == U2 i j.
Proof.
  intros i j.
  destruct i as [|[|i']]; destruct j as [|[|j']];
    unfold GraphUnitary.cayley_2, U2; try reflexivity; field.
Qed.

(* ========================================================================= *)
(*  4. Indivisibility: the two-step transition matrix is not the product of  *)
(*     the one-step transition matrices                                      *)
(* ========================================================================= *)

Definition two_step (U : Mat) : Mat := fun i j => mat_prod U U 2 i j.

Lemma two_step_U2_orthogonal : is_orthogonal (two_step U2) 2.
Proof.
  intros i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia; vm_compute; reflexivity.
Qed.

Lemma two_step_U2_transpose_orthogonal : is_transpose_orthogonal (two_step U2) 2.
Proof.
  intros i j Hi Hj.
  destruct i as [|[|i']]; destruct j as [|[|j']]; try lia; vm_compute; reflexivity.
Qed.

(** The two-step transition matrix is itself unistochastic... *)
Theorem two_step_transition_unistochastic :
  is_unistochastic (gamma_of (two_step U2)) 2.
Proof.
  exists (two_step U2). split; [| split].
  - exact two_step_U2_orthogonal.
  - exact two_step_U2_transpose_orthogonal.
  - intros i j. reflexivity.
Qed.

(** ... but it is not the product of the one-step ones: 49/625 against
    337/625. *)
Theorem two_step_transition_indivisible :
  ~ (forall i j, (i < 2)%nat -> (j < 2)%nat ->
       gamma_of (two_step U2) i j == mat_prod Gamma2 Gamma2 2 i j).
Proof.
  intro H.
  assert (H00 := H 0%nat 0%nat ltac:(lia) ltac:(lia)).
  vm_compute in H00. discriminate H00.
Qed.

Lemma two_step_values :
  gamma_of (two_step U2) 0%nat 0%nat == 49 # 625 /\
  mat_prod Gamma2 Gamma2 2 0%nat 0%nat == 337 # 625.
Proof. split; vm_compute; reflexivity. Qed.
