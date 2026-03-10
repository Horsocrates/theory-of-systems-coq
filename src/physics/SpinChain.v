(* ========================================================================= *)
(*        SPINCHAIN — Two-Qubit Systems and Ising Hamiltonian                *)
(*                                                                          *)
(*  Part of: Theory of Systems — Concrete Quantum Systems (Phase 3E)        *)
(*                                                                          *)
(*  Defines two-qubit systems in dimension 4 = 2⊗2:                       *)
(*  computational basis states, Bell states (entangled),                    *)
(*  the Ising Hamiltonian H = J·σ_z⊗σ_z, and measurement                 *)
(*  probabilities and expectation values.                                   *)
(*                                                                          *)
(*  KEY RESULTS:                                                            *)
(*  - bell_psi_plus_entangled: |01⟩+|10⟩ is entangled                    *)
(*  - ising_bell_expectation: ⟨Φ+|H|Φ+⟩ = 2J                            *)
(*  - diag_mat_action: general diagonal matrix action on vectors           *)
(*                                                                          *)
(*  STATUS: 32 Qed, 0 Admitted                                             *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

Require Import QArith QArith.Qabs List Lia ZArith.
Require Import Coq.micromega.Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import LinearAlgebra.
From ToS Require Import CauchyReal.
From ToS Require Import physics.InnerProductSpace.
From ToS Require Import physics.Orthogonality.
From ToS Require Import physics.QState.
From ToS Require Import physics.QObservable.
From ToS Require Import physics.BornRule.
From ToS Require Import physics.Entanglement.
From ToS Require Import physics.Qubit.

(* ========================================================================= *)
(*  PART I: INFRASTRUCTURE                                                   *)
(* ========================================================================= *)

(** Dot product expansion for 4-dimensional vectors *)
Lemma dot_product_4 : forall (v w : QVec 4),
  dot_product v w == qv_nth v 0 * qv_nth w 0 + qv_nth v 1 * qv_nth w 1 +
                     qv_nth v 2 * qv_nth w 2 + qv_nth v 3 * qv_nth w 3.
Proof.
  intros v w.
  unfold dot_product, qv_nth.
  destruct v as [vd Hvlen]. destruct w as [wd Hwlen]. simpl in *.
  destruct vd as [| v0 [| v1 [| v2 [| v3 [| v4 vrest]]]]];
    simpl in Hvlen; try lia.
  destruct wd as [| w0 [| w1 [| w2 [| w3 [| w4 wrest]]]]];
    simpl in Hwlen; try lia.
  simpl. ring.
Qed.

(** General diagonal matrix action: (diag(e)·v)_i = e_i * v_i *)
Lemma diag_mat_action : forall {dim} (eigenvals : QVec dim) (v : QVec dim) i,
  (i < dim)%nat ->
  qv_nth (mat_vec_mul (diag_mat eigenvals) v) i ==
  qv_nth eigenvals i * qv_nth v i.
Proof.
  intros dim eigenvals v i Hi.
  rewrite mat_vec_mul_nth; [| exact Hi].
  unfold mat_row, diag_mat. simpl.
  rewrite (nth_map_general _ (seq 0 dim) 0%nat _ i); [| rewrite seq_length; exact Hi].
  rewrite seq_nth; [| exact Hi]. simpl.
  rewrite dot_product_scale_l.
  rewrite dot_basis_extracts; [| exact Hi].
  reflexivity.
Qed.

(* ========================================================================= *)
(*  PART II: TWO-QUBIT BASIS STATES                                          *)
(* ========================================================================= *)

(** Computational basis states for 2⊗2 system *)
Definition spin_00 : QState 4 := basis_state 4 0.  (* |00⟩ *)
Definition spin_01 : QState 4 := basis_state 4 1.  (* |01⟩ *)
Definition spin_10 : QState 4 := basis_state 4 2.  (* |10⟩ *)
Definition spin_11 : QState 4 := basis_state 4 3.  (* |11⟩ *)

(** Basis states are normalized *)
Lemma spin_normalization : forall j k, (j < 4)%nat ->
  state_ip_at (basis_state 4 j) (basis_state 4 j) k == 1.
Proof. intros j k Hj. apply basis_self_ip. exact Hj. Qed.

(** Distinct basis states are orthogonal *)
Lemma spin_orthogonality : forall i j k,
  (i < 4)%nat -> (j < 4)%nat -> i <> j ->
  state_ip_at (basis_state 4 i) (basis_state 4 j) k == 0.
Proof. intros i j k Hi Hj Hij. apply basis_orthogonal_direct; assumption. Qed.

(** Product state is separable *)
Lemma product_state_separable : forall (a : QState 2) (b : QState 2),
  is_separable (state_tensor a b).
Proof.
  intros a b. exists a, b.
  intros i Hi eps Heps.
  exists 0%nat. intros k _.
  rewrite !state_tensor_at.
  assert (Hdiff : qv_nth (vec_tensor (state_at a k) (state_at b k)) i -
                  qv_nth (vec_tensor (state_at a k) (state_at b k)) i == 0) by ring.
  assert (Habs := Qabs_wd _ _ Hdiff). rewrite Habs.
  rewrite Qabs_pos; lra.
Qed.

(* ========================================================================= *)
(*  PART III: BELL STATES                                                     *)
(* ========================================================================= *)

(** Bell states: maximally entangled two-qubit states *)

(** Φ+ = |00⟩ + |11⟩ — reuse from Entanglement.v *)
Definition bell_phi_plus : QState (2 * 2) := bell_state.

(** Ψ+ = |01⟩ + |10⟩ *)
Definition bell_psi_plus : QState (2 * 2) :=
  state_add (basis_state 4 1) (basis_state 4 2).

(** Ψ+ component values — proved by unfolding to concrete Q arithmetic *)
Lemma psi_plus_component_0 : forall k,
  qv_nth (state_at bell_psi_plus k) 0 == 0.
Proof.
  intros k.
  change (state_at bell_psi_plus k) with
    (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

Lemma psi_plus_component_1 : forall k,
  qv_nth (state_at bell_psi_plus k) 1 == 1.
Proof.
  intros k.
  change (state_at bell_psi_plus k) with
    (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

Lemma psi_plus_component_2 : forall k,
  qv_nth (state_at bell_psi_plus k) 2 == 1.
Proof.
  intros k.
  change (state_at bell_psi_plus k) with
    (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

Lemma psi_plus_component_3 : forall k,
  qv_nth (state_at bell_psi_plus k) 3 == 0.
Proof.
  intros k.
  change (state_at bell_psi_plus k) with
    (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(** Φ+ is entangled (from Entanglement.v) *)
Theorem bell_phi_plus_entangled : is_entangled bell_phi_plus.
Proof. exact bell_entangled. Qed.

(** ★ Ψ+ is entangled — same algebraic contradiction as Φ+ *)
Theorem bell_psi_plus_entangled : is_entangled bell_psi_plus.
Proof.
  unfold is_entangled, is_separable. intros [a [b Hequiv]].
  assert (Heps : 0 < (1#4)) by lra.
  destruct (Hequiv 0%nat ltac:(lia) (1#4) Heps) as [N0 HN0].
  destruct (Hequiv 1%nat ltac:(lia) (1#4) Heps) as [N1 HN1].
  destruct (Hequiv 2%nat ltac:(lia) (1#4) Heps) as [N2 HN2].
  destruct (Hequiv 3%nat ltac:(lia) (1#4) Heps) as [N3 HN3].
  set (N := Nat.max (Nat.max N0 N1) (Nat.max N2 N3)).
  specialize (HN0 N ltac:(unfold N; lia)).
  specialize (HN1 N ltac:(unfold N; lia)).
  specialize (HN2 N ltac:(unfold N; lia)).
  specialize (HN3 N ltac:(unfold N; lia)).
  rewrite state_tensor_at in HN0, HN1, HN2, HN3.
  set (a0 := qv_nth (state_at a N) 0) in *.
  set (a1 := qv_nth (state_at a N) 1) in *.
  set (b0 := qv_nth (state_at b N) 0) in *.
  set (b1 := qv_nth (state_at b N) 1) in *.
  (* Component 0: |0 - a0*b0| < 1/4, so |a0*b0| < 1/4 *)
  assert (H0 : Qabs (a0 * b0) < 1#4).
  { assert (Htc : qv_nth (vec_tensor (state_at a N) (state_at b N)) 0 ==
                  a0 * b0).
    { change 0%nat with (0 * 2 + 0)%nat. apply vec_tensor_component; lia. }
    assert (Hbc := psi_plus_component_0 N).
    assert (Heq : qv_nth (state_at bell_psi_plus N) 0 -
                  qv_nth (vec_tensor (state_at a N) (state_at b N)) 0 ==
                  -(a0 * b0)).
    { rewrite Hbc, Htc. ring. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hopp : Qabs (-(a0 * b0)) == Qabs (a0 * b0)) by (apply Qabs_opp).
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    assert (Hle3 := Qeq_Qle _ _ Hopp).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Hopp)).
    lra. }
  (* Component 1: |1 - a0*b1| < 1/4, so a0*b1 > 3/4 *)
  assert (H1 : Qabs (1 - a0 * b1) < 1#4).
  { assert (Htc : qv_nth (vec_tensor (state_at a N) (state_at b N)) 1 ==
                  a0 * b1).
    { change 1%nat with (0 * 2 + 1)%nat. apply vec_tensor_component; lia. }
    assert (Hbc := psi_plus_component_1 N).
    assert (Heq : qv_nth (state_at bell_psi_plus N) 1 -
                  qv_nth (vec_tensor (state_at a N) (state_at b N)) 1 ==
                  1 - a0 * b1).
    { rewrite Hbc, Htc. reflexivity. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    lra. }
  (* Component 2: |1 - a1*b0| < 1/4 *)
  assert (H2 : Qabs (1 - a1 * b0) < 1#4).
  { assert (Htc : qv_nth (vec_tensor (state_at a N) (state_at b N)) 2 ==
                  a1 * b0).
    { change 2%nat with (1 * 2 + 0)%nat. apply vec_tensor_component; lia. }
    assert (Hbc := psi_plus_component_2 N).
    assert (Heq : qv_nth (state_at bell_psi_plus N) 2 -
                  qv_nth (vec_tensor (state_at a N) (state_at b N)) 2 ==
                  1 - a1 * b0).
    { rewrite Hbc, Htc. reflexivity. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    lra. }
  (* Component 3: |0 - a1*b1| < 1/4, so |a1*b1| < 1/4 *)
  assert (H3 : Qabs (a1 * b1) < 1#4).
  { assert (Htc : qv_nth (vec_tensor (state_at a N) (state_at b N)) 3 ==
                  a1 * b1).
    { change 3%nat with (1 * 2 + 1)%nat. apply vec_tensor_component; lia. }
    assert (Hbc := psi_plus_component_3 N).
    assert (Heq : qv_nth (state_at bell_psi_plus N) 3 -
                  qv_nth (vec_tensor (state_at a N) (state_at b N)) 3 ==
                  -(a1 * b1)).
    { rewrite Hbc, Htc. ring. }
    pose proof (Qabs_wd _ _ Heq) as Hwd.
    assert (Hopp : Qabs (-(a1 * b1)) == Qabs (a1 * b1)) by (apply Qabs_opp).
    assert (Hle1 := Qeq_Qle _ _ Hwd).
    assert (Hle2 := Qeq_Qle _ _ (Qeq_sym _ _ Hwd)).
    assert (Hle3 := Qeq_Qle _ _ Hopp).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Hopp)).
    lra. }
  (* Algebraic identity: (a0*b1)*(a1*b0) = (a0*b0)*(a1*b1) *)
  assert (Hkey : a0 * b1 * (a1 * b0) == a0 * b0 * (a1 * b1)) by ring.
  (* From H1: a0*b1 > 3/4 *)
  assert (Hab01_lo : 3#4 < a0 * b1).
  { destruct (Qlt_le_dec (1 - a0 * b1) 0) as [Hneg | Hpos].
    - lra.
    - assert (Habs_eq : Qabs (1 - a0 * b1) == 1 - a0 * b1)
        by (rewrite Qabs_pos; lra).
      assert (Hle := Qeq_Qle _ _ Habs_eq). lra. }
  (* From H2: a1*b0 > 3/4 *)
  assert (Hab10_lo : 3#4 < a1 * b0).
  { destruct (Qlt_le_dec (1 - a1 * b0) 0) as [Hneg | Hpos].
    - lra.
    - assert (Habs_eq : Qabs (1 - a1 * b0) == 1 - a1 * b0)
        by (rewrite Qabs_pos; lra).
      assert (Hle := Qeq_Qle _ _ Habs_eq). lra. }
  (* Product: |a0*b0| * |a1*b1| < 1/16 *)
  assert (Hprod_hi : Qabs (a0 * b0) * Qabs (a1 * b1) < 1#16).
  { pose proof (Qabs_nonneg (a1 * b1)) as Hnn.
    destruct (Qeq_dec (Qabs (a1 * b1)) 0) as [Hz | Hnz].
    - assert (Heq0 : Qabs (a0 * b0) * Qabs (a1 * b1) == 0)
        by (rewrite Hz; ring).
      assert (Hle := Qeq_Qle _ _ Heq0). lra.
    - assert (Hpos : 0 < Qabs (a1 * b1)) by lra.
      apply Qlt_trans with ((1#4) * Qabs (a1 * b1)).
      + setoid_replace (Qabs (a0 * b0) * Qabs (a1 * b1))
          with (Qabs (a1 * b1) * Qabs (a0 * b0)) by ring.
        setoid_replace ((1#4) * Qabs (a1 * b1))
          with (Qabs (a1 * b1) * (1#4)) by ring.
        exact (proj2 (Qmult_lt_l _ _ _ Hpos) H0).
      + assert (H14 : 0 < (1#4)) by lra.
        exact (proj2 (Qmult_lt_l _ _ _ H14) H3). }
  (* Product: a0*b1 * a1*b0 > 9/16 *)
  assert (H01pos : 0 < a0 * b1) by lra.
  assert (H10pos : 0 < a1 * b0) by lra.
  assert (H34 : 0 < (3#4)) by lra.
  assert (Hprod_lo : (3#4) * (3#4) < a0 * b1 * (a1 * b0)).
  { apply Qlt_trans with ((3#4) * (a1 * b0)).
    - exact (proj2 (Qmult_lt_l _ _ _ H34) Hab10_lo).
    - setoid_replace ((3#4) * (a1 * b0)) with ((a1 * b0) * (3#4)) by ring.
      setoid_replace (a0 * b1 * (a1 * b0)) with ((a1 * b0) * (a0 * b1)) by ring.
      exact (proj2 (Qmult_lt_l _ _ _ H10pos) Hab01_lo). }
  (* Bridge: a0*b1*(a1*b0) = a0*b0*(a1*b1), both positive, so *)
  (* |a0*b0*(a1*b1)| = |a0*b1*(a1*b0)| = |a0*b0|*|a1*b1| < 1/16 *)
  (* But a0*b1*(a1*b0) > 9/16, contradiction *)
  assert (Habs_prod : Qabs (a0 * b0 * (a1 * b1)) ==
                      Qabs (a0 * b0) * Qabs (a1 * b1)).
  { apply Qabs_Qmult. }
  assert (Habs_key : Qabs (a0 * b1 * (a1 * b0)) ==
                     Qabs (a0 * b0 * (a1 * b1))).
  { apply Qabs_wd. exact Hkey. }
  assert (Habs_pos : Qabs (a0 * b1 * (a1 * b0)) == a0 * b1 * (a1 * b0)).
  { rewrite Qabs_pos; lra. }
  assert (Hchain : a0 * b1 * (a1 * b0) < 1#16).
  { assert (Hle1 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_pos)).
    assert (Hle2 := Qeq_Qle _ _ Habs_key).
    assert (Hle3 := Qeq_Qle _ _ Habs_prod).
    assert (Hle4 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_key)).
    assert (Hle5 := Qeq_Qle _ _ (Qeq_sym _ _ Habs_prod)).
    lra. }
  lra.
Qed.

(** Φ+ norm squared = 2 *)
Lemma bell_phi_plus_norm_sq : forall k,
  state_ip_at bell_phi_plus bell_phi_plus k == 2.
Proof.
  intros k. unfold bell_phi_plus, state_ip_at, bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (v := qv_add (basis_vec 4 0) (basis_vec 4 3)).
  rewrite dot_product_4. subst v.
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(** Ψ+ norm squared = 2 *)
Lemma bell_psi_plus_norm_sq : forall k,
  state_ip_at bell_psi_plus bell_psi_plus k == 2.
Proof.
  intros k. unfold state_ip_at.
  change (state_at bell_psi_plus k)
    with (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  set (v := qv_add (basis_vec 4 1) (basis_vec 4 2)).
  rewrite dot_product_4. subst v.
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(** Φ+ and Ψ+ are orthogonal *)
Lemma bell_states_orthogonal : forall k,
  state_ip_at bell_phi_plus bell_psi_plus k == 0.
Proof.
  intros k. unfold state_ip_at, bell_phi_plus, bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (basis_vec 4 0) (basis_vec 4 3)).
  change (state_at bell_psi_plus k)
    with (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  set (v1 := qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (v2 := qv_add (basis_vec 4 1) (basis_vec 4 2)).
  rewrite dot_product_4. subst v1 v2.
  unfold qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(* ========================================================================= *)
(*  PART IV: ISING HAMILTONIAN                                                *)
(* ========================================================================= *)

(** Ising Hamiltonian: H = J · σ_z ⊗ σ_z
    In computational basis: diag(J, -J, -J, J) *)
Definition ising_eigenvals (J : Q) : QVec 4 :=
  mkQVec [J; -(J); -(J); J] eq_refl.

Definition ising_hamiltonian (J : Q) : QObservable 4 :=
  diag_observable (ising_eigenvals J).

(** Eigenvalue access *)
Lemma ising_eigenval_0 : forall J, qv_nth (ising_eigenvals J) 0 == J.
Proof. intros J. reflexivity. Qed.

Lemma ising_eigenval_1 : forall J, qv_nth (ising_eigenvals J) 1 == -(J).
Proof. intros J. reflexivity. Qed.

Lemma ising_eigenval_2 : forall J, qv_nth (ising_eigenvals J) 2 == -(J).
Proof. intros J. reflexivity. Qed.

Lemma ising_eigenval_3 : forall J, qv_nth (ising_eigenvals J) 3 == J.
Proof. intros J. reflexivity. Qed.

(** Eigenstates: all basis states are eigenstates *)
Theorem ising_eigenstate : forall J j, (j < 4)%nat ->
  is_eigenstate (ising_hamiltonian J) (basis_state 4 j) (qv_nth (ising_eigenvals J) j).
Proof.
  intros J j Hj. unfold ising_hamiltonian.
  apply diag_eigenstate. exact Hj.
Qed.

(** Eigenstate expectations via diag_eigenstate *)
Theorem ising_expectation_basis : forall J j k, (j < 4)%nat ->
  born_expectation_at (ising_hamiltonian J) (basis_state 4 j) k ==
  qv_nth (ising_eigenvals J) j.
Proof.
  intros J j k Hj. unfold ising_hamiltonian.
  apply expectation_diag_basis. exact Hj.
Qed.

(** ★ Bell state expectation: ⟨Φ+|H_Ising|Φ+⟩ = 2J *)
Theorem ising_bell_expectation : forall J k,
  born_expectation_at (ising_hamiltonian J) bell_phi_plus k == 2 * J.
Proof.
  intros J k. unfold born_expectation_at, obs_action_at, bell_phi_plus, bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (basis_vec 4 0) (basis_vec 4 3)).
  change (obs_at (ising_hamiltonian J) k) with (diag_mat (ising_eigenvals J)).
  set (sv := qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (Av := mat_vec_mul (diag_mat (ising_eigenvals J)) sv).
  rewrite dot_product_4.
  subst Av.
  rewrite !(diag_mat_action (ising_eigenvals J)); try lia.
  subst sv.
  unfold ising_eigenvals, qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(** Ψ+ expectation: ⟨Ψ+|H_Ising|Ψ+⟩ = -2J *)
Theorem ising_psi_expectation : forall J k,
  born_expectation_at (ising_hamiltonian J) bell_psi_plus k == -(2 * J).
Proof.
  intros J k. unfold born_expectation_at, obs_action_at.
  change (state_at bell_psi_plus k)
    with (qv_add (basis_vec 4 1) (basis_vec 4 2)).
  change (obs_at (ising_hamiltonian J) k) with (diag_mat (ising_eigenvals J)).
  set (sv := qv_add (basis_vec 4 1) (basis_vec 4 2)).
  set (Av := mat_vec_mul (diag_mat (ising_eigenvals J)) sv).
  rewrite dot_product_4.
  subst Av.
  rewrite !(diag_mat_action (ising_eigenvals J)); try lia.
  subst sv.
  unfold ising_eigenvals, qv_add, qv_nth, basis_vec. simpl. ring.
Qed.

(* ========================================================================= *)
(*  PART V: MEASUREMENT PROBABILITIES                                         *)
(* ========================================================================= *)

(** Born probabilities for basis states *)
Lemma spin_born_same : forall j k, (j < 4)%nat ->
  born_prob_at (basis_state 4 j) (basis_state 4 j) k == 1.
Proof. intros j k Hj. apply born_self_basis. exact Hj. Qed.

Lemma spin_born_diff : forall i j k,
  (i < 4)%nat -> (j < 4)%nat -> i <> j ->
  born_prob_at (basis_state 4 i) (basis_state 4 j) k == 0.
Proof. intros i j k Hi Hj Hij. apply born_orthogonal_at; assumption. Qed.

(** Measurement of Φ+ in computational basis *)
Lemma phi_plus_prob_00 : forall k,
  normalized_prob spin_00 bell_phi_plus k == (1#2).
Proof.
  intros k. unfold normalized_prob, born_prob_at, spin_00, bell_phi_plus, state_ip_at,
    bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (sv := qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (bv := state_at (basis_state 4 0) k).
  change bv with (basis_vec 4 0).
  rewrite !dot_product_4.
  subst sv bv.
  unfold qv_add, qv_nth, basis_vec. simpl. field.
Qed.

Lemma phi_plus_prob_11 : forall k,
  normalized_prob spin_11 bell_phi_plus k == (1#2).
Proof.
  intros k. unfold normalized_prob, born_prob_at, spin_11, bell_phi_plus, state_ip_at,
    bell_state.
  change (state_at (state_add (basis_state 4 0) (basis_state 4 3)) k)
    with (qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (sv := qv_add (basis_vec 4 0) (basis_vec 4 3)).
  set (bv := state_at (basis_state 4 3) k).
  change bv with (basis_vec 4 3).
  rewrite !dot_product_4.
  subst sv bv.
  unfold qv_add, qv_nth, basis_vec. simpl. field.
Qed.

(** Measurement probabilities sum to 1 *)
Theorem phi_plus_prob_sum : forall k,
  normalized_prob spin_00 bell_phi_plus k +
  normalized_prob spin_11 bell_phi_plus k == 1.
Proof.
  intros k. rewrite phi_plus_prob_00, phi_plus_prob_11. ring.
Qed.

(* ========================================================================= *)
(*  PART VI: ISING PROPERTIES                                                 *)
(* ========================================================================= *)

(** Energy gap between aligned and anti-aligned states *)
Theorem ising_energy_gap : forall J,
  0 < J ->
  qv_nth (ising_eigenvals J) 0 - qv_nth (ising_eigenvals J) 1 == 2 * J.
Proof.
  intros J HJ. rewrite ising_eigenval_0, ising_eigenval_1. ring.
Qed.

(** H = Jσ_z⊗σ_z with J > 0: anti-aligned states have lower energy (-J < J) *)
Theorem antiferro_ground : forall J k,
  0 < J ->
  born_expectation_at (ising_hamiltonian J) spin_01 k <
  born_expectation_at (ising_hamiltonian J) spin_00 k.
Proof.
  intros J k HJ.
  unfold spin_00, spin_01.
  rewrite (ising_expectation_basis J 0 k ltac:(lia)).
  rewrite (ising_expectation_basis J 1 k ltac:(lia)).
  rewrite ising_eigenval_0, ising_eigenval_1. lra.
Qed.

(** H = Jσ_z⊗σ_z with J < 0: aligned states have lower energy (J < -J) *)
Theorem ferro_ground : forall J k,
  J < 0 ->
  born_expectation_at (ising_hamiltonian J) spin_00 k <
  born_expectation_at (ising_hamiltonian J) spin_01 k.
Proof.
  intros J k HJ.
  unfold spin_00, spin_01.
  rewrite (ising_expectation_basis J 0 k ltac:(lia)).
  rewrite (ising_expectation_basis J 1 k ltac:(lia)).
  rewrite ising_eigenval_0, ising_eigenval_1. lra.
Qed.

(** Bell state Ψ+ has negative correlation in ferromagnet *)
Theorem bell_anticorrelation : forall J k,
  0 < J ->
  born_expectation_at (ising_hamiltonian J) bell_psi_plus k < 0.
Proof.
  intros J k HJ. rewrite ising_psi_expectation. lra.
Qed.

(** Normalized Bell expectation = J *)
Theorem ising_bell_normalized : forall J k,
  born_expectation_at (ising_hamiltonian J) bell_phi_plus k /
  state_ip_at bell_phi_plus bell_phi_plus k == J.
Proof.
  intros J k. rewrite ising_bell_expectation, bell_phi_plus_norm_sq. field.
Qed.

(* ========================================================================= *)
(*  SUMMARY                                                                  *)
(* ========================================================================= *)

(** Summary:
    SpinChain.v: Two-qubit systems, Bell states, Ising Hamiltonian.

    Part I: Infrastructure
    - dot_product_4, diag_mat_action (general diagonal matrix action)

    Part II: Basis States
    - spin_00/01/10/11, spin_normalization, spin_orthogonality
    - product_state_separable

    Part III: Bell States
    - bell_phi_plus = |00⟩+|11⟩ (from Entanglement.v)
    - bell_psi_plus = |01⟩+|10⟩ (new)
    - ★ bell_psi_plus_entangled: algebraic contradiction proof
    - Norm squared, orthogonality of Bell states

    Part IV: Ising Hamiltonian
    - ising_eigenvals, ising_hamiltonian
    - ising_eigenstate (all basis states)
    - ★ ising_bell_expectation: ⟨Φ+|H|Φ+⟩ = 2J
    - ising_psi_expectation: ⟨Ψ+|H|Ψ+⟩ = -2J

    Part V: Measurements
    - spin_born_same/diff
    - phi_plus_prob_00/11 = 1/2 each
    - phi_plus_prob_sum: probabilities sum to 1

    Part VI: Properties
    - ising_energy_gap, antiferro_ground, ferro_ground
    - bell_anticorrelation, ising_bell_normalized
*)
