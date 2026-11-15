(** * ProcessOperatorSpectrumEvolution.v -- The point spectrum of a diagonal operator, the canonical commutator with a complex constant, energy under a commuting isometry, the Cayley step, as a ToS System

    Elements: rational matrices and vectors on N coordinates; the diagonal
              lam of a diagonal operator; pairs of rational matrices (real
              and imaginary parts); the states psi_n of a discrete evolution.
    Roles:    [diag_op lam]  -- the diagonal operator; its entries are its
                                eigenvalues;
              commutator     -- [A, B] = AB - BA; its trace is zero;
              isometry U     -- a step that keeps the norm;
              H              -- the Hamiltonian; energy <psi, H psi>;
              Cayley step    -- the rational isometric step built from a
                                generator t J.
    Rules:    an eigenvalue of a diagonal operator is one of its entries; if
              the entries tend to zero, a non-zero value occurs among them
              finitely often, its eigenvectors have finitely many non-zero
              coordinates, and the operator is approximated by operators of
              finite rank; no finite matrices realise [A, B] = c 1 with a
              non-zero complex constant; the commutator of the position
              with any matrix has zero diagonal; an isometry that commutes
              with H keeps the energy.

    Proved (no axioms):
      - [to_zero_unfold], [diag_eigen_is_entry],
        [diag_nonzero_value_finitely_often], [diag_eigenspace_finite],
        [diag_finite_rank_approx];
      - [commutator_concrete_entries], [commutator_concrete_not_scalar],
        [no_finite_ccr_complex], [position_commutator_entry],
        [position_commutator_zero_diagonal];
      - [isometry_not_energy_preserving]: an isometry need not keep the
        energy; [isometry_polarization],
        [isometry_commuting_preserves_energy],
        [commuting_isometric_evolution_conserves_both];
      - [cayley_step_isometry], [cayley_step_equation],
        [cayley_half_is_345], [cayley_evolution_conserves_both];
      - [symmetric_without_rational_eigenvector]: a symmetric rational
        matrix with no rational eigenvector.

    P4 diagnostic: all objects are finite rational matrices at a fixed N or
      explicit sequences. The limit of the entries is given as a process
      (lam ~~ 0); the exact propagator and irrational eigenvalues are not
      elements. The step of the evolution is built rationally from the
      generator (Cayley), not as an exponential.

    NOT claimed:
      - compactness of an operator as a notion, or a spectral theorem for an
        arbitrary compact operator;
      - unboundedness of operators (the Wintner-Wielandt theorem): there is
        no operator norm on complete sequences in this layer;
      - closeness of the Cayley step to the exponential exp(-i H t);
      - the existence of an eigenvector of an arbitrary symmetric operator
        (over Q it fails: [symmetric_without_rational_eigenvector]).

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.
From ToS Require Import process.ProcessDCT.
From ToS Require Import process.ProcessL2CauchySchwarz.
From ToS Require Import process.ProcessL2BesselGeneral.
From ToS Require Import process.ProcessCompactSpectral.
From ToS Require Import process.ProcessSelfAdjointSpectral.
From ToS Require Import process.ProcessCanonicalCommutator.
From ToS Require Import process.ProcessPositionMomentum.
From ToS Require Import process.ProcessSchrodingerEvolution.
From ToS Require Import process.ProcessEnergyConservation.
From ToS Require analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. The diagonal operator: point spectrum and finite-rank approximation*)
(* ===================================================================== *)

(** The conclusion of [diag_spectrum_discrete] is the unfolded premise
    lam ~~ 0: the two are equivalent. *)
Lemma to_zero_unfold : forall lam : nat -> Q,
  (lam ~~ const_process 0)
  <-> (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (lam n) < eps).
Proof.
  intro lam. split.
  - apply diag_spectrum_discrete.
  - intros H eps Heps. destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
    assert (E : lam n - const_process 0 n == lam n) by (cbv [const_process]; ring).
    rewrite E. exact (HN n Hn).
Qed.

(** An eigenvalue of a diagonal operator is one of its entries. *)
Theorem diag_eigen_is_entry : forall (lam v : nat -> Q) (mu : Q) (n : nat),
  (forall m, diag_op lam v m == mu * v m) -> ~ v n == 0 -> mu == lam n.
Proof.
  intros lam v mu n He Hv. specialize (He n). unfold diag_op in He.
  assert (Hz : (lam n - mu) * v n == 0).
  { setoid_replace ((lam n - mu) * v n) with (lam n * v n - mu * v n) by ring.
    rewrite He. ring. }
  destruct (Qmult_integral _ _ Hz) as [H | H]; [ lra | contradiction ].
Qed.

(** If lam -> 0, a non-zero value occurs among the entries finitely often. *)
Theorem diag_nonzero_value_finitely_often : forall (lam : nat -> Q) (mu : Q),
  (lam ~~ const_process 0) -> ~ mu == 0 ->
  exists N, forall n, (N <= n)%nat -> ~ lam n == mu.
Proof.
  intros lam mu Hconv Hmu.
  assert (Hpos : 0 < Qabs mu).
  { destruct (Q_dec mu 0) as [[Hlt | Hgt] | Heq].
    - rewrite Qabs_neg by lra. lra.
    - rewrite Qabs_pos by lra. lra.
    - contradiction. }
  destruct (diag_spectrum_discrete lam Hconv (Qabs mu) Hpos) as [N HN].
  exists N. intros n Hn Heq. specialize (HN n Hn). rewrite Heq in HN.
  apply (Qlt_irrefl _ HN).
Qed.

(** The eigenspace of a non-zero eigenvalue is finite-dimensional: an
    eigenvector vanishes from some index on. *)
Theorem diag_eigenspace_finite : forall (lam v : nat -> Q) (mu : Q),
  (lam ~~ const_process 0) -> ~ mu == 0 ->
  (forall m, diag_op lam v m == mu * v m) ->
  exists N, forall n, (N <= n)%nat -> v n == 0.
Proof.
  intros lam v mu Hconv Hmu He.
  destruct (diag_nonzero_value_finitely_often lam mu Hconv Hmu) as [N HN].
  exists N. intros n Hn.
  destruct (Qeq_dec (v n) 0) as [Hz | Hnz]; [ exact Hz | ].
  exfalso. apply (HN n Hn). symmetry. exact (diag_eigen_is_entry lam v mu n He Hnz).
Qed.

(** The tail of the diagonal: the entries below N are replaced by 0. *)
Definition lam_tail (lam : nat -> Q) (N : nat) : nat -> Q :=
  fun n => if (n <? N)%nat then 0 else lam n.

(** Approximation by operators of finite rank: the tail of a diagonal
    operator is small in norm, uniformly in the vector f and the stage M. *)
Theorem diag_finite_rank_approx : forall lam : nat -> Q,
  (lam ~~ const_process 0) ->
  forall eps, 0 < eps -> exists N, forall (f : nat -> Q) (M : nat),
    seq_inner (diag_op (lam_tail lam N) f) (diag_op (lam_tail lam N) f) M
    <= (eps * eps) * seq_inner f f M.
Proof.
  intros lam Hconv eps Heps.
  destruct (diag_spectrum_discrete lam Hconv eps Heps) as [N HN].
  exists N. intros f M. apply diag_bounded. intro n. unfold lam_tail.
  destruct (n <? N)%nat eqn:E.
  - assert (H0 : 0 <= eps * eps) by apply q_sq_nonneg. lra.
  - apply Nat.ltb_ge in E. specialize (HN n E).
    apply Qabs_Qlt_condition in HN. destruct HN as [H1 H2].
    assert (Hp : 0 <= (eps - lam n) * (eps + lam n)).
    { apply Qmult_le_0_compat; lra. }
    assert (Hr : (eps - lam n) * (eps + lam n) == eps * eps - lam n * lam n) by ring.
    rewrite Hr in Hp. lra.
Qed.

(* ===================================================================== *)
(*  2. The canonical commutator                                         *)
(* ===================================================================== *)

(** The witness: A = E_01, B = E_10 on two coordinates; [A, B] = diag(1, -1). *)
Example commutator_concrete_entries :
  let A := fun i j => if andb ((i =? 0)%nat) ((j =? 1)%nat) then 1 else 0 in
  let B := fun i j => if andb ((i =? 1)%nat) ((j =? 0)%nat) then 1 else 0 in
  let C := mat_sub (mat_mul A B 2%nat) (mat_mul B A 2%nat) in
  C 0%nat 0%nat == 1 /\ C 0%nat 1%nat == 0 /\ C 1%nat 0%nat == 0 /\ C 1%nat 1%nat == - (1).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** It is not a multiple of the identity. *)
Example commutator_concrete_not_scalar :
  let A := fun i j => if andb ((i =? 0)%nat) ((j =? 1)%nat) then 1 else 0 in
  let B := fun i j => if andb ((i =? 1)%nat) ((j =? 0)%nat) then 1 else 0 in
  let C := mat_sub (mat_mul A B 2%nat) (mat_mul B A 2%nat) in
  forall c : Q, ~ (C 0%nat 0%nat == mat_scal c mat_id 0%nat 0%nat
                   /\ C 1%nat 1%nat == mat_scal c mat_id 1%nat 1%nat).
Proof.
  intros A B C c [H0 H1].
  assert (E0 : C 0%nat 0%nat == 1) by (vm_compute; reflexivity).
  assert (E1 : C 1%nat 1%nat == - (1)) by (vm_compute; reflexivity).
  rewrite E0 in H0. rewrite E1 in H1.
  unfold mat_scal, mat_id in H0, H1. cbn in H0, H1. lra.
Qed.

(** A complex constant: A = A1 + i A2, B = B1 + i B2,
    [A, B] = ([A1,B1] - [A2,B2]) + i ([A1,B2] + [A2,B1]). *)
Definition comm (A B : nat -> nat -> Q) (N : nat) : nat -> nat -> Q :=
  mat_sub (mat_mul A B N) (mat_mul B A N).
Definition mat_add (A B : nat -> nat -> Q) : nat -> nat -> Q :=
  fun i j => A i j + B i j.

Lemma trace_add : forall (A B : nat -> nat -> Q) (N : nat),
  mat_trace (mat_add A B) N == mat_trace A N + mat_trace B N.
Proof.
  intros A B N. unfold mat_trace, mat_add. cbn beta.
  apply (q_sum_plus (fun i => A i i) (fun i => B i i) N).
Qed.

Lemma scal_zero_of_trace : forall (c : Q) (N : nat),
  (1 <= N)%nat -> c * inject_Z (Z.of_nat N) == 0 -> c == 0.
Proof.
  intros c N HN Hz.
  assert (HzN : (0 < Z.of_nat N)%Z) by lia.
  assert (Hpos : 0 < inject_Z (Z.of_nat N)).
  { rewrite (Zlt_Qlt 0 (Z.of_nat N)) in HzN.
    change (inject_Z 0) with 0 in HzN. exact HzN. }
  destruct (Qmult_integral c (inject_Z (Z.of_nat N)) Hz) as [Hc | Hd].
  - exact Hc.
  - rewrite Hd in Hpos. lra.
Qed.

(** If [A, B] = (c1 + i c2) 1 on N >= 1 coordinates, then c1 = c2 = 0. *)
Theorem no_finite_ccr_complex :
  forall (A1 A2 B1 B2 : nat -> nat -> Q) (c1 c2 : Q) (N : nat),
  (1 <= N)%nat ->
  (forall i j, (i < N)%nat -> (j < N)%nat ->
     mat_sub (comm A1 B1 N) (comm A2 B2 N) i j == mat_scal c1 mat_id i j) ->
  (forall i j, (i < N)%nat -> (j < N)%nat ->
     mat_add (comm A1 B2 N) (comm A2 B1 N) i j == mat_scal c2 mat_id i j) ->
  c1 == 0 /\ c2 == 0.
Proof.
  intros A1 A2 B1 B2 c1 c2 N HN Hre Him. split.
  - apply (scal_zero_of_trace c1 N HN).
    rewrite <- (trace_scal_id c1 N).
    transitivity (mat_trace (mat_sub (comm A1 B1 N) (comm A2 B2 N)) N).
    + unfold mat_trace. symmetry. apply q_sum_ext_bounded. intros i Hi.
      apply (Hre i i Hi Hi).
    + rewrite (trace_sub (comm A1 B1 N) (comm A2 B2 N) N). unfold comm.
      rewrite (trace_commutator_zero A1 B1 N), (trace_commutator_zero A2 B2 N). ring.
  - apply (scal_zero_of_trace c2 N HN).
    rewrite <- (trace_scal_id c2 N).
    transitivity (mat_trace (mat_add (comm A1 B2 N) (comm A2 B1 N)) N).
    + unfold mat_trace. symmetry. apply q_sum_ext_bounded. intros i Hi.
      apply (Him i i Hi Hi).
    + rewrite (trace_add (comm A1 B2 N) (comm A2 B1 N) N). unfold comm.
      rewrite (trace_commutator_zero A1 B2 N), (trace_commutator_zero A2 B1 N). ring.
Qed.

(** The commutator of the position with any matrix B on any lattice:
    [q, B]_ij = (x_i - x_j) B_ij; the diagonal is zero. *)
Theorem position_commutator_entry :
  forall (x : nat -> Q) (B : nat -> nat -> Q) (N i j : nat),
  (i < N)%nat -> (j < N)%nat ->
  mat_sub (mat_mul (qhat x) B N) (mat_mul B (qhat x) N) i j == (x i - x j) * B i j.
Proof.
  intros x B N i j Hi Hj. unfold mat_sub, mat_mul, qhat. cbn beta.
  assert (E1 : q_sum (fun k => (if (i =? k)%nat then x i else 0) * B k j) N == x i * B i j).
  { apply (q_sum_delta (x i) (fun k => B k j) i N Hi). }
  assert (E2 : q_sum (fun k => B i k * (if (k =? j)%nat then x k else 0)) N == x j * B i j).
  { transitivity (q_sum (fun k => (if (j =? k)%nat then x j else 0) * B i k) N).
    - apply q_sum_ext. intro k. cbn beta.
      destruct (Nat.eqb k j) eqn:E.
      + apply Nat.eqb_eq in E. subst k. rewrite Nat.eqb_refl. ring.
      + rewrite Nat.eqb_sym, E. ring.
    - apply (q_sum_delta (x j) (fun k => B i k) j N Hj). }
  rewrite E1, E2. ring.
Qed.

Corollary position_commutator_zero_diagonal :
  forall (x : nat -> Q) (B : nat -> nat -> Q) (N i : nat),
  (i < N)%nat ->
  mat_sub (mat_mul (qhat x) B N) (mat_mul B (qhat x) N) i i == 0.
Proof.
  intros x B N i Hi. rewrite (position_commutator_entry x B N i i Hi Hi). ring.
Qed.

(* ===================================================================== *)
(*  3. Evolution: energy, the commuting isometry, the Cayley step       *)
(* ===================================================================== *)

(** An isometry need not keep the energy: the 3-4-5 rotation and
    H = diag(1, 0). *)
Example isometry_not_energy_preserving :
  Isometry (rotation (3 # 5) (4 # 5)) 2
  /\ ~ EnergyPreserving (rotation (3 # 5) (4 # 5)) (Hdiag 1 0) 2.
Proof.
  split.
  - apply rotation_345_isometry.
  - intro H. specialize (H (fun n => match n with O => 1 | _ => 0 end)).
    vm_compute in H. discriminate H.
Qed.

(** The Cayley (Crank-Nicolson) step for the generator t J,
    J = [[0,-1],[1,0]]: a rational rotation for every rational t. *)
Definition cn_c (t : Q) : Q := (1 - t * t) / (1 + t * t).
Definition cn_s (t : Q) : Q := (2 * t) / (1 + t * t).

Lemma one_plus_sq_nonzero : forall t : Q, ~ 1 + t * t == 0.
Proof. intros t H. assert (H0 : 0 <= t * t) by apply q_sq_nonneg. lra. Qed.

Theorem cayley_step_isometry : forall t : Q, Isometry (rotation (cn_c t) (cn_s t)) 2.
Proof.
  intro t. apply rotation_isometry. unfold cn_c, cn_s. field.
  apply one_plus_sq_nonzero.
Qed.

(** The step w = U v satisfies the implicit midpoint scheme
    w - v = t J (w + v). *)
Theorem cayley_step_equation : forall (t : Q) (v : nat -> Q),
  let w := op_apply (rotation (cn_c t) (cn_s t)) v 2 in
  w 0%nat - v 0%nat == - t * (w 1%nat + v 1%nat)
  /\ w 1%nat - v 1%nat == t * (w 0%nat + v 0%nat).
Proof.
  intros t v w. unfold w, op_apply, rotation, cn_c, cn_s. cbn [q_sum].
  split; field; apply one_plus_sq_nonzero.
Qed.

(** The 3-4-5 rotation is the Cayley step for t = 1/2. *)
Example cayley_half_is_345 : cn_c (1 # 2) == 3 # 5 /\ cn_s (1 # 2) == 4 # 5.
Proof. split; vm_compute; reflexivity. Qed.

Lemma op_apply_add : forall (U : nat -> nat -> Q) (a b : nat -> Q) (N i : nat),
  op_apply U (fun j => a j + b j) N i == op_apply U a N i + op_apply U b N i.
Proof.
  intros U a b N i. unfold op_apply.
  transitivity (q_sum (fun j => U i j * a j + U i j * b j) N).
  - apply q_sum_ext. intro j. ring.
  - apply (q_sum_plus (fun j => U i j * a j) (fun j => U i j * b j) N).
Qed.

Lemma seq_inner_add_sq : forall (a b : nat -> Q) (N : nat),
  seq_inner (fun i => a i + b i) (fun i => a i + b i) N
  == seq_inner a a N + 2 * seq_inner a b N + seq_inner b b N.
Proof.
  intros a b N. unfold seq_inner.
  transitivity (q_sum (fun i => (a i * a i + 2 * (a i * b i)) + b i * b i) N).
  - apply q_sum_ext. intro i. ring.
  - rewrite (q_sum_plus (fun i => a i * a i + 2 * (a i * b i)) (fun i => b i * b i) N).
    rewrite (q_sum_plus (fun i => a i * a i) (fun i => 2 * (a i * b i)) N).
    rewrite (q_sum_scale 2 (fun i => a i * b i) N). reflexivity.
Qed.

(** An isometry keeps the pairing as well (polarization). *)
Theorem isometry_polarization : forall (U : nat -> nat -> Q) (N : nat),
  Isometry U N -> forall a b : nat -> Q,
  seq_inner (op_apply U a N) (op_apply U b N) N == seq_inner a b N.
Proof.
  intros U N HU a b.
  assert (H1 := HU (fun j => a j + b j)).
  assert (H2 : seq_inner (op_apply U (fun j => a j + b j) N)
                         (op_apply U (fun j => a j + b j) N) N
               == seq_inner (fun i => op_apply U a N i + op_apply U b N i)
                            (fun i => op_apply U a N i + op_apply U b N i) N).
  { apply seq_inner_ext; intro i; apply op_apply_add. }
  rewrite H2 in H1.
  rewrite (seq_inner_add_sq (op_apply U a N) (op_apply U b N) N) in H1.
  rewrite (seq_inner_add_sq a b N) in H1.
  rewrite (HU a), (HU b) in H1. lra.
Qed.

(** An isometry that commutes with H keeps the energy. *)
Theorem isometry_commuting_preserves_energy :
  forall (U H : nat -> nat -> Q) (N : nat),
  Isometry U N ->
  (forall (w : nat -> Q) (i : nat), (i < N)%nat ->
     op_apply H (op_apply U w N) N i == op_apply U (op_apply H w N) N i) ->
  EnergyPreserving U H N.
Proof.
  intros U H N HU Hc w. unfold energy.
  transitivity (seq_inner (op_apply U w N) (op_apply U (op_apply H w N) N) N).
  - unfold seq_inner. apply q_sum_ext_bounded. intros i Hi. cbn beta.
    rewrite (Hc w i Hi). reflexivity.
  - apply (isometry_polarization U N HU w (op_apply H w N)).
Qed.

(** A commuting isometric evolution conserves both the norm and the energy. *)
Corollary commuting_isometric_evolution_conserves_both :
  forall (U H : nat -> nat -> Q) (N : nat),
  Isometry U N ->
  (forall (w : nat -> Q) (i : nat), (i < N)%nat ->
     op_apply H (op_apply U w N) N i == op_apply U (op_apply H w N) N i) ->
  forall (v : nat -> Q) (n : nat),
  seq_inner (evolve U N v n) (evolve U N v n) N == seq_inner v v N
  /\ energy H (evolve U N v n) N == energy H v N.
Proof.
  intros U H N HU Hc v n. split.
  - apply evolution_conserves_norm. exact HU.
  - apply evolution_conserves_energy.
    apply isometry_commuting_preserves_energy; assumption.
Qed.

(** Example: the Cayley step commutes with H = e 1 (one level in the real
    coordinates (Re, Im)) and conserves the norm and the energy. *)
Example cayley_evolution_conserves_both : forall (t e : Q) (v : nat -> Q) (n : nat),
  let U := rotation (cn_c t) (cn_s t) in
  seq_inner (evolve U 2 v n) (evolve U 2 v n) 2 == seq_inner v v 2
  /\ energy (Hdiag e e) (evolve U 2 v n) 2 == energy (Hdiag e e) v 2.
Proof.
  intros t e v n U. apply commuting_isometric_evolution_conserves_both.
  - apply cayley_step_isometry.
  - intros w i Hi. unfold op_apply, rotation, Hdiag.
    destruct i as [|[|i]]; [ cbn [q_sum]; ring | cbn [q_sum]; ring | lia ].
Qed.

(* ===================================================================== *)
(*  4. The boundary of existence of an eigenvector                      *)
(* ===================================================================== *)

(** A symmetric rational matrix without a rational eigenvector:
    T = [[1,1],[1,-1]], whose eigenvalues are +-sqrt 2. *)
Example symmetric_without_rational_eigenvector :
  let T := fun i j : nat =>
             match i, j with
             | O, O => 1 | O, S O => 1 | S O, O => 1 | S O, S O => - (1)
             | _, _ => 0
             end in
  op_symmetric T 2
  /\ forall (v : nat -> Q) (lam : Q),
       is_eigenpair T v lam 2 -> v 0%nat == 0 /\ v 1%nat == 0.
Proof.
  intro T. split.
  - intros i j Hi Hj.
    destruct i as [|[|i]]; destruct j as [|[|j]]; try lia; reflexivity.
  - intros v lam He.
    assert (H0 := He 0%nat ltac:(lia)). assert (H1 := He 1%nat ltac:(lia)).
    unfold op_apply, T in H0, H1. cbn [q_sum] in H0, H1.
    assert (E0 : lam * v 0%nat == v 0%nat + v 1%nat) by lra.
    assert (E1 : lam * v 1%nat == v 0%nat - v 1%nat) by lra.
    assert (Hz : (lam * lam - 2) * v 1%nat == 0).
    { setoid_replace ((lam * lam - 2) * v 1%nat)
        with (lam * (lam * v 1%nat) - 2 * v 1%nat) by ring.
      rewrite E1.
      setoid_replace (lam * (v 0%nat - v 1%nat))
        with (lam * v 0%nat - lam * v 1%nat) by ring.
      rewrite E0, E1. ring. }
    destruct (Qmult_integral _ _ Hz) as [Hl | Hv1].
    + exfalso. apply (Sqrt2Irrational.no_rational_sqrt2 lam). lra.
    + split; [ | exact Hv1 ].
      rewrite Hv1 in E1. lra.
Qed.

