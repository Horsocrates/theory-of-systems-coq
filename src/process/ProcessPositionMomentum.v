(** * ProcessPositionMomentum.v — Lattice position & momentum: the commutator
      defect made explicit (Tier 2, Part VI → physics)

    Elements: rational lattice positions x_i; difference operator p̂; basis vectors e_j
    Roles:    q̂ = position (multiplication by x_i); x_i = eigenvalue (lattice point);
              p̂ = momentum (difference); [q̂,p̂] = the forced commutator defect
    Rules:    (q̂v)_i = x_i v_i; q̂ e_j = x_j e_j; q̂ self-adjoint (diagonal);
              [q̂,p̂]_ij = (x_i − x_j) p̂_ij ⟹ the diagonal vanishes ⟹ [q̂,p̂] ≠ iℏI

    A concrete lattice realisation of position and momentum. The position operator q̂
    is diagonal: it acts by multiplication by the lattice coordinate x_i, is
    self-adjoint, and its eigenvectors are the basis states e_j with eigenvalues x_j
    (the lattice points). The momentum p̂ is a finite-difference operator. Because q̂
    is diagonal, [q̂,p̂]_ij = (x_i − x_j) p̂_ij, so the commutator has an identically
    ZERO diagonal — it can never equal iℏI. This is the concrete realisation of the
    obstruction (ProcessCanonicalCommutator.no_finite_ccr): on N = 3 we exhibit the
    explicit defect ([q̂,p̂] is −shift, off-diagonal, trace 0), all over ℚ.

    HONEST FRONTIER (P4 boundary): the exact CCR [q̂,p̂] = iℏI is a role-limit
    (continuum); every finite lattice carries the defect shown here. Explicit operator
    domains and the Schrödinger evolution are the next bricks.

    ============ E/R/R разбор ============
      Rules (L5): (q̂v)_i=x_i v_i; q̂ e_j=x_j e_j; q̂ самосопряжена; [q̂,p̂]_ij=(x_i−x_j)p̂_ij
                  ⟹ нулевая диагональ ⟹ [q̂,p̂]≠iℏI.
      Roles (L4): q̂=роль-позиция (мультипликатор); x_i=роль-собств.значение (точка решётки);
                  p̂=роль-импульс (разность); [q̂,p̂]=роль-дефект (внедиаг., след 0).
      Elements  : рациональные x_i, элементы p̂, конечная решётка N узлов, базис e_j (L1+P4).
    ДИАГНОСТИКА: дефект коммутатора на решётке — конкретная реализация обструкции
    no_finite_ccr; точный CCR=iℏI = роль-предел (континуум), P4-граница.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_zero *)
From ToS Require Import process.ProcessL2BesselGeneral. (* q_sum_ext_bounded *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply, op_symmetric, is_eigenpair *)
From ToS Require Import process.ProcessCanonicalCommutator. (* mat_mul, mat_sub, mat_trace *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Diagonal extraction: Σ_{k<N} (if i=k then a else 0) · g k = a · g i.   *)
(* ===================================================================== *)

Lemma q_sum_delta : forall (a : Q) (g : nat -> Q) (i N : nat),
  (i < N)%nat ->
  q_sum (fun k => (if (i =? k)%nat then a else 0) * g k) N == a * g i.
Proof.
  intros a g i N. induction N as [|n IH]; intro Hi.
  - lia.
  - cbn [q_sum]. cbn beta.
    destruct (Nat.eqb i n) eqn:E; cbv iota.
    + apply Nat.eqb_eq in E. subst n.
      assert (Hz : q_sum (fun k => (if (i =? k)%nat then a else 0) * g k) i == 0).
      { transitivity (q_sum (fun _ : nat => 0) i).
        - apply q_sum_ext_bounded. intros k Hk. cbn beta.
          assert (H0 : (if (i =? k)%nat then a else 0) == 0).
          { assert (Hik : (i =? k)%nat = false) by (apply Nat.eqb_neq; lia).
            rewrite Hik. reflexivity. }
          rewrite H0. ring.
        - apply q_sum_zero. }
      rewrite Hz. ring.
    + assert (Hi' : (i < n)%nat) by (apply Nat.eqb_neq in E; lia).
      rewrite (IH Hi'). ring.
Qed.

(* ===================================================================== *)
(*  Position operator (diagonal) and basis vectors.                       *)
(* ===================================================================== *)

(** Position: q̂ acts by multiplication by the lattice coordinate x_i. *)
Definition qhat (x : nat -> Q) : nat -> nat -> Q :=
  fun i j => if (i =? j)%nat then x i else 0.

(** Standard basis vector e_j. *)
Definition basis_vec (j : nat) : nat -> Q :=
  fun k => if (k =? j)%nat then 1 else 0.

(** Position acts diagonally: (q̂ v)_i = x_i · v_i. *)
Lemma position_apply : forall (x v : nat -> Q) (N i : nat),
  (i < N)%nat -> op_apply (qhat x) v N i == x i * v i.
Proof.
  intros x v N i Hi. unfold op_apply, qhat. cbn beta.
  apply (q_sum_delta (x i) v i N Hi).
Qed.

(** Position is self-adjoint (its matrix is symmetric — diagonal). *)
Lemma position_symmetric : forall (x : nat -> Q) (N : nat),
  op_symmetric (qhat x) N.
Proof.
  intros x N i j Hi Hj. unfold qhat.
  destruct (Nat.eqb i j) eqn:E.
  - apply Nat.eqb_eq in E. subst j. rewrite Nat.eqb_refl. reflexivity.
  - assert (Eji : (j =? i)%nat = false)
      by (apply Nat.eqb_neq; apply Nat.eqb_neq in E; lia).
    rewrite Eji. reflexivity.
Qed.

(** The basis vector e_j is an eigenvector of q̂ with eigenvalue x_j (the lattice
    point): q̂ e_j = x_j e_j. *)
Lemma position_eigenpair : forall (x : nat -> Q) (N j : nat),
  (j < N)%nat -> is_eigenpair (qhat x) (basis_vec j) (x j) N.
Proof.
  intros x N j Hj i Hi.
  rewrite (position_apply x (basis_vec j) N i Hi).
  unfold basis_vec. cbn beta.
  destruct (Nat.eqb i j) eqn:E; cbv iota.
  - apply Nat.eqb_eq in E. subst j. reflexivity.
  - ring.
Qed.

(* ===================================================================== *)
(*  Concrete N = 3 lattice: the commutator defect.                        *)
(*    x_i = i, p̂ = forward difference (p̂_{i,i+1}=1, p̂_{i,i}=−1).          *)
(*    [q̂,p̂] has zero diagonal (≠ iℏI) and equals −shift; trace = 0.       *)
(* ===================================================================== *)

(** The commutator has an identically zero diagonal — hence is not iℏI. *)
Example commutator_qp_zero_diagonal_N3 :
  let X := fun i => inject_Z (Z.of_nat i) in
  let q := qhat X in
  let p := fun i j => if (j =? S i)%nat then 1 else (if (i =? j)%nat then - (1) else 0) in
  let C := mat_sub (mat_mul q p 3%nat) (mat_mul p q 3%nat) in
  C 0%nat 0%nat == 0 /\ C 1%nat 1%nat == 0 /\ C 2%nat 2%nat == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The explicit defect: [q̂,p̂] = −(forward shift), i.e. −1 on the super-diagonal. *)
Example commutator_qp_defect_N3 :
  let X := fun i => inject_Z (Z.of_nat i) in
  let q := qhat X in
  let p := fun i j => if (j =? S i)%nat then 1 else (if (i =? j)%nat then - (1) else 0) in
  let C := mat_sub (mat_mul q p 3%nat) (mat_mul p q 3%nat) in
  C 0%nat 1%nat == - (1) /\ C 1%nat 2%nat == - (1)
  /\ mat_trace C 3%nat == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Print Assumptions position_eigenpair.
Print Assumptions commutator_qp_defect_N3.
