(** * ProcessSelfAdjointSpectral.v — Spectral structure of a self-adjoint operator:
      self-adjointness, Rayleigh, eigenvector orthogonality (F-31 frontier, Part VI)

    Elements: rational matrix entries T i j; coordinates v i; finite sums Σ_{i,j<N}
    Roles:    ⟨·,·⟩ = pairing; T = symmetric operator; λ = (real) eigenvalue;
              orthogonality of eigenspaces = role-separation
    Rules:    ⟨Tv,w⟩ = ⟨v,Tw⟩ (self-adjoint, via the commuting double sum);
              ⟨Tv,v⟩ = λ‖v‖² (Rayleigh); distinct eigenvalues ⟹ ⟨v,w⟩ = 0

    The structural core of the spectral theorem for a self-adjoint (symmetric)
    operator, proved constructively over ℚ with 0 axioms: self-adjointness
    ⟨Tv,w⟩ = ⟨v,Tw⟩ (a discrete-Fubini swap plus symmetry), the Rayleigh identity
    ⟨Tv,v⟩ = λ‖v‖², and — the key result — eigenvectors for distinct eigenvalues are
    orthogonal. A concrete 2×2 rational diagonalisation (T = [[1,2],[2,1]], eigenpairs
    (1,1)↦3 and (1,−1)↦−1, orthogonal) is machine-checked.

    HONEST FRONTIER (P4 boundary): the EXISTENCE of an eigenvector for an arbitrary
    self-adjoint / compact operator — the maximiser of the Rayleigh quotient, the
    "compactness ⟹ the sup is attained" step — is NOT proved. Over ℚ the eigenvalues
    are generally irrational (√ of the discriminant) and existence needs
    completeness/compactness; this is the same boundary as EVT (we attain the argmax
    only on a finite grid, not on the continuum). The full orthonormal BASIS of an
    arbitrary compact operator (the deflation iteration to completeness) is likewise a
    role-limit. We prove the algebraic structure and a concrete rational instance.

    ============ E/R/R разбор ============
      Rules (L5): ⟨Tv,w⟩=⟨v,Tw⟩ (симметрия+Фубини-swap); ⟨Tv,v⟩=λ‖v‖² (Рэлей);
                  λ≠μ ⟹ ⟨v,w⟩=0 (ортогональность собственных векторов).
      Roles (L4): ⟨·,·⟩ = роль-спаривание; T = роль-оператор; λ = роль-собственное-
                  значение (вещественное над ℚ); ортогональность = роль-разделение.
      Elements  : рациональные T i j, координаты v i, конечные суммы Σ_{i,j<N} (L1+P4).
    ДИАГНОСТИКА: структура + конкретная диагонализация — процессный факт (0 акс);
    СУЩЕСТВОВАНИЕ собств. вектора произвольного («sup достигается», λ иррационально) и
    полный ортобазис (дефляция) — роль-предел, P4-граница (как у EVT: argmax на сетке).

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_swap, q_sum_scale, q_sum_ext *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2BesselGeneral. (* q_sum_ext_bounded *)

Open Scope Q_scope.

(** A matrix T acts on a vector v over the first N coordinates. *)
Definition op_apply (T : nat -> nat -> Q) (v : nat -> Q) (N : nat) : nat -> Q :=
  fun i => q_sum (fun j => T i j * v j) N.

(** T is self-adjoint on N coordinates iff its matrix is symmetric there. *)
Definition op_symmetric (T : nat -> nat -> Q) (N : nat) : Prop :=
  forall i j, (i < N)%nat -> (j < N)%nat -> T i j == T j i.

(** An eigenpair: T v = λ v on the first N coordinates. *)
Definition is_eigenpair (T : nat -> nat -> Q) (v : nat -> Q) (lam : Q) (N : nat) : Prop :=
  forall i, (i < N)%nat -> op_apply T v N i == lam * v i.

(* ===================================================================== *)
(*  ⟨Tv,w⟩ and ⟨v,Tw⟩ as explicit double sums.                           *)
(* ===================================================================== *)

Lemma inner_op_left : forall (T : nat -> nat -> Q) (v w : nat -> Q) (N : nat),
  seq_inner (op_apply T v N) w N
  == q_sum (fun i => q_sum (fun j => T i j * v j * w i) N) N.
Proof.
  intros T v w N. unfold seq_inner, op_apply. cbn beta.
  apply q_sum_ext. intro i.
  transitivity (w i * q_sum (fun j => T i j * v j) N).
  - ring.
  - transitivity (q_sum (fun j => w i * (T i j * v j)) N).
    + symmetry. apply q_sum_scale.
    + apply q_sum_ext. intro j. ring.
Qed.

Lemma inner_op_right : forall (T : nat -> nat -> Q) (v w : nat -> Q) (N : nat),
  seq_inner v (op_apply T w N) N
  == q_sum (fun i => q_sum (fun j => T i j * w j * v i) N) N.
Proof.
  intros T v w N. unfold seq_inner, op_apply. cbn beta.
  apply q_sum_ext. intro i.
  transitivity (q_sum (fun j => v i * (T i j * w j)) N).
  - symmetry. apply q_sum_scale.
  - apply q_sum_ext. intro j. ring.
Qed.

(* ===================================================================== *)
(*  Self-adjointness: ⟨Tv,w⟩ = ⟨v,Tw⟩ for a symmetric T.                  *)
(* ===================================================================== *)

Theorem adjoint_inner : forall (T : nat -> nat -> Q) (v w : nat -> Q) (N : nat),
  op_symmetric T N ->
  seq_inner (op_apply T v N) w N == seq_inner v (op_apply T w N) N.
Proof.
  intros T v w N Hsym.
  rewrite inner_op_left, inner_op_right.
  transitivity (q_sum (fun j => q_sum (fun i => T i j * v j * w i) N) N).
  - apply (q_sum_swap (fun i j => T i j * v j * w i) N N).
  - apply q_sum_ext_bounded. intros a Ha. cbn beta.
    apply q_sum_ext_bounded. intros b Hb. cbn beta.
    rewrite (Hsym b a Hb Ha). ring.
Qed.

(* ===================================================================== *)
(*  Rayleigh identity and the eigen-pairing reductions.                   *)
(* ===================================================================== *)

(** Rayleigh: ⟨Tv,v⟩ = λ‖v‖² for an eigenpair. *)
Theorem rayleigh_eq : forall (T : nat -> nat -> Q) (v : nat -> Q) (lam : Q) (N : nat),
  is_eigenpair T v lam N ->
  seq_inner (op_apply T v N) v N == lam * seq_inner v v N.
Proof.
  intros T v lam N He. unfold seq_inner.
  transitivity (q_sum (fun i => lam * (v i * v i)) N).
  - apply q_sum_ext_bounded. intros i Hi. cbn beta. rewrite (He i Hi). ring.
  - apply q_sum_scale.
Qed.

(** ⟨Tv,w⟩ = λ⟨v,w⟩ when v is an eigenvector. *)
Lemma inner_op_eig_left : forall (T : nat -> nat -> Q) (v w : nat -> Q) (lam : Q) (N : nat),
  is_eigenpair T v lam N ->
  seq_inner (op_apply T v N) w N == lam * seq_inner v w N.
Proof.
  intros T v w lam N He. unfold seq_inner.
  transitivity (q_sum (fun i => lam * (v i * w i)) N).
  - apply q_sum_ext_bounded. intros i Hi. cbn beta. rewrite (He i Hi). ring.
  - apply q_sum_scale.
Qed.

(** ⟨v,Tw⟩ = μ⟨v,w⟩ when w is an eigenvector. *)
Lemma inner_op_eig_right : forall (T : nat -> nat -> Q) (v w : nat -> Q) (mu : Q) (N : nat),
  is_eigenpair T w mu N ->
  seq_inner v (op_apply T w N) N == mu * seq_inner v w N.
Proof.
  intros T v w mu N He. unfold seq_inner.
  transitivity (q_sum (fun i => mu * (v i * w i)) N).
  - apply q_sum_ext_bounded. intros i Hi. cbn beta. rewrite (He i Hi). ring.
  - apply q_sum_scale.
Qed.

(* ===================================================================== *)
(*  Eigenvectors for distinct eigenvalues are orthogonal.                 *)
(* ===================================================================== *)

Theorem eigvec_orthogonal :
  forall (T : nat -> nat -> Q) (v w : nat -> Q) (lam mu : Q) (N : nat),
  op_symmetric T N ->
  is_eigenpair T v lam N ->
  is_eigenpair T w mu N ->
  ~ (lam == mu) ->
  seq_inner v w N == 0.
Proof.
  intros T v w lam mu N Hsym Hv Hw Hne.
  assert (Hcomb : lam * seq_inner v w N == mu * seq_inner v w N).
  { rewrite <- (inner_op_eig_left T v w lam N Hv).
    rewrite (adjoint_inner T v w N Hsym).
    apply (inner_op_eig_right T v w mu N Hw). }
  assert (Hz : (lam - mu) * seq_inner v w N == 0).
  { assert (Hr : (lam - mu) * seq_inner v w N
                 == lam * seq_inner v w N - mu * seq_inner v w N) by ring.
    rewrite Hr, Hcomb. ring. }
  destruct (Qmult_integral _ _ Hz) as [Hd | HS].
  - exfalso. apply Hne. lra.
  - exact HS.
Qed.

(* Concrete 2×2 diagonalisation over ℚ: T = [[1,2],[2,1]],
   eigenpair (1,1) ↦ 3, eigenpair (1,−1) ↦ −1, and the two are orthogonal. *)
Example spectral_2x2_concrete :
  let T := fun i j => if (i =? j)%nat then 1 else 2 in
  let v := fun _ : nat => 1 in
  let w := fun n => if (n =? 0)%nat then 1 else - (1) in
  (op_apply T v 2%nat 0%nat == 3 * v 0%nat
   /\ op_apply T v 2%nat 1%nat == 3 * v 1%nat)
  /\ (op_apply T w 2%nat 0%nat == (- (1)) * w 0%nat
      /\ op_apply T w 2%nat 1%nat == (- (1)) * w 1%nat)
  /\ seq_inner v w 2%nat == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Print Assumptions adjoint_inner.
Print Assumptions eigvec_orthogonal.
