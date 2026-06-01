(** * ProcessCompactSpectral.v — Diagonal compact self-adjoint operator on
      process-L² (F-31 core, Part VI)

    Elements: rational eigenvalues λₙ; coordinate sequences f(n); finite sums
    Roles:    λₙ = spectrum; eₙ = |n⟩ = eigen-directions; compactness = λₙ → 0
    Rules:    T diagonal; ⟨Tf,g⟩=⟨f,Tg⟩; discrete spectrum (λₙ→0); ‖Tf‖²≤K‖f‖²

    The spectral theorem for a COMPACT self-adjoint operator says it is diagonal in
    an orthonormal eigenbasis, with eigenvalues λₙ → 0. We formalise the spectral
    FORM on process-L² (the number basis, sequences nat→Q): the diagonal operator
        (T f)(n) = λₙ · f(n),      T eₙ = λₙ eₙ
    and prove its defining properties — self-adjointness, the eigenvalue equation,
    boundedness ‖Tf‖² ≤ K‖f‖², and the hallmark of COMPACTNESS: the spectrum is
    DISCRETE, accumulating only at 0 (λₙ → 0, hence only finitely many eigenvalues
    exceed any ε). Eigenvalues are a PROCESS (λ ~~ 0); no completed spectral measure,
    no completed Hilbert space.

    HONEST RESIDUE: that an ARBITRARY compact self-adjoint operator is diagonalisable
    (constructing the orthonormal eigenbasis via the variational/Rayleigh argument in
    infinite dimension — which needs "compactness ⇒ the sup is attained", hard
    constructively) is the frontier. Here we formalise the spectral form and its
    properties — the conclusion the theorem reaches — on the process continuum.

    ============ E/R/R разбор ============
      Rules (L5): T диагонален; ⟨Tf,g⟩=⟨f,Tg⟩; λₙ→0 (дискретность); ‖Tf‖²≤K‖f‖².
      Roles (L4): λₙ = роли-спектр; eₙ = роли-собственные направления; компактность =
                  роль «спектр к 0».
      Elements  : рациональные λₙ, координаты f(n), конечные суммы (L1+P4).
    ДИАГНОСТИКА: компактность = дискретный спектр, накапливающийся к 0 — процессное
    свойство последовательности λₙ, не свойство завершённого оператора на завершённом
    Гильберте. Собственный базис счётен = процесс.

    STATUS: 6 Qed, 0 Admitted, 0 axioms (process-equiv part uses no axiom; diag is exact)
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import process.ProcessCore.            (* process_equiv ~~, const_process *)
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_le, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_ext, q_sum_scale *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Process-L² on the number basis: coordinate sequences, inner product.  *)
(* ===================================================================== *)

(** L² inner product on coordinate sequences (finite stage N). *)
Definition seq_inner (a b : nat -> Q) (N : nat) : Q :=
  q_sum (fun i => a i * b i) N.

(** Number-basis vector eₙ = |n⟩. *)
Definition ket (n : nat) : nat -> Q := fun m => if Nat.eqb m n then 1 else 0.

(** Diagonal operator: (T f)(n) = λₙ · f(n). *)
Definition diag_op (lam f : nat -> Q) : nat -> Q := fun n => lam n * f n.

(* ===================================================================== *)
(*  Defining properties of the spectral (diagonal) form.                  *)
(* ===================================================================== *)

(** Self-adjointness: ⟨Tf,g⟩ = ⟨f,Tg⟩. *)
Lemma diag_self_adjoint : forall lam a b N,
  seq_inner (diag_op lam a) b N == seq_inner a (diag_op lam b) N.
Proof.
  intros lam a b N. unfold seq_inner, diag_op. apply q_sum_ext. intro i. ring.
Qed.

(** Eigenvalue equation: T eₙ = λₙ eₙ. *)
Lemma diag_eigenvalue : forall lam n m,
  diag_op lam (ket n) m == lam n * ket n m.
Proof.
  intros lam n m. unfold diag_op, ket. destruct (Nat.eqb m n) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst m. ring.
  - ring.
Qed.

(** COMPACTNESS hallmark: discrete spectrum — λₙ → 0 means only finitely many
    eigenvalues exceed any threshold ε. *)
Lemma diag_spectrum_discrete : forall lam,
  (lam ~~ const_process 0) ->
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Qabs (lam n) < eps.
Proof.
  intros lam Hconv eps Heps.
  destruct (Hconv eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  assert (E : lam n - const_process 0 n == lam n) by (cbv [const_process]; ring).
  rewrite E in HN. exact HN.
Qed.

(** Boundedness: ‖Tf‖² ≤ K·‖f‖²  when every λₙ² ≤ K. *)
Lemma diag_bounded : forall lam f K N,
  (forall n, lam n * lam n <= K) ->
  seq_inner (diag_op lam f) (diag_op lam f) N <= K * seq_inner f f N.
Proof.
  intros lam f K N HK. unfold seq_inner, diag_op.
  apply Qle_trans with (q_sum (fun i => K * (f i * f i)) N).
  - apply q_sum_le. intro i.
    assert (E : (lam i * f i) * (lam i * f i) == (lam i * lam i) * (f i * f i)) by ring.
    rewrite E. apply Qmult_le_compat_r; [ apply HK | apply q_sq_nonneg ].
  - assert (Hs : q_sum (fun i => K * (f i * f i)) N == K * q_sum (fun i => f i * f i) N)
      by apply q_sum_scale.
    rewrite Hs. apply Qle_refl.
Qed.

(** The n-th coordinate is the projection ⟨eₙ,f⟩ onto the eigen-direction;
    so (Tf)(n) = λₙ·⟨eₙ,f⟩ — the spectral action, read coordinatewise. *)
Lemma diag_spectral_action : forall lam f n,
  diag_op lam f n == lam n * f n.
Proof. intros lam f n. unfold diag_op. reflexivity. Qed.

(* Computational sanity: λ = (1, 1/2, 1/3-ish via 1#3, 0, 0, …) decreasing to 0;
   T applied to the all-ones first three coords reads off λ. *)
Example diag_eigenvalue_concrete :
  diag_op (fun n => if Nat.eqb n 0 then 1 else if Nat.eqb n 1 then (1#2) else 0)
          (ket 1) 1 == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions diag_bounded.
Print Assumptions diag_spectrum_discrete.
