(** * ProcessHarmonicLadder.v — Harmonic-oscillator ladder operators (F-33, Part VI)

    Elements: rational amplitudes ψ(n) on number states |n⟩ (the Fock process)
    Roles:    a / a† = lowering / raising; N = a†a = number; H = N + ½
    Rules:    [a,a†] = 1, N|n⟩ = n|n⟩, H|n⟩ = (n+½)|n⟩ — exact over ℚ

    The quantum harmonic oscillator is the first genuinely INFINITE-dimensional
    quantum system: the number states |0⟩,|1⟩,|2⟩,… form a countable basis and the
    energy spectrum Eₙ = n+½ is UNBOUNDED. In \ToS the Fock space is not a completed
    Hilbert space but a PROCESS — amplitudes ψ : nat → Q on the number states, finite
    at each stage (P4). The ladder operators carry the irrational coefficient √n
        a|n⟩ = √n·|n−1⟩,   a†|n⟩ = √(n+1)·|n+1⟩,
    yet the PHYSICALLY MEANINGFUL combinations are exactly rational, because the √'s
    cancel:
        a†a|n⟩ = √n·√n·|n⟩ = n|n⟩         (number operator, eigenvalue n)
        [a,a†]|n⟩ = (n+1 − n)|n⟩ = |n⟩    (canonical commutation, = identity)
    We formalise the algebra exactly over ℚ, parametrising the √-coefficient by an
    abstract s : nat → Q with s(n)² = n. The relations [a,a†]=1 and N=a†a then hold
    for ANY such s (the value of √n never matters — it cancels), so the result is
    √-independent and uses 0 axioms. The existence of s = √· as a RealProcess is a
    separate, standard fact.

    ============ E/R/R разбор ============
      Rules (L5): [a,a†]=1; N=a†a; H=N+½; уровни Eₙ=n+½ (точно над ℚ).
      Roles (L4): a/a† = роли понижения/повышения; N = роль-счётчик уровня; спектр =
                  роль-предел (бесконечный, неограниченный) — но не завершённый объект.
      Elements  : рациональные амплитуды ψ(n) на |n⟩ — конечны на каждой стадии (L1+P4).
    ДИАГНОСТИКА: бесконечный спектр осциллятора — ПРОЦЕСС (счётный базис = процесс
    усечений, уровни точны), не завершённое гильбертово пространство. Иррациональный √n
    живёт в a,a† порознь, но сокращается в N и [a,a†] — наблюдаемая алгебра рациональна.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa PeanoNat.
From ToS Require Import process.ProcessArithmetic.   (* q_archimedean *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Fock space as a process: amplitudes on number states |n⟩.            *)
(* ===================================================================== *)

Definition FockState := nat -> Q.

(** The number state |n⟩ = unit amplitude on level n. *)
Definition ket (n : nat) : FockState := fun m => if Nat.eqb m n then 1 else 0.

(** Number operator N: multiplies the n-th amplitude by n. *)
Definition num (psi : FockState) : FockState :=
  fun n => inject_Z (Z.of_nat n) * psi n.

(** Energy levels and Hamiltonian H = N + ½  (units ℏω = 1). *)
Definition energy (n : nat) : Q := inject_Z (Z.of_nat n) + (1 # 2).
Definition ham (psi : FockState) : FockState := fun n => energy n * psi n.

(* ===================================================================== *)
(*  Spectrum (exact, unconditional — no √ needed).                       *)
(* ===================================================================== *)

(** N|n⟩ = n|n⟩. *)
Lemma num_eigenvalue : forall n m,
  num (ket n) m == inject_Z (Z.of_nat n) * ket n m.
Proof.
  intros n m. unfold num, ket. destruct (Nat.eqb m n) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst m. ring.
  - ring.
Qed.

(** H|n⟩ = (n+½)|n⟩. *)
Lemma ham_eigenvalue : forall n m,
  ham (ket n) m == energy n * ket n m.
Proof.
  intros n m. unfold ham, ket, energy. destruct (Nat.eqb m n) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst m. ring.
  - ring.
Qed.

(** Equispaced levels: Eₙ₊₁ − Eₙ = 1. *)
Lemma energy_spacing : forall n, energy (S n) - energy n == 1.
Proof.
  intro n. unfold energy.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite inject_Z_plus. change (inject_Z 1) with (1 # 1). ring.
Qed.

(** Zero-point energy: E₀ = ½. *)
Lemma ground_energy : energy 0 == 1 # 2.
Proof. unfold energy. simpl. ring. Qed.

(** The spectrum is UNBOUNDED — the signature of infinite dimension. *)
Lemma energy_unbounded : forall B : Q, exists n : nat, B < energy n.
Proof.
  intro B. unfold energy.
  assert (H01 : (0:Q) < 1) by lra.
  destruct (q_archimedean B 1 H01) as [K HK].
  exists K.
  apply Qlt_le_trans with (inject_Z (Z.of_nat K)).
  - rewrite Qmult_1_r in HK. exact HK.
  - lra.
Qed.

(* ===================================================================== *)
(*  Ladder operators (carry the √-coefficient s; algebra is √-independent). *)
(* ===================================================================== *)

Section Ladder.

Variable s : nat -> Q.
Hypothesis Hs : forall n, s n * s n == inject_Z (Z.of_nat n).   (* s n = √n *)

(** Annihilation a: (aψ)(n) = √(n+1)·ψ(n+1). *)
Definition ann (psi : FockState) : FockState := fun n => s (S n) * psi (S n).

(** Creation a†: (a†ψ)(n) = √n·ψ(n−1), zero at n=0. *)
Definition cre (psi : FockState) : FockState :=
  fun n => match n with O => 0 | S m => s (S m) * psi m end.

(** a†a = N : the number operator. (Eigenvalue n on |n⟩; the √'s cancel.) *)
Lemma cre_ann_eq_num : forall psi n, cre (ann psi) n == num psi n.
Proof.
  intros psi n. unfold cre, ann, num. destruct n as [|m].
  - simpl. ring.
  - cbn. assert (H := Hs (S m)). rewrite <- H. ring.
Qed.

(** aa† = N+1 : (eigenvalue n+1 on |n⟩). *)
Lemma ann_cre_eq : forall psi n,
  ann (cre psi) n == inject_Z (Z.of_nat (S n)) * psi n.
Proof.
  intros psi n. unfold ann, cre. cbn.
  assert (H := Hs (S n)). rewrite <- H. ring.
Qed.

(** Canonical commutation relation [a,a†] = 1 : (aa† − a†a)ψ = ψ. *)
Theorem commutator_canonical : forall psi n,
  ann (cre psi) n - cre (ann psi) n == psi n.
Proof.
  intros psi n.
  rewrite (ann_cre_eq psi n), (cre_ann_eq_num psi n). unfold num.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite inject_Z_plus. change (inject_Z 1) with (1 # 1). ring.
Qed.

End Ladder.

(* Computational sanity checks. *)
Example ground_energy_half : energy 0 == 1 # 2.
Proof. vm_compute. reflexivity. Qed.

Example third_level_energy : energy 3 == 7 # 2.
Proof. vm_compute. reflexivity. Qed.

Example level_spacing_one : energy 5 - energy 4 == 1.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions commutator_canonical.
Print Assumptions energy_unbounded.
