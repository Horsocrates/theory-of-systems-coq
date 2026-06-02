(** * ProcessFourierON.v — Orthonormal Fourier expansion: Plancherel for the
      Walsh transform via the operator framework (Part VII)

    Elements: rational amplitudes f_m, transform values (Hf)_i; finite sums Σ_{i,m<N}
    Roles:    H = transform; Hf = spectrum (Fourier coefficients); ‖Hf‖² = energy
    Rules:    H symmetric (Hᵢⱼ=Hⱼᵢ); H² = N·I (on f: H(Hf)=N·f); Plancherel ‖Hf‖²=N‖f‖²

    Connecting the abstract operator theory (self-adjointness, ProcessSelfAdjointSpectral)
    to the concrete Walsh–Hadamard transform (ProcessWalshHadamard): the Hadamard matrix
    is symmetric, so it is self-adjoint, and HᵀH = N·I gives H² = N·I, whence the Walsh
    transform applied twice rescales by N (H(Hf)=N·f — Fourier inversion up to 1/N), and
    Plancherel ‖Hf‖² = N‖f‖² (energy conservation of the Fourier–Walsh transform). All
    GENERAL in k (any N = 2ᵏ), over ℚ, 0 axioms — the rational Fourier–Parseval.

    HONEST FRONTIER: the unitary normalisation H/√N (giving ‖H f/√N‖² = ‖f‖², the
    orthonormal-basis Parseval Σ⟨eᵢ,f⟩²=‖f‖²) needs √N, rational only when N is a perfect
    square (e.g. N=4, √4=2); the complex DFT and the continuous Fourier transform need
    transcendentals — role-limits.

    ============ E/R/R разбор ============
      Rules (L5): H симметрична; H²=N·I (H(Hf)=N·f); Планшерель ‖Hf‖²=N‖f‖².
      Roles (L4): H = роль-преобразование; Hf = роль-спектр; ‖Hf‖² = роль-энергия.
      Elements  : рациональные f_m, (Hf)_i, конечные суммы Σ_{i,m<N}, N=2ᵏ (L1+P4).
    ДИАГНОСТИКА: над ℚ точно (0 акс); 1/√N рациональна лишь для N=квадрат — граница.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_ext, q_sum_scale, q_sum_swap *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply, op_symmetric, adjoint_inner *)
From ToS Require Import process.ProcessL2BesselGeneral. (* q_sum_ext_bounded *)
From ToS Require Import process.ProcessPositionMomentum.    (* q_sum_delta *)
From ToS Require Import process.ProcessWalshHadamard.   (* had, pow2, hadamard_orthogonal *)

Open Scope Q_scope.

(** The Sylvester–Hadamard matrix is symmetric. *)
Lemma had_symmetric : forall k i j, had k i j = had k j i.
Proof.
  induction k as [|k IH]; intros i j; cbn [had].
  - reflexivity.
  - rewrite (andb_comm (Nat.leb (pow2 k) i) (Nat.leb (pow2 k) j)).
    rewrite (IH (i mod pow2 k)%nat (j mod pow2 k)%nat). reflexivity.
Qed.

(** Hence H is self-adjoint as an operator on the first N coordinates. *)
Lemma walsh_op_symmetric : forall k, op_symmetric (had k) (pow2 k).
Proof. intros k i j _ _. rewrite (had_symmetric k i j). reflexivity. Qed.

(* ===================================================================== *)
(*  H² = N·I on f : applying the Walsh transform twice rescales by N.      *)
(*    (Fourier inversion up to the 1/N factor.)                            *)
(* ===================================================================== *)

Theorem walsh_HH : forall k f m, (m < pow2 k)%nat ->
  op_apply (had k) (op_apply (had k) f (pow2 k)) (pow2 k) m
  == inject_Z (Z.of_nat (pow2 k)) * f m.
Proof.
  intros k f m Hm. unfold op_apply. cbn beta.
  transitivity (q_sum (fun l => (if Nat.eqb m l then inject_Z (Z.of_nat (pow2 k)) else 0) * f l)
                      (pow2 k)).
  - transitivity (q_sum (fun j => q_sum (fun l => had k m j * (had k j l * f l)) (pow2 k)) (pow2 k)).
    + apply q_sum_ext. intro j. symmetry.
      apply (q_sum_scale (had k m j) (fun l => had k j l * f l) (pow2 k)).
    + transitivity (q_sum (fun l => q_sum (fun j => had k m j * (had k j l * f l)) (pow2 k)) (pow2 k)).
      * apply (q_sum_swap (fun j l => had k m j * (had k j l * f l)) (pow2 k) (pow2 k)).
      * apply q_sum_ext_bounded. intros l Hl.
        transitivity (f l * q_sum (fun j => had k m j * had k j l) (pow2 k)).
        -- transitivity (q_sum (fun j => f l * (had k m j * had k j l)) (pow2 k)).
           ++ apply q_sum_ext. intro j. ring.
           ++ apply (q_sum_scale (f l) (fun j => had k m j * had k j l) (pow2 k)).
        -- assert (Hml : q_sum (fun j => had k m j * had k j l) (pow2 k)
                         == (if Nat.eqb m l then inject_Z (Z.of_nat (pow2 k)) else 0)).
           { transitivity (q_sum (fun j => had k m j * had k l j) (pow2 k)).
             - apply q_sum_ext. intro j. rewrite (had_symmetric k j l). reflexivity.
             - exact (hadamard_orthogonal k m l Hm Hl). }
           rewrite Hml. ring.
  - exact (q_sum_delta (inject_Z (Z.of_nat (pow2 k))) f m (pow2 k) Hm).
Qed.

(* ===================================================================== *)
(*  Plancherel for the Walsh transform: ‖Hf‖² = N‖f‖².                    *)
(* ===================================================================== *)

Theorem parseval_walsh : forall k f,
  seq_inner (op_apply (had k) f (pow2 k)) (op_apply (had k) f (pow2 k)) (pow2 k)
  == inject_Z (Z.of_nat (pow2 k)) * seq_inner f f (pow2 k).
Proof.
  intros k f.
  rewrite (adjoint_inner (had k) f (op_apply (had k) f (pow2 k)) (pow2 k)
                         (walsh_op_symmetric k)).
  unfold seq_inner.
  transitivity (q_sum (fun m => f m * (inject_Z (Z.of_nat (pow2 k)) * f m)) (pow2 k)).
  - apply q_sum_ext_bounded. intros m Hm. rewrite (walsh_HH k f m Hm). reflexivity.
  - transitivity (q_sum (fun m => inject_Z (Z.of_nat (pow2 k)) * (f m * f m)) (pow2 k)).
    + apply q_sum_ext. intro m. ring.
    + apply (q_sum_scale (inject_Z (Z.of_nat (pow2 k))) (fun m => f m * f m) (pow2 k)).
Qed.

(* Concrete Plancherel for N = 4 on a sample state, as a sanity check. *)
Example parseval_walsh_4_concrete :
  let f := fun j => if Nat.eqb j 0%nat then 3 else (if Nat.eqb j 1%nat then 4 else 0) in
  seq_inner (op_apply (had 2%nat) f 4%nat) (op_apply (had 2%nat) f 4%nat) 4%nat
  == 4 * seq_inner f f 4%nat.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions parseval_walsh.
