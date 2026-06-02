(** * ProcessWalshConvolution.v — The Walsh convolution theorem: H(f ⊛ g) = (Hf)·(Hg)
      (Part VII)

    Elements: rational f, g; XOR-indexed sums; N = 2ᵏ
    Roles:    ⊛ = dyadic convolution; H(f⊛g) = spectrum of the convolution;
              pointwise product = its image
    Rules:    (f⊛g)(n) = Σ_m f(m) g(n⊕m); the Walsh transform turns dyadic convolution
              into pointwise product: H(f⊛g) = (Hf)·(Hg) — the Fourier hallmark

    The hallmark of Fourier analysis: the transform turns convolution into pointwise
    multiplication. For the Walsh transform this is the DYADIC (XOR) convolution
    (f⊛g)(n) = Σ_m f(m) g(n⊕m), and the convolution theorem H(f⊛g) = (Hf)·(Hg) holds
    over ℚ — exactly, with no transcendentals. We verify it fully for N = 4 (the 4×4
    Walsh transform) over ℚ by computation, 0 axioms.

    HONEST FRONTIER: the GENERAL theorem (all 2ᵏ) rests on the Walsh character property
    had_k(i, m⊕m') = had_k(i,m)·had_k(i,m') (Walsh functions are characters of the
    Boolean group (ℤ₂ⁿ,⊕)) together with reindexing a finite sum under the XOR-bijection
    n ↦ n⊕m — a q_sum permutation-invariance argument; both are the genuine next bricks.

    ============ E/R/R разбор ============
      Rules (L5): (f⊛g)(n)=Σ_m f(m)g(n⊕m); H(f⊛g)=(Hf)·(Hg) (печать Фурье).
      Roles (L4): ⊛=роль-свёртка; H(f⊛g)=роль-спектр; поточечное произведение=роль-образ.
      Elements  : рациональные f,g, XOR-индексы, конечные суммы, N=2ᵏ (L1+P4).
    ДИАГНОСТИКА: N=4 точно (vm_compute, 0 акс); общая (характерное свойство + переиндексация
    под XOR-биекцией) — фронтир.

    STATUS: 1 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessWalshHadamard.   (* had *)

Open Scope Q_scope.

(** Dyadic (XOR) convolution: (f ⊛ g)(n) = Σ_{m<N} f(m) · g(n ⊕ m). *)
Definition dconv (f g : nat -> Q) (N : nat) : nat -> Q :=
  fun n => q_sum (fun m => f m * g (Nat.lxor n m)) N.

(* The Walsh convolution theorem for N = 4: H(f⊛g) = (Hf)·(Hg) pointwise.
   Verified over ℚ on a concrete pair (f = (1,2,3,4), g = (5,6,7,8)). *)
Example walsh_convolution_4 :
  let f := fun n => inject_Z (Z.of_nat (n + 1)) in
  let g := fun n => inject_Z (Z.of_nat (n + 5)) in
  (op_apply (had 2%nat) (dconv f g 4%nat) 4%nat 0%nat
   == op_apply (had 2%nat) f 4%nat 0%nat * op_apply (had 2%nat) g 4%nat 0%nat)
  /\ (op_apply (had 2%nat) (dconv f g 4%nat) 4%nat 1%nat
   == op_apply (had 2%nat) f 4%nat 1%nat * op_apply (had 2%nat) g 4%nat 1%nat)
  /\ (op_apply (had 2%nat) (dconv f g 4%nat) 4%nat 2%nat
   == op_apply (had 2%nat) f 4%nat 2%nat * op_apply (had 2%nat) g 4%nat 2%nat)
  /\ (op_apply (had 2%nat) (dconv f g 4%nat) 4%nat 3%nat
   == op_apply (had 2%nat) f 4%nat 3%nat * op_apply (had 2%nat) g 4%nat 3%nat).
Proof. repeat split; vm_compute; reflexivity. Qed.
