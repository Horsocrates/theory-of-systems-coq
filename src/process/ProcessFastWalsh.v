(** * ProcessFastWalsh.v — The fast Walsh–Hadamard transform equals the matrix
      transform (Part VII): fast = process

    Elements: rational amplitudes f_i; halves f|lo, f|hi; recursion on k; N = 2ᵏ
    Roles:    fwht = the algorithm; the butterfly = one step; "fast = matrix" = correctness
    Rules:    butterfly H_{2N}f = [lo+hi ; lo−hi] of the transformed halves;
              fwht k f = op_apply (had k) f  (the recursive O(N log N) transform equals
              the N×N matrix transform)

    The Walsh–Hadamard transform admits a fast recursive (butterfly) algorithm, the
    analogue of the FFT, running in O(N log N) instead of O(N²). We define it by the
    Sylvester split — transform the two halves, then combine as lo+hi (top) and lo−hi
    (bottom) — and prove it computes EXACTLY the matrix transform op_apply (had k),
    for all N = 2ᵏ, over ℚ, 0 axioms. "Fast = process" made precise.

    HONEST FRONTIER: the O(N log N) complexity itself is an operational property (a
    statement about step counts), outside the equational core proved here.

    ============ E/R/R разбор ============
      Rules (L5): бабочка H_{2N}f=[lo+hi;lo−hi]; fwht k f = op_apply(had k) f (fast=matrix).
      Roles (L4): fwht=роль-алгоритм; бабочка=роль-шаг; fast=matrix=роль-корректность.
      Elements  : рациональные f_i, половины f|lo/f|hi, рекурсия по k, N=2ᵏ (L1+P4).
    ДИАГНОСТИКА: fast=matrix — точное тождество (0 акс); O(N log N) — операционное свойство.

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_scale *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessL2BesselGeneral. (* q_sum_ext_bounded *)
From ToS Require Import process.ProcessWalshHadamard.   (* had, pow2, pow2_pos, had_lo, had_hi, q_sum_split *)

Open Scope Q_scope.

(** The fast Walsh–Hadamard transform (Sylvester butterfly). *)
Fixpoint fwht (k : nat) (f : nat -> Q) : nat -> Q :=
  match k with
  | O => f
  | S k' =>
      fun i => if Nat.leb (pow2 k') i
               then fwht k' f (i - pow2 k')%nat
                    - fwht k' (fun j => f (pow2 k' + j)%nat) (i - pow2 k')%nat
               else fwht k' f i + fwht k' (fun j => f (pow2 k' + j)%nat) i
  end.

(** Residue of an upper-half index: n ≤ i < 2n ⟹ i mod n = i − n. *)
Lemma mod_hi : forall n i, (0 < n)%nat -> (n <= i)%nat -> (i < 2 * n)%nat ->
  (i mod n = i - n)%nat.
Proof.
  intros n i Hn Hle Hlt.
  replace (i mod n)%nat with (((i - n) + 1 * n) mod n)%nat by (f_equal; lia).
  rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia.
Qed.

(** Correctness: the fast transform equals the matrix transform. *)
Theorem fwht_correct : forall k f i, (i < pow2 k)%nat ->
  fwht k f i == op_apply (had k) f (pow2 k) i.
Proof.
  induction k as [|k IH]; intros f i Hi.
  - cbn [fwht pow2] in *. assert (i = 0)%nat by lia. subst i.
    unfold op_apply. cbn [q_sum had]. ring.
  - assert (Hn := pow2_pos k).
    assert (Hsplit : (pow2 (S k) = pow2 k + pow2 k)%nat) by (cbn [pow2]; lia).
    assert (Hi2 : (i < 2 * pow2 k)%nat) by (cbn [pow2] in Hi; lia).
    cbn [fwht]. unfold op_apply. rewrite Hsplit. rewrite q_sum_split. cbn beta.
    destruct (Nat.leb (pow2 k) i) eqn:Ei.
    + (* upper half *)
      apply Nat.leb_le in Ei.
      assert (Him : (i - pow2 k < pow2 k)%nat) by lia.
      assert (Hmod : (i mod pow2 k = i - pow2 k)%nat) by (apply mod_hi; lia).
      rewrite (IH f (i - pow2 k)%nat Him).
      rewrite (IH (fun j => f (pow2 k + j)%nat) (i - pow2 k)%nat Him).
      unfold op_apply.
      assert (Hs1 : q_sum (fun j => had (S k) i j * f j) (pow2 k)
                    == q_sum (fun j => had k (i - pow2 k)%nat j * f j) (pow2 k)).
      { apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_lo k i j Hj), Hmod. reflexivity. }
      assert (Hs2 : q_sum (fun j => had (S k) i (pow2 k + j)%nat * f (pow2 k + j)%nat) (pow2 k)
                    == q_sum (fun j => (- (1)) * (had k (i - pow2 k)%nat j * f (pow2 k + j)%nat))
                             (pow2 k)).
      { apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_hi k i j Hj).
        assert (Eleb : Nat.leb (pow2 k) i = true) by (apply Nat.leb_le; exact Ei).
        rewrite Eleb, Hmod. ring. }
      rewrite Hs1, Hs2.
      rewrite (q_sum_scale (- (1)) (fun j => had k (i - pow2 k)%nat j * f (pow2 k + j)%nat)
                           (pow2 k)).
      ring.
    + (* lower half *)
      apply Nat.leb_gt in Ei.
      assert (Hmod : (i mod pow2 k = i)%nat) by (apply Nat.mod_small; exact Ei).
      rewrite (IH f i Ei).
      rewrite (IH (fun j => f (pow2 k + j)%nat) i Ei).
      unfold op_apply.
      assert (Hs1 : q_sum (fun j => had (S k) i j * f j) (pow2 k)
                    == q_sum (fun j => had k i j * f j) (pow2 k)).
      { apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_lo k i j Hj), Hmod. reflexivity. }
      assert (Hs2 : q_sum (fun j => had (S k) i (pow2 k + j)%nat * f (pow2 k + j)%nat) (pow2 k)
                    == q_sum (fun j => had k i j * f (pow2 k + j)%nat) (pow2 k)).
      { apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_hi k i j Hj).
        assert (Eleb : Nat.leb (pow2 k) i = false) by (apply Nat.leb_gt; exact Ei).
        rewrite Eleb, Hmod. cbv iota. ring. }
      rewrite Hs1, Hs2. ring.
Qed.

Print Assumptions fwht_correct.
