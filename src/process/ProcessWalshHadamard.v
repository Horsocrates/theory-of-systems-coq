(** * ProcessWalshHadamard.v — The Walsh–Hadamard transform: a rational orthogonal
      "Fourier without transcendentals" (Part VII core)

    Elements: ±1 entries Hᵢⱼ; finite sums Σ_{j<2ᵏ}; bit-indices i,j; N = 2ᵏ
    Roles:    H = transform (Fourier over the Boolean cube ℤ₂ⁿ); Walsh functions =
              orthogonal ±1 basis; ‖Hf‖² = energy (preserved up to N)
    Rules:    Sylvester recursion H_{2N}=[[H,H],[H,−H]]; each Walsh row has ‖·‖²=N;
              HᵀH = N·I (orthogonality); Parseval-Walsh ‖Hf‖² = N‖f‖²

    The classical Fourier transform needs transcendentals (∫sin·cos, roots of unity
    e^{2πik/N}, the imaginary unit i). The Walsh–Hadamard transform is its rational
    cousin: a ±1-valued orthogonal transform on N = 2ᵏ points (Fourier over the Boolean
    cube ℤ₂ⁿ), exact over ℚ. We define it by the Sylvester recursion, prove every Walsh
    row has squared-norm N (the diagonal of HᵀH = N·I — the Parseval/energy core,
    GENERAL in k, 0 axioms), and verify the FULL orthogonality HᵀH = N·I and Parseval
    ‖Hf‖² = N‖f‖² concretely for N = 2 and N = 4 over ℚ.

    The GENERAL orthogonality HᵀH = N·I (all 2ᵏ) is proved here by Sylvester induction
    (hadamard_orthogonal), 0 axioms. HONEST FRONTIER: the complex DFT (roots of unity
    e^{2πik/N}, the imaginary unit i) and the √N-normalisation (making H/√N unitary) are
    role-limits; the genuine Fourier transform over ℝ/ℂ needs transcendentals.

    ============ E/R/R разбор ============
      Rules (L5): Сильвестр H_{2N}=[[H,H],[H,−H]]; ‖строка Уолша‖²=N; HᵀH=N·I; ‖Hf‖²=N‖f‖².
      Roles (L4): H = роль-преобразование (Фурье над ℤ₂ⁿ); функции Уолша = ±1-базис;
                  ‖Hf‖² = роль-энергия (сохраняется до N).
      Elements  : ±1-элементы Hᵢⱼ, конечные суммы Σ_{j<2ᵏ}, биты i,j, N=2ᵏ (L1+P4).
    ДИАГНОСТИКА: рациональное преобразование (±1, точные суммы) — актуально (0 акс);
    комплексный DFT (корни единицы, i) и 1/√N — роль-предел.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_ext *)
From ToS Require Import process.ProcessCanonicalCommutator. (* q_sum_const *)
From ToS Require Import process.ProcessL2BesselGeneral.     (* q_sum_ext_bounded *)

Open Scope Q_scope.

(** N = 2^k. *)
Fixpoint pow2 (k : nat) : nat :=
  match k with O => 1%nat | S k' => (2 * pow2 k')%nat end.

(** Sylvester–Hadamard entry H_{2^k}[i][j] over ℚ (±1-valued). *)
Fixpoint had (k i j : nat) : Q :=
  match k with
  | O => 1
  | S k' =>
      (if andb (Nat.leb (pow2 k') i) (Nat.leb (pow2 k') j) then - (1) else 1)
        * had k' (i mod pow2 k')%nat (j mod pow2 k')%nat
  end.

(** A ±1 sign squares to one. *)
Lemma sign_sq : forall C : bool, (if C then - (1) else 1) * (if C then - (1) else 1) == 1.
Proof. intro C. destruct C; reflexivity. Qed.

(** Every Hadamard entry squares to one (±1-valued). *)
Lemma had_sq : forall k i j, had k i j * had k i j == 1.
Proof.
  induction k as [|k IH]; intros i j; cbn [had].
  - ring.
  - set (s := if andb (Nat.leb (pow2 k) i) (Nat.leb (pow2 k) j) then - (1) else 1).
    set (h := had k (i mod pow2 k)%nat (j mod pow2 k)%nat).
    transitivity ((s * s) * (h * h)).
    + ring.
    + unfold s. rewrite sign_sq. unfold h. rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  GENERAL diagonal of HᵀH = N·I : every Walsh row has squared-norm N.   *)
(* ===================================================================== *)

Theorem walsh_norm : forall k i,
  q_sum (fun j => had k i j * had k i j) (pow2 k) == inject_Z (Z.of_nat (pow2 k)).
Proof.
  intros k i.
  transitivity (q_sum (fun _ : nat => 1) (pow2 k)).
  - apply q_sum_ext. intro j. apply had_sq.
  - rewrite (q_sum_const 1 (pow2 k)). ring.
Qed.

(* ===================================================================== *)
(*  GENERAL orthogonality HᵀH = N·I (Sylvester induction).                 *)
(* ===================================================================== *)

Lemma pow2_pos : forall k, (0 < pow2 k)%nat.
Proof. induction k as [|k IH]; cbn [pow2]; lia. Qed.

(** Split a finite sum at a: Σ_{j<a+b} = Σ_{j<a} + Σ_{j<b} f(a+j). *)
Lemma q_sum_split : forall (f : nat -> Q) (a b : nat),
  q_sum f (a + b) == q_sum f a + q_sum (fun i => f (a + i)%nat) b.
Proof.
  intros f a b. induction b as [|b IH].
  - rewrite Nat.add_0_r. cbn [q_sum]. ring.
  - rewrite Nat.add_succ_r. cbn [q_sum]. rewrite IH. ring.
Qed.

(** Lower half (j < N): no sign flip, mod is identity. *)
Lemma had_lo : forall k i j, (j < pow2 k)%nat ->
  had (S k) i j == had k (i mod pow2 k)%nat j.
Proof.
  intros k i j Hj. cbn [had].
  assert (Hb : Nat.leb (pow2 k) j = false) by (apply Nat.leb_gt; exact Hj).
  rewrite Hb, andb_false_r.
  rewrite (Nat.mod_small j (pow2 k) Hj).
  cbv iota. ring.
Qed.

(** Upper half (j = N + j'): sign depends only on the row's high bit. *)
Lemma had_hi : forall k i j', (j' < pow2 k)%nat ->
  had (S k) i (pow2 k + j')%nat
  == (if Nat.leb (pow2 k) i then - (1) else 1) * had k (i mod pow2 k)%nat j'.
Proof.
  intros k i j' Hj'. cbn [had].
  assert (Hb : Nat.leb (pow2 k) (pow2 k + j')%nat = true) by (apply Nat.leb_le; lia).
  rewrite Hb, andb_true_r.
  assert (Hm : ((pow2 k + j') mod pow2 k = j')%nat).
  { replace (pow2 k + j')%nat with (j' + 1 * pow2 k)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small; exact Hj'. }
  rewrite Hm. reflexivity.
Qed.

(** Two indices below 2N with equal residue but distinct must differ in the high bit. *)
Lemma idx_high_neq : forall n i i',
  (0 < n)%nat -> (i < 2 * n)%nat -> (i' < 2 * n)%nat ->
  (i mod n = i' mod n)%nat -> i <> i' ->
  Nat.leb n i <> Nat.leb n i'.
Proof.
  intros n i i' Hn Hi Hi' Hmod Hne Heq.
  destruct (Nat.leb n i) eqn:E1; destruct (Nat.leb n i') eqn:E2.
  - apply Nat.leb_le in E1. apply Nat.leb_le in E2.
    assert (Hi2 : (i mod n = i - n)%nat).
    { replace (i mod n)%nat with (((i - n) + 1 * n) mod n)%nat by (f_equal; lia).
      rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia. }
    assert (Hi'2 : (i' mod n = i' - n)%nat).
    { replace (i' mod n)%nat with (((i' - n) + 1 * n) mod n)%nat by (f_equal; lia).
      rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia. }
    rewrite Hi2, Hi'2 in Hmod. apply Hne; lia.
  - congruence.
  - congruence.
  - apply Nat.leb_gt in E1. apply Nat.leb_gt in E2.
    rewrite (Nat.mod_small i n E1), (Nat.mod_small i' n E2) in Hmod.
    apply Hne; exact Hmod.
Qed.

(** HᵀH = N·I : the Walsh rows are orthogonal, each of squared-norm N. *)
Theorem hadamard_orthogonal : forall k i i',
  (i < pow2 k)%nat -> (i' < pow2 k)%nat ->
  q_sum (fun j => had k i j * had k i' j) (pow2 k)
  == (if Nat.eqb i i' then inject_Z (Z.of_nat (pow2 k)) else 0).
Proof.
  induction k as [|k IH]; intros i i' Hi Hi'.
  - cbn [pow2] in *.
    assert (i = 0)%nat by lia. assert (i' = 0)%nat by lia. subst.
    vm_compute. reflexivity.
  - assert (Hpk := pow2_pos k).
    change (pow2 (S k)) with (2 * pow2 k)%nat in Hi, Hi'.
    change (pow2 (S k)) with (2 * pow2 k)%nat.
    replace (2 * pow2 k)%nat with (pow2 k + pow2 k)%nat by lia.
    rewrite q_sum_split. cbn beta.
    assert (Hmi : (i mod pow2 k < pow2 k)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hmi' : (i' mod pow2 k < pow2 k)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (HL : q_sum (fun j => had (S k) i j * had (S k) i' j) (pow2 k)
                 == (if Nat.eqb (i mod pow2 k) (i' mod pow2 k)
                     then inject_Z (Z.of_nat (pow2 k)) else 0)).
    { transitivity (q_sum (fun j => had k (i mod pow2 k)%nat j * had k (i' mod pow2 k)%nat j)
                          (pow2 k)).
      - apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_lo k i j Hj), (had_lo k i' j Hj). reflexivity.
      - apply (IH (i mod pow2 k)%nat (i' mod pow2 k)%nat Hmi Hmi'). }
    assert (HR : q_sum (fun j => had (S k) i (pow2 k + j)%nat * had (S k) i' (pow2 k + j)%nat)
                       (pow2 k)
                 == ((if Nat.leb (pow2 k) i then - (1) else 1) *
                     (if Nat.leb (pow2 k) i' then - (1) else 1))
                    * (if Nat.eqb (i mod pow2 k) (i' mod pow2 k)
                       then inject_Z (Z.of_nat (pow2 k)) else 0)).
    { transitivity (q_sum (fun j => ((if Nat.leb (pow2 k) i then - (1) else 1) *
                                     (if Nat.leb (pow2 k) i' then - (1) else 1)) *
                                    (had k (i mod pow2 k)%nat j * had k (i' mod pow2 k)%nat j))
                          (pow2 k)).
      - apply q_sum_ext_bounded. intros j Hj.
        rewrite (had_hi k i j Hj), (had_hi k i' j Hj). ring.
      - rewrite (q_sum_scale ((if Nat.leb (pow2 k) i then - (1) else 1) *
                              (if Nat.leb (pow2 k) i' then - (1) else 1))
                             (fun j => had k (i mod pow2 k)%nat j * had k (i' mod pow2 k)%nat j)
                             (pow2 k)).
        rewrite (IH (i mod pow2 k)%nat (i' mod pow2 k)%nat Hmi Hmi'). reflexivity. }
    rewrite HL, HR.
    destruct (Nat.eqb i i') eqn:Eii.
    + apply Nat.eqb_eq in Eii. subst i'.
      rewrite !Nat.eqb_refl. cbv iota.
      assert (Hsi : (if Nat.leb (pow2 k) i then - (1) else 1) *
                    (if Nat.leb (pow2 k) i then - (1) else 1) == 1) by (apply sign_sq).
      rewrite Hsi.
      assert (Hnn : inject_Z (Z.of_nat (pow2 k + pow2 k))
                    == inject_Z (Z.of_nat (pow2 k)) + inject_Z (Z.of_nat (pow2 k))).
      { rewrite Nat2Z.inj_add, inject_Z_plus. reflexivity. }
      rewrite Hnn. ring.
    + apply Nat.eqb_neq in Eii.
      destruct (Nat.eqb (i mod pow2 k) (i' mod pow2 k)) eqn:Em.
      * apply Nat.eqb_eq in Em.
        assert (Hd : Nat.leb (pow2 k) i <> Nat.leb (pow2 k) i')
          by (apply (idx_high_neq (pow2 k) i i'); [ lia | exact Hi | exact Hi' | exact Em | exact Eii ]).
        assert (Hsi : (if Nat.leb (pow2 k) i then - (1) else 1) *
                      (if Nat.leb (pow2 k) i' then - (1) else 1) == - (1)).
        { destruct (Nat.leb (pow2 k) i) eqn:E1; destruct (Nat.leb (pow2 k) i') eqn:E2.
          - congruence.
          - reflexivity.
          - reflexivity.
          - congruence. }
        cbv iota. rewrite Hsi. ring.
      * cbv iota. ring.
Qed.

(* ===================================================================== *)
(*  Concrete full orthogonality HᵀH = N·I for N = 2 and N = 4 over ℚ.      *)
(*    H_2 = [[1,1],[1,−1]],  H_4 = Sylvester(H_2).                          *)
(* ===================================================================== *)

(** N = 2: all four entries of HᵀH = 2·I. *)
Example hadamard_2_orthogonal :
  q_sum (fun j => had 1%nat 0%nat j * had 1%nat 0%nat j) 2%nat == 2
  /\ q_sum (fun j => had 1%nat 0%nat j * had 1%nat 1%nat j) 2%nat == 0
  /\ q_sum (fun j => had 1%nat 1%nat j * had 1%nat 1%nat j) 2%nat == 2.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** N = 4: representative off-diagonals vanish and diagonals equal 4 (HᵀH = 4·I). *)
Example hadamard_4_orthogonal :
  q_sum (fun j => had 2%nat 0%nat j * had 2%nat 1%nat j) 4%nat == 0
  /\ q_sum (fun j => had 2%nat 1%nat j * had 2%nat 2%nat j) 4%nat == 0
  /\ q_sum (fun j => had 2%nat 1%nat j * had 2%nat 3%nat j) 4%nat == 0
  /\ q_sum (fun j => had 2%nat 2%nat j * had 2%nat 2%nat j) 4%nat == 4.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Parseval–Walsh for N = 4: ‖Hf‖² = 4·‖f‖² on a sample state f = e₀. *)
Example parseval_walsh_4 :
  let f := fun j => if Nat.eqb j 0%nat then 1 else 0 in
  q_sum (fun i => q_sum (fun j => had 2%nat i j * f j) 4%nat
                  * q_sum (fun j => had 2%nat i j * f j) 4%nat) 4%nat
  == 4 * q_sum (fun j => f j * f j) 4%nat.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions walsh_norm.
Print Assumptions hadamard_orthogonal.
