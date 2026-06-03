(** * WalshOrthogonality.v — the GENERAL n-qubit Walsh orthogonality: HₙᵀHₙ = 2ⁿ·I
      for EVERY n.  Completes WalshHadamardN.v (concrete n ≤ 3) into a theorem.

    Elements: the ±1 rational entries of the 2ⁿ×2ⁿ Hadamard (from WalshHadamardN)
    Roles:    the computational and Walsh bases as ORTHOGONAL contexts — at EVERY n
    Rules:    the character-sum recurrence — splitting the 2ⁿ⁺¹ column sum into its
              even/odd halves gives idot(S n, i, k) = (2 if the low bits agree, else
              0)·idot(n, ⌊i/2⌋, ⌊k/2⌋); the off-diagonal vanishes by cancellation

    The single-qubit Walsh layer (③) and the n-qubit file showed the entries are ±1,
    every row has squared norm 2ⁿ (idot_diag, general), and the rows are orthogonal —
    but only VERIFIED for n ≤ 3.  Here the off-diagonal orthogonality is PROVED for
    EVERY n: idot n i k = 0 whenever i ≠ k.  Together with the general diagonal this is
    HₙᵀHₙ = 2ⁿ·I for all n — so the Element / constructive side of the finitization
    boundary doesn't merely sample as scaling, it IS proven to scale.

    The mechanism is the character sum.  Splitting Σ_{j<2ⁿ⁺¹} into even/odd j pairs the
    columns; each pair contributes (1 + s_i·s_k) where s = ±1 is the low-bit sign, which
    is 2 when the low bits agree and 0 when they differ.  Off the diagonal either the
    low bits differ (factor 0) or they agree but the upper halves differ (induction) —
    either way the sum cancels to 0.  Pure cancellation, 0 axioms.

    ============ E/R/R разбор ============
      Rules (L5): rsum_split (чётно/нечётное расщепление) ⟹ idot_rec (рекуррентность
                  половинного деления + сокращение пар); зануление вне диагонали.
      Roles (L4): вычислительный/Уолш-базисы ОРТОГОНАЛЬНЫ на КАЖДОМ n.
      Elements  : ±1-входы; диагональ 2ⁿ (L1+P4).
    ДИАГНОСТИКА (P4): Element/конструктивный костяк ДОКАЗАННО масштабируется (HₙᵀHₙ=2ⁿI
    для любого n), а не выборочно проверен; зануление = сокращение пар, конструктивно.

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia Lqa.
From ToS Require Import stdlib.WalshHadamardN.
Open Scope Z_scope.

(* ===================================================================== *)
(*  nat bit helpers                                                       *)
(* ===================================================================== *)

Lemma odd_double : forall j, Nat.odd (2 * j) = false.
Proof. intro j. rewrite Nat.odd_mul. reflexivity. Qed.

Lemma odd_double_succ : forall j, Nat.odd (S (2 * j)) = true.
Proof. intro j. rewrite Nat.odd_succ, Nat.even_mul. reflexivity. Qed.

Lemma div2_SS : forall n, Nat.div2 (S (S n)) = S (Nat.div2 n).
Proof. reflexivity. Qed.

Lemma div2_double : forall j, Nat.div2 (2 * j) = j.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - replace (2 * S j)%nat with (S (S (2 * j))) by lia.
    rewrite div2_SS, IH. reflexivity.
Qed.

Lemma div2_double_succ : forall j, Nat.div2 (S (2 * j)) = j.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - replace (S (2 * S j))%nat with (S (S (S (2 * j)))) by lia.
    rewrite div2_SS, IH. reflexivity.
Qed.

(** Bit decomposition: i = k iff low bits agree and the halves agree. *)
Lemma bit_decomp : forall i k : nat,
  i = k <-> (Nat.odd i = Nat.odd k /\ Nat.div2 i = Nat.div2 k).
Proof.
  intros i k. split.
  - intro H; subst; split; reflexivity.
  - intros [Ho Hd].
    rewrite (Nat.div2_odd i), (Nat.div2_odd k), Hd, Ho. reflexivity.
Qed.

(* ===================================================================== *)
(*  A general range sum and its even/odd split                           *)
(* ===================================================================== *)

Fixpoint rsum (g : nat -> Z) (c : nat) : Z :=
  match c with O => 0 | S c' => g c' + rsum g c' end.

Lemma rsum_ext : forall (g h : nat -> Z) c,
  (forall j, g j = h j) -> rsum g c = rsum h c.
Proof.
  intros g h c H. induction c as [|c IH]; simpl; [reflexivity | rewrite H, IH; reflexivity].
Qed.

Lemma rsum_const_mul : forall (a : Z) (g : nat -> Z) c,
  rsum (fun j => a * g j) c = a * rsum g c.
Proof.
  intros a g c. induction c as [|c IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma rsum_split : forall (g : nat -> Z) (c : nat),
  rsum g (2 * c)%nat = rsum (fun j => g (2 * j)%nat + g (S (2 * j)%nat)) c.
Proof.
  intros g. induction c as [|c IH].
  - reflexivity.
  - replace (2 * S c)%nat with (S (S (2 * c)))%nat by lia.
    cbn [rsum]. rewrite IH. ring.
Qed.

(* ===================================================================== *)
(*  idot as a range sum, and its halving recurrence                      *)
(* ===================================================================== *)

Lemma idot_eq : forall n i k,
  idot n i k = rsum (fun j => wval n i j * wval n k j) (Nat.pow 2 n).
Proof.
  intros n i k. unfold idot.
  generalize (Nat.pow 2 n) as c. intro c.
  induction c as [|c IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** One paired column contributes the low-bit factor times the halved product. *)
Lemma pair_term : forall n i k j,
  wval (S n) i (2 * j)%nat * wval (S n) k (2 * j)%nat
  + wval (S n) i (S (2 * j)%nat) * wval (S n) k (S (2 * j)%nat)
  = (if Bool.eqb (Nat.odd i) (Nat.odd k) then 2 else 0)
    * (wval n (Nat.div2 i) j * wval n (Nat.div2 k) j).
Proof.
  intros n i k j. cbn [wval].
  rewrite odd_double, odd_double_succ, div2_double, div2_double_succ.
  destruct (Nat.odd i), (Nat.odd k); cbn [andb Bool.eqb]; ring.
Qed.

Lemma idot_rec : forall n i k,
  idot (S n) i k
  = (if Bool.eqb (Nat.odd i) (Nat.odd k) then 2 else 0) * idot n (Nat.div2 i) (Nat.div2 k).
Proof.
  intros n i k.
  rewrite (idot_eq (S n) i k).
  replace (Nat.pow 2 (S n)) with (2 * Nat.pow 2 n)%nat by (cbn [Nat.pow]; lia).
  rewrite rsum_split.
  rewrite (rsum_ext _
    (fun j => (if Bool.eqb (Nat.odd i) (Nat.odd k) then 2 else 0)
              * (wval n (Nat.div2 i) j * wval n (Nat.div2 k) j))
    (Nat.pow 2 n) (fun j => pair_term n i k j)).
  rewrite rsum_const_mul.
  rewrite <- (idot_eq n (Nat.div2 i) (Nat.div2 k)).
  reflexivity.
Qed.

(* ===================================================================== *)
(*  ★ THE GENERAL ORTHOGONALITY:  HₙᵀHₙ = 2ⁿ·I  for every n              *)
(* ===================================================================== *)

Theorem walsh_orthogonality : forall n i k,
  (i < Nat.pow 2 n)%nat -> (k < Nat.pow 2 n)%nat ->
  idot n i k = if Nat.eqb i k then Z.of_nat (Nat.pow 2 n) else 0.
Proof.
  induction n as [|n IH]; intros i k Hi Hk.
  - (* n = 0: i = k = 0 *)
    cbn [Nat.pow] in *.
    assert (i = 0)%nat by lia. assert (k = 0)%nat by lia. subst.
    reflexivity.
  - rewrite idot_rec.
    assert (Hi2 : (Nat.div2 i < Nat.pow 2 n)%nat).
    { rewrite Nat.div2_div. cbn [Nat.pow] in Hi. apply Nat.Div0.div_lt_upper_bound. lia. }
    assert (Hk2 : (Nat.div2 k < Nat.pow 2 n)%nat).
    { rewrite Nat.div2_div. cbn [Nat.pow] in Hk. apply Nat.Div0.div_lt_upper_bound. lia. }
    rewrite (IH (Nat.div2 i) (Nat.div2 k) Hi2 Hk2).
    (* case on whether i = k via low bits and halves *)
    destruct (Bool.eqb (Nat.odd i) (Nat.odd k)) eqn:Eo;
    destruct (Nat.eqb (Nat.div2 i) (Nat.div2 k)) eqn:Ed.
    + (* low bits agree, halves agree ⟹ i = k *)
      apply Bool.eqb_prop in Eo. apply Nat.eqb_eq in Ed.
      assert (i = k) by (apply bit_decomp; split; assumption).
      subst. rewrite Nat.eqb_refl. cbn [Nat.pow]. lia.
    + (* halves differ ⟹ i ≠ k *)
      apply Nat.eqb_neq in Ed.
      assert (i <> k) by (intro Hc; apply Ed; subst; reflexivity).
      apply Nat.eqb_neq in H. rewrite H. ring.
    + (* low bits differ ⟹ i ≠ k; factor is 0 *)
      apply Bool.eqb_false_iff in Eo.
      assert (i <> k) by (intro Hc; apply Eo; subst; reflexivity).
      apply Nat.eqb_neq in H. rewrite H. ring.
    + apply Bool.eqb_false_iff in Eo.
      assert (i <> k) by (intro Hc; apply Eo; subst; reflexivity).
      apply Nat.eqb_neq in H. rewrite H. ring.
Qed.

(** Restated: off the diagonal the inner product vanishes (for every n). *)
Corollary walsh_off_diagonal : forall n i k,
  (i < Nat.pow 2 n)%nat -> (k < Nat.pow 2 n)%nat -> i <> k ->
  idot n i k = 0.
Proof.
  intros n i k Hi Hk Hne. rewrite (walsh_orthogonality n i k Hi Hk).
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.
