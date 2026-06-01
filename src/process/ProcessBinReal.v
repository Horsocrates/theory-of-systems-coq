(** * ProcessBinReal.v — Bridge: Cantor 2^N  ->  Cauchy [0,1]  (F-19, core)

    ============ E/R/R разбор моста двух моделей континуума ============
    Две МОДЕЛИ: Кантор 2^N (BinProcess := nat->bool; дихотомия КБ, гл. 4.5) и
    Коши-[0,1] (RealProcess := nat->Q; гл. 4.2–4.4). Мост bin_to_real переводит
    представителя ОДНОЙ модели в представителя ДРУГОЙ.

      Rules (L5): правило двоичного разложения (n-я усечёнка = сумма bit/2^(k+1));
                  process_equiv — когда два процесса именуют ОДНУ точку.
      Roles (L4): «точка континуума» — обе модели её именуют; «представитель».
      Elements  : бинарные процессы и Коши-процессы — НОСИТЕЛИ (в разных моделях);
                  рациональные усечёнки (L1+P4).

    ГЛАВНАЯ ТОНКОСТЬ (диагностика): bin_to_real НЕ инъективна (двоичная
    неоднозначность 0,0111…=0,1000…): РАЗНЫЕ бинарные процессы именуют ОДНУ точку.
    Это тема F-10 (точка=класс): мост согласует модели на уровне ТОЧЕК
    (process_equiv), не представителей. «2^N ≅ [0,1] как объекты» ложно; честно —
    СЮРЪЕКЦИЯ С ОТОЖДЕСТВЛЕНИЕМ на точках. Свидетель: 0,111…(2) = 1
    (bin_ones_equiv_one) — двоичный аналог F-11 (0,999…=1), тем же приёмом.

    ЧЕСТНАЯ ГРАНИЦА (вне ядра): полная неинъективность парой (1000…~0111… в ½) и
    ПЕРЕНОС дихотомии Кантора–Бендиксона на Коши-процессы — отмечены как открытые
    расширения, не доказаны здесь.

    NB: общий is_Cauchy моста использует monotone_bounded_Cauchy (=> classic/L3),
    что согласовано с гл. 4.5 (модель 2^N уже на L3+L4). Свидетель 0,111…=1 —
    axiom-free.

    STATUS: 15 Qed, 0 Admitted; общий is_Cauchy на classic (L3), остальное 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import ProcessTypes.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Powers of two as a rational                                          *)
(* ===================================================================== *)

Fixpoint pow2 (n : nat) : positive :=
  match n with O => 1%positive | S k => (2 * pow2 k)%positive end.

Definition two_pow (n : nat) : Q := inject_Z (Z.pos (pow2 n)).

Lemma two_pow_pos : forall n, 0 < two_pow n.
Proof.
  intros n. unfold two_pow. change 0 with (inject_Z 0).
  rewrite <- Zlt_Qlt. lia.
Qed.

Lemma two_pow_succ : forall k, two_pow (S k) == 2 * two_pow k.
Proof.
  intros k. unfold two_pow.
  change (pow2 (S k)) with (2 * pow2 k)%positive.
  rewrite Pos2Z.inj_mul, inject_Z_mult. reflexivity.
Qed.

Lemma pow2_ge : forall n, (Z.of_nat (S n) <= Z.pos (pow2 n))%Z.
Proof.
  induction n as [|k IH].
  - simpl. lia.
  - change (pow2 (S k)) with (2 * pow2 k)%positive.
    rewrite Pos2Z.inj_mul. lia.
Qed.

Lemma two_pow_half : forall k, 1 / two_pow k - 1 / two_pow (S k) == 1 / two_pow (S k).
Proof.
  intros k. pose proof (two_pow_pos k) as Hp.
  assert (Ht : ~ (two_pow k == 0)) by lra.
  rewrite two_pow_succ. field. exact Ht.
Qed.

(* ===================================================================== *)
(*  The bridge: a binary process -> its partial sums (a Cauchy real)      *)
(* ===================================================================== *)

Definition bit_val (b : bool) : Q := if b then 1 else 0.

Fixpoint bin_partial (b : BinProcess) (n : nat) : Q :=
  match n with
  | O => 0
  | S k => bin_partial b k + bit_val (b k) / two_pow (S k)
  end.

Definition bin_to_real (b : BinProcess) : RealProcess := bin_partial b.

Definition all_ones : BinProcess := fun _ => true.

(* ===================================================================== *)
(*  Closed form for all-ones, and the geometric upper bound               *)
(* ===================================================================== *)

Lemma bin_partial_ones_closed : forall n,
  bin_partial all_ones n == 1 - 1 / two_pow n.
Proof.
  induction n as [|k IH].
  - vm_compute. reflexivity.
  - change (bin_partial all_ones (S k))
      with (bin_partial all_ones k + bit_val (all_ones k) / two_pow (S k)).
    assert (Hone : bit_val (all_ones k) = 1) by reflexivity.
    rewrite Hone, IH.
    pose proof (two_pow_half k) as Hh. lra.
Qed.

Lemma bit_val_le_1 : forall b, bit_val b <= 1.
Proof. intros b. unfold bit_val. destruct b; lra. Qed.

Lemma bit_val_nonneg : forall b, 0 <= bit_val b.
Proof. intros b. unfold bit_val. destruct b; lra. Qed.

Lemma term_nonneg : forall b k, 0 <= bit_val (b k) / two_pow (S k).
Proof.
  intros b k. unfold Qdiv. apply Qmult_le_0_compat.
  - apply bit_val_nonneg.
  - apply Qlt_le_weak, Qinv_lt_0_compat, two_pow_pos.
Qed.

Lemma bin_partial_le_ones : forall b n, bin_partial b n <= bin_partial all_ones n.
Proof.
  intros b. induction n as [|k IH].
  - simpl. lra.
  - change (bin_partial b (S k))
      with (bin_partial b k + bit_val (b k) / two_pow (S k)).
    change (bin_partial all_ones (S k))
      with (bin_partial all_ones k + bit_val (all_ones k) / two_pow (S k)).
    assert (Hone : bit_val (all_ones k) = 1) by reflexivity.
    rewrite Hone.
    assert (Hterm : bit_val (b k) / two_pow (S k) <= 1 / two_pow (S k)).
    { unfold Qdiv. apply Qmult_le_compat_r.
      - apply bit_val_le_1.
      - apply Qlt_le_weak, Qinv_lt_0_compat, two_pow_pos. }
    lra.
Qed.

Lemma bin_nonneg : forall b n, 0 <= bin_partial b n.
Proof.
  intros b. induction n as [|k IH].
  - simpl. lra.
  - simpl bin_partial. pose proof (term_nonneg b k). lra.
Qed.

Lemma bin_le_1 : forall b n, bin_partial b n <= 1.
Proof.
  intros b n.
  pose proof (bin_partial_le_ones b n) as H1.
  pose proof (bin_partial_ones_closed n) as H2.
  pose proof (two_pow_pos n) as Hp.
  assert (Hinv : 0 < 1 / two_pow n).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat, two_pow_pos. }
  lra.
Qed.

(* ===================================================================== *)
(*  The bridge is well-defined: a binary process gives a Cauchy real      *)
(*  in [0,1].                                                             *)
(* ===================================================================== *)

Lemma bin_monotone : forall b, monotone_increasing (bin_to_real b).
Proof.
  intros b n. unfold bin_to_real. simpl bin_partial.
  pose proof (term_nonneg b n). lra.
Qed.

Theorem bin_to_real_in_interval : forall b, in_interval 0 1 (bin_to_real b).
Proof.
  intros b n. split.
  - apply bin_nonneg.
  - apply bin_le_1.
Qed.

Theorem bin_to_real_is_Cauchy : forall b, is_Cauchy (bin_to_real b).
Proof.
  intros b. apply (monotone_bounded_Cauchy (bin_to_real b) 1).
  - apply bin_monotone.
  - intros n. apply bin_le_1.
Qed.

(* ===================================================================== *)
(*  Point-identification witness: 0,111...(2) = 1  (binary analogue of    *)
(*  0,999...=1, F-11). Different representatives, SAME point.             *)
(* ===================================================================== *)

Theorem bin_ones_equiv_one : bin_to_real all_ones ~~ const_process 1.
Proof.
  intros eps Heps.
  destruct (q_archimedean 1 eps Heps) as [K HK].
  exists K. intros n Hn.
  assert (Hclosed : bin_to_real all_ones n == 1 - 1 / two_pow n)
    by (unfold bin_to_real; apply bin_partial_ones_closed).
  assert (Hpos : 0 < 1 / two_pow n).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat, two_pow_pos. }
  assert (Eabs : Qabs (bin_to_real all_ones n - const_process 1 n) == 1 / two_pow n).
  { assert (E1 : bin_to_real all_ones n - const_process 1 n == - (1 / two_pow n)).
    { rewrite Hclosed. unfold const_process. set (x := 1 / two_pow n). ring. }
    rewrite (Qabs_wd _ _ E1). rewrite Qabs_opp. apply Qabs_pos, Qlt_le_weak, Hpos. }
  rewrite Eabs.
  apply Qlt_shift_div_r.
  - apply two_pow_pos.
  - assert (Hmono : inject_Z (Z.of_nat K) <= two_pow n).
    { unfold two_pow. rewrite <- Zle_Qle.
      pose proof (pow2_ge n) as G.
      assert (Z.of_nat K <= Z.of_nat (S n))%Z by lia. lia. }
    assert (Hle : inject_Z (Z.of_nat K) * eps <= two_pow n * eps).
    { apply Qmult_le_compat_r. exact Hmono. apply Qlt_le_weak, Heps. }
    rewrite (Qmult_comm eps (two_pow n)).
    apply Qlt_le_trans with (inject_Z (Z.of_nat K) * eps); [ exact HK | exact Hle ].
Qed.

Print Assumptions bin_ones_equiv_one.
Print Assumptions bin_to_real_in_interval.
Print Assumptions bin_to_real_is_Cauchy.   (* expected: classic (L3), via monotone_bounded_Cauchy *)
