(** * Sqrt2Approx.v — rational approximations of √2 via the Pell recurrence, as a PROCESS.  The Pell
       sequence pₖ₊₁=pₖ+2qₖ, qₖ₊₁=pₖ+qₖ gives |pₖ²−2qₖ²|=1 (one ring invariant), so xₖ=pₖ/qₖ satisfies
       EXACTLY |xₖ²−2|=1/qₖ² with qₖ→∞ — rationals arbitrarily close to √2, never equal (P4: √2 is the
       non-terminating PROCESS, each xₖ an Element).  Reusable brick for F-20 (ℚ non-compactness) and
       F-21 (Cantor–Heine failure over ℚ).

    Key output: `sqrt2_uncovered N` — a rational x ∈ [1,2] with |x²−2| ≤ 1/(k+1) for every k ≤ N.

    ============ E/R/R разбор ============
      Elements : пары Пелля (pₖ,qₖ:ℤ); приближение xₖ=pₖ/qₖ∈ℚ — каждое актуально (P4).
      Roles    : √2 = role-limit (незавершённый процесс); xₖ = роль-приближение, |xₖ²−2|=1/qₖ² назначается правилом.
      Rules    : рекуррентность Пелля + инвариант pₖ²−2qₖ²=±1 (один ring-шаг) ⟹ точная ошибка 1/qₖ², qₖ↑.
      ДИАГНОСТИКА (P4): xₖ Element-сторона (рациональны, |xₖ²−2|>0 всегда — √2∉ℚ); √2 само = role-limit. Уровень: `инструмент`.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia.

(* ===================================================================== *)
(*  Robust Z→Q bridges (proved by unfolding, no lemma-name dependence)     *)
(* ===================================================================== *)

Lemma injZ_lt : forall a b : Z, (a < b)%Z -> inject_Z a < inject_Z b.
Proof. intros a b H. unfold Qlt; simpl; lia. Qed.

Lemma injZ_le : forall a b : Z, (a <= b)%Z -> inject_Z a <= inject_Z b.
Proof. intros a b H. unfold Qle; simpl; lia. Qed.

Lemma injZ_pos : forall z : Z, (0 < z)%Z -> 0 < inject_Z z.
Proof. intros z H. unfold Qlt; simpl; lia. Qed.

Lemma injZ_neq0 : forall z : Z, (z <> 0)%Z -> ~ inject_Z z == 0.
Proof. intros z H Hc. unfold Qeq in Hc; simpl in Hc; lia. Qed.

Lemma injZ_sub : forall a b : Z, inject_Z (a - b) = inject_Z a - inject_Z b.
Proof.
  intros a b. unfold Qminus.
  replace (a - b)%Z with (a + (- b))%Z by ring.
  rewrite inject_Z_plus. f_equal.
Qed.

(** Reciprocal is antitone on the positives — robust manual proof. *)
Lemma Qinv_antitone : forall a b : Q, 0 < a -> a <= b -> / b <= / a.
Proof.
  intros a b Ha Hab. assert (Hb : 0 < b) by lra.
  assert (H0z : 0 < a * b) by (apply Qmult_lt_0_compat; assumption).
  rewrite <- (Qmult_le_l (/ b) (/ a) (a * b) H0z).
  setoid_replace (a * b * / b) with a by (field; lra).
  setoid_replace (a * b * / a) with b by (field; lra).
  exact Hab.
Qed.

(* ===================================================================== *)
(*  The Pell sequence (integer core)                                       *)
(* ===================================================================== *)

Fixpoint pell (k : nat) : Z * Z :=
  match k with
  | O => (1, 1)%Z
  | S j => let (p, q) := pell j in ((p + 2 * q)%Z, (p + q)%Z)
  end.
Definition pp (k : nat) : Z := fst (pell k).
Definition qq (k : nat) : Z := snd (pell k).

Lemma pell_S : forall k, pp (S k) = (pp k + 2 * qq k)%Z /\ qq (S k) = (pp k + qq k)%Z.
Proof. intro k. unfold pp, qq. simpl. destruct (pell k) as [p q]. simpl. split; reflexivity. Qed.

(** Positivity + range: 0 < q ≤ p ≤ 2q  (gives 1 ≤ p/q ≤ 2). *)
Lemma pell_inv : forall k, (0 < qq k)%Z /\ (qq k <= pp k)%Z /\ (pp k <= 2 * qq k)%Z.
Proof.
  induction k as [| k IH].
  - unfold pp, qq; simpl. lia.
  - destruct IH as [Hpos [Hle Hub]].
    destruct (pell_S k) as [Hp Hq]. rewrite Hp, Hq. lia.
Qed.

(** Growth: qₖ ≥ k+1. *)
Lemma qq_ge : forall k, (Z.of_nat (S k) <= qq k)%Z.
Proof.
  induction k as [| k IH].
  - unfold qq; simpl. lia.
  - destruct (pell_inv k) as [Hpos [Hle _]].
    destruct (pell_S k) as [_ Hq]. rewrite Hq.
    rewrite Nat2Z.inj_succ in *. lia.
Qed.

(** The Pell invariant: pₖ²−2qₖ² = ±1 (one ring step per induction). *)
Lemma pell_pm : forall k,
  (pp k * pp k - 2 * (qq k * qq k) = 1)%Z \/ (pp k * pp k - 2 * (qq k * qq k) = -1)%Z.
Proof.
  induction k as [| k IH].
  - unfold pp, qq; simpl. right. reflexivity.
  - destruct (pell_S k) as [Hp Hq]. rewrite Hp, Hq.
    destruct IH as [H | H].
    + right.
      replace ((pp k + 2 * qq k) * (pp k + 2 * qq k) - 2 * ((pp k + qq k) * (pp k + qq k)))%Z
        with (- (pp k * pp k - 2 * (qq k * qq k)))%Z by ring.
      rewrite H. reflexivity.
    + left.
      replace ((pp k + 2 * qq k) * (pp k + 2 * qq k) - 2 * ((pp k + qq k) * (pp k + qq k)))%Z
        with (- (pp k * pp k - 2 * (qq k * qq k)))%Z by ring.
      rewrite H. reflexivity.
Qed.

(* ===================================================================== *)
(*  The rational approximation xₖ = pₖ/qₖ                                  *)
(* ===================================================================== *)

Open Scope Q_scope.

Definition sx (k : nat) : Q := inject_Z (pp k) / inject_Z (qq k).

(** inject_Z respects the squared-deviation numerator. *)
Lemma sx_num_eq : forall N,
  inject_Z (pp N) * inject_Z (pp N) - 2 * (inject_Z (qq N) * inject_Z (qq N))
  == inject_Z (pp N * pp N - 2 * (qq N * qq N)).
Proof.
  intro N. rewrite injZ_sub.
  rewrite (inject_Z_mult (pp N) (pp N)).
  rewrite (inject_Z_mult 2 (qq N * qq N)).
  rewrite (inject_Z_mult (qq N) (qq N)).
  reflexivity.
Qed.

(** 1 ≤ xₖ ≤ 2. *)
Lemma sx_range : forall N, 1 <= sx N /\ sx N <= 2.
Proof.
  intro N. destruct (pell_inv N) as [Hqpos [Hle Hub]].
  assert (Hiq : 0 < inject_Z (qq N)) by (apply injZ_pos; exact Hqpos).
  unfold sx. split.
  - apply Qle_shift_div_l; [ exact Hiq | ].
    setoid_replace (1 * inject_Z (qq N)) with (inject_Z (qq N)) by ring.
    apply injZ_le; exact Hle.
  - apply Qle_shift_div_r; [ exact Hiq | ].
    setoid_replace (2 * inject_Z (qq N)) with (inject_Z (2 * qq N)) by
      (rewrite inject_Z_mult; reflexivity).
    apply injZ_le; exact Hub.
Qed.

(** EXACT error: |xₖ²−2| = 1/qₖ². *)
Lemma sx_abs_eq : forall N, Qabs (sx N * sx N - 2) == / inject_Z (qq N * qq N).
Proof.
  intro N. destruct (pell_inv N) as [Hqpos _].
  assert (Hd : ~ inject_Z (qq N) == 0) by (apply injZ_neq0; lia).
  assert (Hqq2 : (0 < qq N * qq N)%Z) by nia.
  assert (Hd2 : ~ inject_Z (qq N * qq N) == 0) by (apply injZ_neq0; lia).
  assert (Hpos2 : 0 < inject_Z (qq N * qq N)) by (apply injZ_pos; exact Hqq2).
  assert (Hsq0 : sx N * sx N - 2 ==
                 inject_Z (pp N * pp N - 2 * (qq N * qq N)) / inject_Z (qq N * qq N)).
  { unfold sx.
    setoid_replace
      (inject_Z (pp N) / inject_Z (qq N) * (inject_Z (pp N) / inject_Z (qq N)) - 2)
      with ((inject_Z (pp N) * inject_Z (pp N) - 2 * (inject_Z (qq N) * inject_Z (qq N)))
            / (inject_Z (qq N) * inject_Z (qq N)))
      by (field; exact Hd).
    rewrite sx_num_eq. rewrite <- (inject_Z_mult (qq N) (qq N)). reflexivity. }
  rewrite Hsq0.
  destruct (pell_pm N) as [Hpm | Hpm]; rewrite Hpm.
  - setoid_replace (inject_Z 1) with 1 by reflexivity.
    setoid_replace (1 / inject_Z (qq N * qq N)) with (/ inject_Z (qq N * qq N))
      by (field; exact Hd2).
    rewrite Qabs_pos; [ reflexivity | apply Qlt_le_weak; apply Qinv_lt_0_compat; exact Hpos2 ].
  - setoid_replace (inject_Z (-1)) with (-(1)) by reflexivity.
    setoid_replace (-(1) / inject_Z (qq N * qq N)) with (- / inject_Z (qq N * qq N))
      by (field; exact Hd2).
    rewrite Qabs_neg.
    + ring.
    + assert (Hinv : 0 < / inject_Z (qq N * qq N)) by (apply Qinv_lt_0_compat; exact Hpos2).
      lra.
Qed.

(* ===================================================================== *)
(*  Main brick: a rational uncovered by the first N "gap > 1/(k+1)" sets   *)
(* ===================================================================== *)

(** ★★ For every N there is x ∈ [1,2]∩ℚ with |x²−2| ≤ 1/(k+1) for all k ≤ N — a rational so close to √2
    that the first N+1 "gap" neighbourhoods all miss it.  x := xₙ (Pell). *)
Theorem sqrt2_uncovered : forall N : nat,
  exists x : Q, (1 <= x /\ x <= 2) /\
    forall k : nat, (k <= N)%nat -> Qabs (x * x - 2) <= / inject_Z (Z.of_nat (S k)).
Proof.
  intro N. exists (sx N). split; [ apply sx_range | ].
  intros k Hk.
  rewrite sx_abs_eq.
  apply Qinv_antitone.
  - apply injZ_pos. lia.
  - apply injZ_le.
    destruct (pell_inv N) as [Hqpos _].
    pose proof (qq_ge N) as HqN.
    assert (HkN : (Z.of_nat (S k) <= Z.of_nat (S N))%Z) by (apply Nat2Z.inj_le; lia).
    nia.
Qed.
