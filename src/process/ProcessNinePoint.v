(** * ProcessNinePoint.v — 0,999… = 1 as point-equality of processes (F-11)

    ================= E/R/R разбор: «0,999… = 1» =================
    Система — НЕ «бесконечная десятичная дробь как объект», а процесс
    приближений и его равенство-как-точки единице. Rules -> Roles -> Elements:

      Rules (L5): process_equiv (~~) — когда два процесса именуют ОДНУ точку;
                  правило записи: n-я усечёнка = 1 - 1/10^(n+1).
      Roles (L4): «значение 0,999…» / «единица как точка» = позиция
                  «приближаемое значение», занимаемая процессом.
      Elements  : процессы nine_raw (0,9; 0,99; …) и const 1 — РАЗНЫЕ носители;
                  рациональные усечёнки на каждом шаге (L1+P4).

    ДИАГНОСТИКА (растворяем «парадокс 0,999… < 1»):
    - на уровне ЭЛЕМЕНТОВ каждая усечёнка  nine_raw n = 1 - 1/10^(n+1)  СТРОГО
      МЕНЬШЕ 1 (теорема nine_raw_lt_one) — это ВЕРНО;
    - на уровне РОЛИ процессы 0,999… и 1 занимают ОДНУ точку: nine_raw ~~ 1
      (теорема nine_equiv_one);
    - «парадокс» = смешение уровней: поэлементное «< 1» переносят на роль.
    Корневая P4: «0,999…» — НЕ завершённый десятичный объект, а процесс
    (правило порождения усечёнок); «= 1» — НЕ лейбницево равенство (процессы
    РАЗНЫЕ: nine_raw 0 = 0,9 <> 1), а равенство КАК ТОЧЕК (один режим/класс).
    Поэтому утверждаем «~~» (равенство точек), НЕ «=» (тождество объектов).

    Status: F-11 — nine_raw ~~ const 1, axiom-free.
    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Powers of ten, as a rational; the truncation process 0,9; 0,99; …     *)
(* ===================================================================== *)

Fixpoint pow10 (n : nat) : positive :=
  match n with
  | O => 1%positive
  | S k => (10 * pow10 k)%positive
  end.

Definition ten_pow (n : nat) : Q := inject_Z (Z.pos (pow10 n)).

Lemma ten_pow_pos : forall n, 0 < ten_pow n.
Proof.
  intros n. unfold ten_pow. change 0 with (inject_Z 0).
  rewrite <- Zlt_Qlt. lia.
Qed.

(** Growth: 10^m dominates m+1 (mirror of pow2_ge_Sn). *)
Lemma pow10_ge : forall m, (Z.of_nat (S m) <= Z.pos (pow10 m))%Z.
Proof.
  induction m as [|k IH].
  - simpl. lia.
  - change (pow10 (S k)) with (10 * pow10 k)%positive.
    rewrite Pos2Z.inj_mul. lia.
Qed.

(** The n-th decimal truncation 0,9…9 (n+1 nines): 1 - 1/10^(n+1). *)
Definition nine_raw : RealProcess := fun n => 1 - 1 / ten_pow (S n).

(* ===================================================================== *)
(*  Element level: every finite truncation is STRICTLY below 1            *)
(* ===================================================================== *)

Lemma nine_raw_lt_one : forall n, nine_raw n < 1.
Proof.
  intros n. unfold nine_raw.
  assert (Hpos : 0 < 1 / ten_pow (S n)).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. apply ten_pow_pos. }
  lra.
Qed.

(* ===================================================================== *)
(*  Role level: the truncation process names the SAME point as 1          *)
(* ===================================================================== *)

Theorem nine_equiv_one : nine_raw ~~ const_process 1.
Proof.
  intros eps Heps.
  destruct (q_archimedean 1 eps Heps) as [K HK].   (* 1 < inject_Z (Z.of_nat K) * eps *)
  exists K. intros n Hn.
  assert (Hpos : 0 < 1 / ten_pow (S n)).
  { unfold Qdiv. rewrite Qmult_1_l. apply Qinv_lt_0_compat. apply ten_pow_pos. }
  (* The error |nine_raw n - 1| equals the tail 1/10^(n+1). *)
  assert (Eabs : Qabs (nine_raw n - const_process 1 n) == 1 / ten_pow (S n)).
  { assert (E1 : nine_raw n - const_process 1 n == - (1 / ten_pow (S n))).
    { unfold nine_raw, const_process. set (x := 1 / ten_pow (S n)). ring. }
    rewrite (Qabs_wd _ _ E1). rewrite Qabs_opp.
    apply Qabs_pos. apply Qlt_le_weak, Hpos. }
  rewrite Eabs.
  (* Tail bound: 1/10^(n+1) < eps. *)
  apply Qlt_shift_div_r.
  - apply ten_pow_pos.
  - (* 1 < eps * 10^(n+1) *)
    assert (Hmono : inject_Z (Z.of_nat K) <= ten_pow (S n)).
    { unfold ten_pow. rewrite <- Zle_Qle.
      pose proof (pow10_ge (S n)) as G.
      assert (HKn : (Z.of_nat K <= Z.of_nat (S (S n)))%Z) by lia.
      lia. }
    assert (Hle : inject_Z (Z.of_nat K) * eps <= ten_pow (S n) * eps).
    { apply Qmult_le_compat_r. exact Hmono. apply Qlt_le_weak, Heps. }
    rewrite (Qmult_comm eps (ten_pow (S n))).
    apply Qlt_le_trans with (inject_Z (Z.of_nat K) * eps); [ exact HK | exact Hle ].
Qed.

(** Hence 0,999… is a Cauchy real (it shares 1's point). *)
Theorem nine_raw_is_Cauchy : is_Cauchy nine_raw.
Proof.
  apply (equiv_cauchy_l (const_process 1) nine_raw).
  - apply process_equiv_sym. exact nine_equiv_one.
  - apply const_is_Cauchy.
Qed.

(* Computational sanity: the first truncation is 0,9. *)
Example nine_raw_0 : nine_raw 0%nat == 9 # 10.
Proof. reflexivity. Qed.

Print Assumptions nine_equiv_one.
