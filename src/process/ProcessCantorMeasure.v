(** * ProcessCantorMeasure.v — The Cantor set has measure zero (F-30, Part VI)

    Elements: rational cover-measures (2/3)^n at each stage of the construction
    Roles:    cover-measure as a process (total length of the stage-n cover)
    Rules:    geometric decay (2/3)^n ~~ 0  (P4: measure-zero = process to 0)

    The ternary Cantor set: start with [0,1]; at each stage remove the open
    middle third of every remaining interval. Stage n then consists of 2^n
    closed intervals, each of length 3^{-n}, so the TOTAL length of the
    stage-n cover is
        cantor_cover_measure n  =  2^n * 3^{-n}  =  (2/3)^n.
    The Cantor set is contained in the stage-n cover for every n, hence its
    (outer) measure is <= (2/3)^n for all n. Since (2/3)^n -> 0, the Cantor
    set has measure zero. We state this in the P4 / process sense, exactly as
    ProcessNinePoint states 0,999...=1: the cover-measure PROCESS names the
    same point as 0:
        cantor_measure_zero : cantor_cover_measure ~~ const_process 0.

    ============ E/R/R разбор ============
      Rules (L5): геометрический распад (2/3)^n; ~~ (process_equiv) = одна точка.
      Roles (L4): "мера Канторова множества" = роль-предел, занимаемая cover-процессом.
      Elements  : рациональные cover-меры (2/3)^n на каждой стадии (L1+P4).
    ДИАГНОСТИКА: Канторово множество НЕСЧЁТНО (III.4/IV.4), но меры НУЛЬ — обе
    величины суть ПРОЦЕССЫ (само множество = вложенные интервалы; его мера =
    (2/3)^n -> 0), а не завершённые объекты. "Несчётно, но меры нуль" — не
    парадокс: счёт и мера отвечают на РАЗНЫЕ вопросы о процессе.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The cover-measure process:  cantor_cover_measure n = (2/3)^n          *)
(*  (= 2^n intervals, each of length 3^{-n}, total length (2/3)^n)        *)
(* ===================================================================== *)

Fixpoint cantor_cover_measure (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (2 # 3) * cantor_cover_measure k
  end.

Lemma cantor_nonneg : forall n, 0 <= cantor_cover_measure n.
Proof. induction n as [|n IH]; simpl; lra. Qed.

Lemma cantor_le_one : forall n, cantor_cover_measure n <= 1.
Proof. induction n as [|n IH]; simpl; lra. Qed.

(* ===================================================================== *)
(*  Cleared geometric bound:  (2/3)^n * (n+2) <= 2.                        *)
(*  Division-free induction (uses cantor_le_one in the step).             *)
(* ===================================================================== *)

Lemma cantor_cleared_bound : forall n,
  cantor_cover_measure n * inject_Z (Z.of_nat (n + 2)) <= 2.
Proof.
  induction n as [|n IH].
  - change (inject_Z (Z.of_nat (0 + 2))) with (2 # 1). simpl. lra.
  - replace (Z.of_nat (S n + 2)) with (Z.of_nat (n + 2) + 1)%Z by lia.
    rewrite inject_Z_plus.
    cbn [cantor_cover_measure].
    set (a := cantor_cover_measure n) in *.
    set (m := inject_Z (Z.of_nat (n + 2))) in *.
    assert (Ha1 : a <= 1) by (unfold a; apply cantor_le_one).
    (* IH : a * m <= 2 ;  goal: (2#3) * a * (m + inject_Z 1) <= 2 *)
    assert (E : (2 # 3) * a * (m + inject_Z 1) == (a * m) * (2 # 3) + a * (2 # 3))
      by (change (inject_Z 1) with (1 # 1); ring).
    rewrite E.
    apply Qle_trans with (2 * (2 # 3) + 1 * (2 # 3)).
    + apply Qplus_le_compat.
      * apply Qmult_le_compat_r; [ exact IH | lra ].
      * apply Qmult_le_compat_r; [ exact Ha1 | lra ].
    + assert (E3 : 2 * (2 # 3) + 1 * (2 # 3) == 2) by ring.
      rewrite E3. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  Main theorem: the cover-measure process converges to 0                *)
(*  (= the Cantor set has measure zero, in the P4/process sense).         *)
(* ===================================================================== *)

Theorem cantor_measure_zero : cantor_cover_measure ~~ const_process 0.
Proof.
  intros eps Heps.
  destruct (q_archimedean 2 eps Heps) as [K HK].   (* 2 < inject_Z (Z.of_nat K) * eps *)
  exists K. intros n Hn.
  unfold const_process.
  assert (Hn0 : 0 <= cantor_cover_measure n) by apply cantor_nonneg.
  assert (Eabs : Qabs (cantor_cover_measure n - 0) == cantor_cover_measure n).
  { assert (R : cantor_cover_measure n - 0 == cantor_cover_measure n) by ring.
    rewrite R. apply Qabs_pos. exact Hn0. }
  rewrite Eabs.
  (* goal: cantor_cover_measure n < eps *)
  pose proof (cantor_cleared_bound n) as Hb.
  set (m := inject_Z (Z.of_nat (n + 2))) in *.
  assert (Hm_pos : 0 < m).
  { unfold m. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
  assert (HmK : inject_Z (Z.of_nat K) <= m).
  { unfold m. rewrite <- Zle_Qle. lia. }
  assert (H2 : 2 < m * eps).
  { apply Qlt_le_trans with (inject_Z (Z.of_nat K) * eps).
    - exact HK.
    - apply Qmult_le_compat_r; [ exact HmK | apply Qlt_le_weak; exact Heps ]. }
  assert (Hlt : cantor_cover_measure n * m < eps * m).
  { rewrite (Qmult_comm eps m).
    apply Qle_lt_trans with 2; [ exact Hb | exact H2 ]. }
  apply (Qmult_lt_r (cantor_cover_measure n) eps m Hm_pos). exact Hlt.
Qed.

(* Computational sanity checks. *)
Example cantor_cover_0 : cantor_cover_measure 0 = 1.
Proof. reflexivity. Qed.

Example cantor_cover_1 : cantor_cover_measure 1 == 2 # 3.
Proof. reflexivity. Qed.

Example cantor_cover_2 : cantor_cover_measure 2 == 4 # 9.
Proof. reflexivity. Qed.

Print Assumptions cantor_measure_zero.
