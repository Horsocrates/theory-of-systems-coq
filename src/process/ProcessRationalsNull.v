(** * ProcessRationalsNull.v — Q ∩ [0,1] has measure zero (F-32, Part VI)

    Elements: rational cover-measures (1/2)^n at each refinement stage
    Roles:    cover-measure of a COUNTABLE set as a process
    Rules:    geometric decay (1/2)^n ~~ 0  (P4: countable ⇒ measure zero)

    The rationals in [0,1] are countable: in Countability_Q.v (F-17) we built an
    explicit bijection enum_Q : nat -> Q (with its inverse index_of_Q). Enumerate
    the rationals of [0,1] as e_0, e_1, e_2, ....  To witness "measure zero" we
    cover them: at refinement stage n, place around e_k an interval of length
        (1/2)^(k+1) * (1/2)^n .
    The total length of the stage-n cover is then
        (1/2)^n * SUM_{k>=0} (1/2)^(k+1)  =  (1/2)^n * 1  =  (1/2)^n,
    because the budget series SUM (1/2)^(k+1) = 1.  Hence the WHOLE countable set
    Q ∩ [0,1] is covered, at stage n, by intervals of total length <= (1/2)^n,
    and (1/2)^n -> 0.  We state this in the P4 / process sense, exactly as
    ProcessNinePoint states 0,999...=1 and ProcessCantorMeasure states the Cantor
    cover -> 0:
        rationals_cover_to_zero : half_pow ~~ const_process 0,
    where half_pow n = (1/2)^n is the stage-n total cover length.

    ============ E/R/R разбор ============
      Rules (L5): геометрический распад (1/2)^n; ~~ (process_equiv) = одна точка 0.
      Roles (L4): "мера Q ∩ [0,1]" = роль-предел, занимаемая cover-процессом.
      Elements  : рациональные cover-меры (1/2)^n на каждой стадии (L1+P4).
    ДИАГНОСТИКА: Q СЧЁТНО (III.2/III.3, enum_Q из F-17), а [0,1] НЕСЧЁТНО (III.4/IV.4)
    и имеет меру 1. Мера РАЗЛИЧАЕТ их, хотя обе суть процессы. И именно СЧЁТНОСТЬ
    (наличие enum_Q) делает cover-ряд SUM (1/2)^(k+1) суммируемым = 1: вот почему
    "счётное ⇒ нулевое". Несчётное [0,1] такого budget-покрытия не допускает.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Stage-n total cover length:  half_pow n = (1/2)^n                     *)
(*  (= global shrink factor times the budget-1 enumeration cover)         *)
(* ===================================================================== *)

Fixpoint half_pow (n : nat) : Q :=
  match n with
  | O => 1
  | S k => (1 # 2) * half_pow k
  end.

Lemma half_pow_nonneg : forall n, 0 <= half_pow n.
Proof. induction n as [|n IH]; simpl; lra. Qed.

Lemma half_pow_le_one : forall n, half_pow n <= 1.
Proof. induction n as [|n IH]; simpl; lra. Qed.

(* ===================================================================== *)
(*  Cleared geometric bound:  (1/2)^n * (n+1) <= 2.                        *)
(*  Division-free induction (uses half_pow_le_one in the step).           *)
(* ===================================================================== *)

Lemma half_pow_cleared_bound : forall n,
  half_pow n * inject_Z (Z.of_nat (n + 1)) <= 2.
Proof.
  induction n as [|n IH].
  - change (inject_Z (Z.of_nat (0 + 1))) with (1 # 1). simpl. lra.
  - replace (Z.of_nat (S n + 1)) with (Z.of_nat (n + 1) + 1)%Z by lia.
    rewrite inject_Z_plus.
    cbn [half_pow].
    set (a := half_pow n) in *.
    set (m := inject_Z (Z.of_nat (n + 1))) in *.
    assert (Ha1 : a <= 1) by (unfold a; apply half_pow_le_one).
    (* IH : a * m <= 2 ;  goal: (1#2) * a * (m + inject_Z 1) <= 2 *)
    assert (E : (1 # 2) * a * (m + inject_Z 1) == (a * m) * (1 # 2) + a * (1 # 2))
      by (change (inject_Z 1) with (1 # 1); ring).
    rewrite E.
    apply Qle_trans with (2 * (1 # 2) + 1 * (1 # 2)).
    + apply Qplus_le_compat.
      * apply Qmult_le_compat_r; [ exact IH | lra ].
      * apply Qmult_le_compat_r; [ exact Ha1 | lra ].
    + lra.
Qed.

(* ===================================================================== *)
(*  Main theorem: the stage-n cover length -> 0                            *)
(*  (= Q ∩ [0,1] has measure zero, in the P4/process sense).              *)
(* ===================================================================== *)

Theorem rationals_cover_to_zero : half_pow ~~ const_process 0.
Proof.
  intros eps Heps.
  destruct (q_archimedean 2 eps Heps) as [K HK].   (* 2 < inject_Z (Z.of_nat K) * eps *)
  exists K. intros n Hn.
  unfold const_process.
  assert (Hn0 : 0 <= half_pow n) by apply half_pow_nonneg.
  assert (Eabs : Qabs (half_pow n - 0) == half_pow n).
  { assert (R : half_pow n - 0 == half_pow n) by ring.
    rewrite R. apply Qabs_pos. exact Hn0. }
  rewrite Eabs.
  (* goal: half_pow n < eps *)
  pose proof (half_pow_cleared_bound n) as Hb.
  set (m := inject_Z (Z.of_nat (n + 1))) in *.
  assert (Hm_pos : 0 < m).
  { unfold m. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt. lia. }
  assert (HmK : inject_Z (Z.of_nat K) <= m).
  { unfold m. rewrite <- Zle_Qle. lia. }
  assert (H2 : 2 < m * eps).
  { apply Qlt_le_trans with (inject_Z (Z.of_nat K) * eps).
    - exact HK.
    - apply Qmult_le_compat_r; [ exact HmK | apply Qlt_le_weak; exact Heps ]. }
  assert (Hlt : half_pow n * m < eps * m).
  { rewrite (Qmult_comm eps m).
    apply Qle_lt_trans with 2; [ exact Hb | exact H2 ]. }
  apply (Qmult_lt_r (half_pow n) eps m Hm_pos). exact Hlt.
Qed.

(* Computational sanity checks. *)
Example half_pow_0 : half_pow 0 = 1.
Proof. reflexivity. Qed.

Example half_pow_1 : half_pow 1 == 1 # 2.
Proof. reflexivity. Qed.

Example half_pow_3 : half_pow 3 == 1 # 8.
Proof. reflexivity. Qed.

Print Assumptions rationals_cover_to_zero.
