(** * QIntervalNotCompact.v — F-20: ℚ-non-compactness as a THEOREM.  The rational interval [1,2]∩ℚ is
       closed and bounded yet NOT compact: an explicit open cover (intervals dodging the √2-gap) has NO
       finite subcover.  This turns the honest "ℚ не компактно" of V.2 §2.5 from a stated limitation into
       a proved fact — with the witness built from the Pell √2-approximation (Sqrt2Approx.v).

    -- The cover (each Uₖ open) --
      Uₖ x := 1 < (k+1)·|x²−2|   (i.e. |x²−2| > 1/(k+1)) — the points whose square is > 1/(k+1) away from 2.
      Each Uₖ is open (preimage of the open set {t : |t−2|>1/(k+1)} under the continuous x↦x²); their union
      is all of [1,2]∩ℚ because every rational has x²≠2 (√2 irrational, analysis/Sqrt2Irrational.v) so
      |x²−2|>0 and Archimedes places it beyond some 1/(k+1).

    -- No finite subcover (the √2-gap) --
      Any finite subfamily has a largest index N; by Sqrt2Approx.sqrt2_uncovered there is a rational
      xₙ ∈ [1,2] (a Pell convergent of √2) with |xₙ²−2| ≤ 1/(k+1) for ALL k ≤ N — so xₙ lies in NONE of the
      chosen Uₖ.  The rationals crowd arbitrarily close to √2 (which is absent), leaving every finite
      subfamily with an uncovered point.  That is exactly the failure of compactness over ℚ.

    -- The boundary (E/R/R) --
      Classical compactness = a Rule about a COMPLETED cover of a COMPLETED point-set (reifying Element-
      totality).  The ToS route is the Lebesgue number (HeineBorel_ERR.v): operational uniform refinement,
      no completed cover.  The completed-cover version is a P4 category error, and THIS witness shows ℚ has
      no such finite reduction — genuinely, not as a gap.

    ============ E/R/R разбор ============
      Elements : рациональные точки [1,2]∩ℚ; конечный список индексов L; приближения Пелля xₙ — актуальны (P4).
      Roles    : √2 = role-limit (отсутствующая предельная точка); покрытие Uₖ = роль-окрестности; «компактность» = role-limit.
      Rules    : Uₖ покрывают (x²≠2 + Архимед); конечное подпокрытие невозможно (xₙ у √2-зазора не покрыт).
      ДИАГНОСТИКА (P4): некомпактность ℚ = ДОКАЗАННЫЙ факт (свидетель xₙ), не дефект; ToS-путь = число Лебега
        (операциональное измельчение). Классическое «завершённое покрытие завершённого множества» = ошибка P4.
        Уровень: `новая теорема` (негативная: ℚ genuinely не компактно).

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (witness from Sqrt2Approx; irrationality from analysis.Sqrt2Irrational)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia PeanoNat List.
From ToS Require Import Sqrt2Approx.
From ToS Require Import analysis.Sqrt2Irrational.
Import ListNotations.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The carrier and the open cover                                          *)
(* ===================================================================== *)

(** The carrier [1,2]∩ℚ. *)
Definition inC (x : Q) : Prop := 1 <= x /\ x <= 2.

(** The k-th cover set: |x²−2| > 1/(k+1), written cross-multiplied (no reciprocal). *)
Definition U (k : nat) (x : Q) : Prop := 1 < inject_Z (Z.of_nat (S k)) * Qabs (x * x - 2).

(* ===================================================================== *)
(*  Helpers: max of a list, and a nat above any rational (Archimedes)      *)
(* ===================================================================== *)

Lemma in_le_max : forall (L : list nat) k, In k L -> (k <= fold_right Nat.max O L)%nat.
Proof.
  induction L as [| a L IH]; intros k Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin]; [ lia | ].
    pose proof (IH k Hin). lia.
Qed.

Lemma nat_archimedean : forall q : Q, exists n : nat, q < inject_Z (Z.of_nat n).
Proof.
  intro q. destruct (Qarchimedean q) as [p Hp].
  exists (Pos.to_nat p). rewrite positive_nat_Z. exact Hp.
Qed.

(* ===================================================================== *)
(*  The cover covers [1,2]∩ℚ                                                *)
(* ===================================================================== *)

Theorem covers : forall x, inC x -> exists k, U k x.
Proof.
  intros x [Hlo Hhi].
  assert (Ht : ~ (x * x - 2 == 0)).
  { intro Hc. apply (no_rational_sqrt2 x). lra. }
  assert (Hd : 0 < Qabs (x * x - 2)).
  { destruct (Qlt_le_dec 0 (Qabs (x * x - 2))) as [H | H]; [ exact H | exfalso ].
    apply Qabs_Qle_condition in H. destruct H as [H1 H2]. apply Ht. lra. }
  assert (Hdne : ~ Qabs (x * x - 2) == 0) by lra.
  destruct (nat_archimedean (/ Qabs (x * x - 2))) as [n Hn].
  exists n. unfold U.
  assert (HSn : inject_Z (Z.of_nat n) <= inject_Z (Z.of_nat (S n))) by (apply injZ_le; lia).
  assert (Hlt : / Qabs (x * x - 2) < inject_Z (Z.of_nat (S n))) by lra.
  assert (Hkey : / Qabs (x * x - 2) * Qabs (x * x - 2)
                 < inject_Z (Z.of_nat (S n)) * Qabs (x * x - 2)).
  { rewrite (Qmult_lt_r (/ Qabs (x * x - 2)) (inject_Z (Z.of_nat (S n))) (Qabs (x * x - 2)) Hd).
    exact Hlt. }
  setoid_replace (/ Qabs (x * x - 2) * Qabs (x * x - 2)) with 1 in Hkey by (field; exact Hdne).
  exact Hkey.
Qed.

(* ===================================================================== *)
(*  No finite subcover (the √2-gap witness)                                 *)
(* ===================================================================== *)

Theorem no_finite_subcover :
  forall L : list nat, exists x, inC x /\ forall k, In k L -> ~ U k x.
Proof.
  intro L. set (N := fold_right Nat.max O L).
  destruct (sqrt2_uncovered N) as [x [Hrange Hbound]].
  exists x. split; [ exact Hrange | ].
  intros k Hin Hcontra. unfold U in Hcontra.
  assert (Hk : (k <= N)%nat) by (apply in_le_max; exact Hin).
  pose proof (Hbound k Hk) as Hb.
  assert (HSk : 0 < inject_Z (Z.of_nat (S k))) by (apply injZ_pos; lia).
  assert (Hle : inject_Z (Z.of_nat (S k)) * Qabs (x * x - 2) <= 1).
  { setoid_replace 1 with (inject_Z (Z.of_nat (S k)) * / inject_Z (Z.of_nat (S k)))
      by (field; apply injZ_neq0; lia).
    rewrite (Qmult_le_l (Qabs (x * x - 2)) (/ inject_Z (Z.of_nat (S k)))
                        (inject_Z (Z.of_nat (S k))) HSk).
    exact Hb. }
  lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — ℚ∩[1,2] is not compact                                      *)
(* ===================================================================== *)

(** F-20 closed: [1,2]∩ℚ is closed and bounded but NOT compact — the open cover {Uₖ} (each Uₖ open, their
    union all of [1,2]∩ℚ) has NO finite subcover, the witness being a Pell convergent crowding the absent
    √2.  Compactness over ℚ genuinely fails; the ToS replacement is the Lebesgue number (HeineBorel_ERR.v),
    operational not completed.  Level: a new negative theorem (ℚ non-compactness made a fact). *)
Theorem Q_interval_not_compact :
  (forall x, inC x -> exists k, U k x)
  /\ (forall L : list nat, exists x, inC x /\ forall k, In k L -> ~ U k x).
Proof. split; [ exact covers | exact no_finite_subcover ]. Qed.
