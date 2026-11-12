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

    STATUS: 15 Qed, 0 Admitted, 0 axioms  (witness from Sqrt2Approx; irrationality from analysis.Sqrt2Irrational)
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

(* ===================================================================== *)
(*  Nov 2026: the sets U k ARE open; and the same failure stated in the    *)
(*  very definitions of the positive theorem (HeineBorel_ERR.v)            *)
(* ===================================================================== *)

From Stdlib Require Import Qminmax.
From ToS Require Import stdlib.Topology.
From ToS Require Import HeineBorel_ERR.

(** Each U k is open in the sense of Topology.is_open (until Nov 2026 this
    stood in the header comment only). *)
Lemma U_open : forall k : nat, is_open (U k).
Proof.
  intros k x Hx. unfold U in Hx.
  remember (inject_Z (Z.of_nat (S k))) as n eqn:En.
  assert (Hn : 0 < n) by (rewrite En; apply injZ_pos; lia).
  assert (Hg : exists g : Q, 0 <= g /\ 1 < n * g /\
            ((x * x - 2 < 0 /\ g == - (x * x - 2)) \/ (0 <= x * x - 2 /\ g == x * x - 2))).
  { exists (Qabs (x * x - 2)). split; [apply Qabs_nonneg | split; [exact Hx|]].
    destruct (Qlt_le_dec (x * x - 2) 0) as [Hneg | Hpos].
    - left. split; [exact Hneg | apply Qabs_neg; lra].
    - right. split; [exact Hpos | apply Qabs_pos; exact Hpos]. }
  destruct Hg as [g [Hg0 [Hng Hcase]]].
  assert (Ht : / n < g).
  { assert (E : / n == 1 / n) by (field; lra). rewrite E.
    apply Qlt_shift_div_r; [exact Hn | lra]. }
  assert (HW : exists W : Q, 0 < W /\ 2 * Qabs x + 1 <= W).
  { exists (2 * Qabs x + 1). pose proof (Qabs_nonneg x). split; lra. }
  destruct HW as [W [HW0 HWx]].
  assert (Heps : exists eps : Q, 0 < eps /\ eps <= 1 /\ eps * W <= g - / n).
  { exists (Qmin 1 ((g - / n) / W)).
    assert (Hq : 0 < (g - / n) / W) by (apply Qlt_shift_div_l; [exact HW0 | lra]).
    split; [apply Q.min_glb_lt; lra | split; [apply Q.le_min_l |]].
    assert (E : (g - / n) / W * W == g - / n) by (field; lra).
    apply Qle_trans with ((g - / n) / W * W).
    - apply Qmult_le_compat_r; [apply Q.le_min_r | lra].
    - rewrite E. apply Qle_refl. }
  destruct Heps as [eps [He0 [He1 HB]]].
  exists eps. split; [exact He0|].
  intros y Hy. unfold open_ball in Hy. unfold U. rewrite <- En.
  apply Qabs_Qlt_condition in Hy. destruct Hy as [Hy1 Hy2].
  assert (Hxa : x <= Qabs x) by apply Qle_Qabs.
  assert (Hxb : - x <= Qabs x) by (rewrite <- Qabs_opp; apply Qle_Qabs).
  assert (Hv1 : y + x < W) by lra.
  assert (Hv2 : - W < y + x) by lra.
  assert (P1 : 0 < (eps - (y - x)) * (W + (y + x))) by (apply Qmult_lt_0_compat; lra).
  assert (P2 : 0 < (eps + (y - x)) * (W - (y + x))) by (apply Qmult_lt_0_compat; lra).
  assert (P3 : 0 < (eps + (y - x)) * (W + (y + x))) by (apply Qmult_lt_0_compat; lra).
  assert (P4 : 0 < (eps - (y - x)) * (W - (y + x))) by (apply Qmult_lt_0_compat; lra).
  assert (Hup : y * y - x * x < eps * W) by lra.
  assert (Hlo : - (eps * W) < y * y - x * x) by lra.
  assert (Hfin : / n < Qabs (y * y - 2)).
  { destruct Hcase as [[Hneg Hgeq] | [Hpos Hgeq]].
    - pose proof (Qle_Qabs (- (y * y - 2))) as Hab. rewrite Qabs_opp in Hab. lra.
    - pose proof (Qle_Qabs (y * y - 2)) as Hab. lra. }
  assert (Hm : / n * n < Qabs (y * y - 2) * n)
    by (apply Qmult_lt_compat_r; [exact Hn | exact Hfin]).
  assert (E : / n * n == 1) by (field; lra).
  lra.
Qed.

(** The cover of the chapter in rational form: the radius shrinks at the
    cut sqrt 2.  C(x) = min(1, |x^2 - 2|) / 8. *)
Definition gap (x : Q) : Q := Qabs (x * x - 2).

Definition C_gap : OpenCover := fun x => Qmin 1 (gap x) * (1#8).

Lemma gap_pos : forall x, 0 < gap x.
Proof.
  intros x. unfold gap.
  destruct (Qlt_le_dec 0 (Qabs (x * x - 2))) as [H | H]; [exact H | exfalso].
  apply Qabs_Qle_condition in H. destruct H as [H1 H2].
  apply (no_rational_sqrt2 x). lra.
Qed.

Lemma C_gap_valid : forall a b, valid_cover C_gap a b.
Proof.
  intros a b x _. unfold C_gap. pose proof (gap_pos x) as Hg.
  assert (Hm : 0 < Qmin 1 (gap x)) by (apply Q.min_glb_lt; lra).
  assert (Hgoal : 0 < Qmin 1 (gap x) * (1#8)) by lra. exact Hgoal.
Qed.

Lemma covered_far_from_gap : forall c y,
  1 <= y -> y <= 2 -> covered_by C_gap c y -> (3#8) * gap c < gap y.
Proof.
  intros c y Hy1 Hy2 Hcov. unfold covered_by, C_gap in Hcov.
  pose proof (gap_pos c) as Hg.
  assert (Hm1 : Qmin 1 (gap c) <= 1) by apply Q.le_min_l.
  assert (Hm2 : Qmin 1 (gap c) <= gap c) by apply Q.le_min_r.
  assert (Hm0 : 0 < Qmin 1 (gap c)) by (apply Q.min_glb_lt; lra).
  assert (Hd0 : 0 < Qmin 1 (gap c) * (1#8)) by lra.
  assert (Hd1 : Qmin 1 (gap c) * (1#8) <= 1#8) by lra.
  assert (Hd2 : Qmin 1 (gap c) * (1#8) <= gap c * (1#8)) by lra.
  clear Hm1 Hm2 Hm0.
  revert Hcov Hd0 Hd1 Hd2. generalize (Qmin 1 (gap c) * (1#8)). intros d Hcov Hd0 Hd1 Hd2.
  apply Qabs_Qlt_condition in Hcov. destruct Hcov as [Hc1 Hc2].
  assert (Hs : 0 < y + c) by lra.
  assert (Hs2 : 0 < 5 - (y + c)) by lra.
  assert (P1 : 0 < (d - (y - c)) * (y + c)) by (apply Qmult_lt_0_compat; lra).
  assert (P2 : 0 < ((y - c) + d) * (y + c)) by (apply Qmult_lt_0_compat; lra).
  assert (P3 : 0 < d * (5 - (y + c))) by (apply Qmult_lt_0_compat; lra).
  assert (Hup : y * y - c * c < d * 5) by lra.
  assert (Hlo : - (d * 5) < y * y - c * c) by lra.
  unfold gap in *.
  destruct (Qlt_le_dec (c * c - 2) 0) as [Hn | Hp].
  - rewrite (Qabs_neg (c * c - 2)) in * by lra.
    pose proof (Qle_Qabs (- (y * y - 2))) as Hab. rewrite Qabs_opp in Hab. lra.
  - rewrite (Qabs_pos (c * c - 2)) in * by lra.
    pose proof (Qle_Qabs (y * y - 2)) as Hab. lra.
Qed.

Lemma inv_le_of : forall (n : nat) (g : Q),
  1 <= g * inject_Z (Z.of_nat (S n)) -> / inject_Z (Z.of_nat (S n)) <= g.
Proof.
  intros n g H.
  assert (HN : 0 < inject_Z (Z.of_nat (S n))) by (apply injZ_pos; lia).
  assert (E : / inject_Z (Z.of_nat (S n)) == 1 / inject_Z (Z.of_nat (S n))) by (field; lra).
  rewrite E. apply Qle_shift_div_r; [exact HN | exact H].
Qed.

Lemma small_gap_level : forall centers : list Q,
  exists N : nat, forall c, In c centers ->
    1 <= ((3#8) * gap c) * inject_Z (Z.of_nat (S N)).
Proof.
  induction centers as [| c rest IH].
  - exists 0%nat. intros c [].
  - destruct IH as [N1 HN1].
    pose proof (gap_pos c) as Hg.
    assert (Hg' : 0 < (3#8) * gap c) by lra.
    destruct (Qarchimedean (/ ((3#8) * gap c))) as [p Hp].
    set (N2 := Pos.to_nat p).
    exists (Nat.max N1 N2). intros c' [Heq | Hin].
    + subst c'.
      assert (Hle : inject_Z (Z.pos p) <= inject_Z (Z.of_nat (S (Nat.max N1 N2)))).
      { apply injZ_le. unfold N2. lia. }
      assert (Hkey : / ((3#8) * gap c) * ((3#8) * gap c) < inject_Z (Z.pos p) * ((3#8) * gap c)).
      { apply Qmult_lt_compat_r; [exact Hg' | exact Hp]. }
      assert (E1 : / ((3#8) * gap c) * ((3#8) * gap c) == 1) by (field; lra).
      rewrite E1 in Hkey.
      assert (P : 0 <= ((3#8) * gap c) * (inject_Z (Z.of_nat (S (Nat.max N1 N2))) - inject_Z (Z.pos p))).
      { apply Qmult_le_0_compat; lra. }
      lra.
    + pose proof (HN1 c' Hin) as H1.
      pose proof (gap_pos c') as Hg1.
      assert (Hle : inject_Z (Z.of_nat (S N1)) <= inject_Z (Z.of_nat (S (Nat.max N1 N2)))).
      { apply injZ_le. lia. }
      assert (P : 0 <= ((3#8) * gap c') * (inject_Z (Z.of_nat (S (Nat.max N1 N2))) - inject_Z (Z.of_nat (S N1)))).
      { apply Qmult_le_0_compat; lra. }
      lra.
Qed.

Lemma is_covered_In : forall C centers y,
  is_covered C centers y -> exists c, In c centers /\ covered_by C c y.
Proof.
  intros C centers y. induction centers as [| c rest IH]; simpl; intro H; [contradiction|].
  destruct H as [H | H].
  - exists c. split; [left; reflexivity | exact H].
  - destruct (IH H) as [c' [Hin Hc']]. exists c'. split; [right; exact Hin | exact Hc'].
Qed.

(** No finite family of centres (wherever they lie) covers [1,2] in Q. *)
Theorem C_gap_no_finite_subcover : forall centers : FiniteSubcover,
  ~ covers_interval C_gap centers 1 2.
Proof.
  intros centers Hcov.
  destruct (small_gap_level centers) as [N HN].
  destruct (sqrt2_uncovered N) as [y [[Hy1 Hy2] Hb]].
  specialize (Hb N (le_n _)).
  destruct (is_covered_In _ _ _ (Hcov y (conj Hy1 Hy2))) as [c [Hin Hc]].
  pose proof (covered_far_from_gap c y Hy1 Hy2 Hc) as Hfar.
  pose proof (inv_le_of N _ (HN c Hin)) as Hsmall.
  unfold gap in *. lra.
Qed.

(** Classical Heine-Borel (no condition on the radii) is FALSE over Q --
    in the definitions of HeineBorel_ERR.v. *)
Theorem classical_Heine_Borel_fails_over_Q :
  ~ (forall (C : OpenCover) (a b : Q), a < b -> valid_cover C a b ->
       exists centers : FiniteSubcover, covers_interval C centers a b).
Proof.
  intro H.
  destruct (H C_gap 1 2 ltac:(lra) (C_gap_valid 1 2)) as [centers Hc].
  exact (C_gap_no_finite_subcover centers Hc).
Qed.

(** This cover has no uniform lower bound of the radii. *)
Corollary C_gap_not_uniform : forall delta, ~ uniform_cover C_gap 1 2 delta.
Proof.
  intros delta Hu.
  destruct (Heine_Borel_uniform C_gap 1 2 delta ltac:(lra) Hu) as [centers Hc].
  exact (C_gap_no_finite_subcover centers Hc).
Qed.
