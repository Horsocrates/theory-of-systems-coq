(** * CantorHeineQ.v — F-21: the Cantor–Heine theorem FAILS over ℚ, made explicit.  On [1,2]∩ℚ the
       function f(x)=1/(x²−2) is CONTINUOUS at every (rational) point yet NOT uniformly continuous — the
       √2-pole, absent from ℚ, lets f oscillate unboundedly in arbitrarily small windows.  This closes
       FORMALIZATION-BACKLOG F-21 (V.3 §3.3.2) on the canon analysis/Continuity.v, with the failure witness
       built from the Pell √2-approximation (Sqrt2Approx.v).

    -- Continuous (pointwise) --
      At x0∈[1,2], A0:=x0²−2≠0 (√2∉ℚ).  For x near x0 the denominator stays ≥|A0|/2, so
        |f x − f x0| = |x0²−x²| / (|x²−2|·|x0²−2|) ≤ 8|x−x0|/|A0|²,
      which a δ = min(|A0|/8, ε|A0|²/16) drives below ε.

    -- NOT uniformly continuous (the √2-pole) --
      The Pell convergents xₖ satisfy EXACTLY |xₖ²−2| = 1/qₖ², hence |f xₖ| = qₖ² → ∞.  Consecutive
      convergents are 1/(qₖqₖ₊₁)-close yet, by the reverse triangle inequality,
        |f xₖ − f xₖ₊₁| ≥ | |f xₖ₊₁| − |f xₖ| | = qₖ₊₁² − qₖ² ≥ 1.
      So with ε=1 no δ works: pick k with 1/(qₖqₖ₊₁) < δ — the two close points break the bound.  (No sign
      bookkeeping needed: the magnitude gap alone, qₖ₊₁²−qₖ² ≥ 1, defeats uniformity.)

    -- The boundary (E/R/R) --
      Cantor–Heine = a Rule "pointwise ⇒ uniform" THROUGH completed compactness; over ℚ the compactness
      step fails at the √2-gap (QIntervalNotCompact.v / F-20).  ToS does not need Cantor–Heine: uniformity
      is an EXPLICIT role-requirement (IVT/EVT hypothesize it) with the constructive Lipschitz route
      (analysis/Continuity.lipschitz_uniform).  The counterexample is honest content, not a defect.

    ============ E/R/R разбор ============
      Elements : рациональные точки [1,2]∩ℚ; Пелля-приближения xₖ; значения f xₖ=±qₖ² — все актуальны (P4).
      Roles    : √2-полюс = role-limit (отсутствующая особенность); равномерность = роль-требование, не следствие.
      Rules    : f непрерывна поточечно (знаменатель отделён от 0 у каждой точки); равномерность ломается у √2-зазора
                 (соседние xₖ близки, но |f xₖ−f xₖ₊₁|≥1).
      ДИАГНОСТИКА (P4): непрерывное-но-не-равномерное = ДОКАЗАННЫЙ контрпример (Cantor–Heine над ℚ ложен); шаг
        компактности проваливается (F-20). ToS: равномерность = явное правило-роль (Липшиц-маршрут). Уровень: `новая теорема`.

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (witness from Sqrt2Approx; irrationality from analysis.Sqrt2Irrational)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia Qminmax.
From ToS Require Import Sqrt2Approx.
From ToS Require Import analysis.Sqrt2Irrational.
From ToS Require Import analysis.Continuity.
Open Scope Q_scope.

Definition f (x : Q) : Q := / (x * x - 2).

(* ===================================================================== *)
(*  Small Q helpers                                                         *)
(* ===================================================================== *)

Lemma Qabs_inv : forall a : Q, Qabs (/ a) == / Qabs a.
Proof.
  intro a. destruct (Qlt_le_dec 0 (Qabs a)) as [Hpos | Hnp].
  - (* a apart from 0 *)
    assert (Hane : ~ a == 0).
    { intro Hc. rewrite Hc in Hpos. simpl in Hpos. (* Qabs 0 = 0 *)
      change (Qabs 0) with 0 in Hpos. lra. }
    apply (Qmult_inj_l _ _ (Qabs a)).
    { intro Hc. rewrite Hc in Hpos. lra. }
    rewrite <- Qabs_Qmult.
    setoid_replace (a * / a) with 1 by (field; exact Hane).
    setoid_replace (Qabs a * / Qabs a) with 1 by (field; intro Hc; rewrite Hc in Hpos; lra).
    reflexivity.
  - (* Qabs a <= 0, so a == 0 *)
    assert (Ha0 : a == 0).
    { pose proof (Qabs_nonneg a).
      assert (Qabs a == 0) by lra.
      apply Qabs_Qle_condition in Hnp. lra. }
    rewrite Ha0. reflexivity.
Qed.

Lemma Qabs_div_loc : forall a b : Q, Qabs (a / b) == Qabs a / Qabs b.
Proof. intros a b. unfold Qdiv. rewrite Qabs_Qmult, Qabs_inv. reflexivity. Qed.

Lemma div_lt : forall num den e : Q, 0 < den -> num < e * den -> num / den < e.
Proof.
  intros num den e Hd H.
  assert (Hdi : 0 < / den) by (apply Qinv_lt_0_compat; exact Hd).
  apply Qlt_le_trans with (e * den * / den).
  - unfold Qdiv. rewrite (Qmult_lt_r num (e * den) (/ den) Hdi). exact H.
  - setoid_replace (e * den * / den) with e by (field; lra). apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  Part 1: f is continuous on [1,2]∩ℚ                                      *)
(* ===================================================================== *)

(** A division-free midpoint helper (lra over ℚ does not normalise c/2, so we feed multiplied forms). *)
Lemma Qmid : forall a b c : Q, c - b <= a -> 2 * b < c -> c < 2 * a.
Proof. intros a b c H1 H2. lra. Qed.

Theorem cantor_heine_continuous : continuous_on f 1 2.
Proof.
  intros x0 [Hx0a Hx0b] eps Heps.
  assert (Ht0 : ~ (x0 * x0 - 2 == 0)) by (intro Hc; apply (no_rational_sqrt2 x0); lra).
  assert (Hc0 : 0 < Qabs (x0 * x0 - 2)).
  { destruct (Qlt_le_dec 0 (Qabs (x0 * x0 - 2))) as [HH | HH]; [ exact HH | exfalso ].
    apply Qabs_Qle_condition in HH. apply Ht0. lra. }
  set (c0 := Qabs (x0 * x0 - 2)) in *.
  assert (Hc0eq : c0 = Qabs (x0 * x0 - 2)) by reflexivity. clearbody c0.
  assert (Hpos8 : 0 < c0 / 8)
    by (unfold Qdiv; apply Qmult_lt_0_compat; [ exact Hc0 | apply Qinv_lt_0_compat; lra ]).
  assert (Hpos16 : 0 < eps * c0 * c0 / 16)
    by (unfold Qdiv; apply Qmult_lt_0_compat;
        [ apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; [ exact Heps | exact Hc0 ] | exact Hc0 ]
        | apply Qinv_lt_0_compat; lra ]).
  exists (Qmin (c0 / 8) (eps * c0 * c0 / 16)).
  split.
  { apply Q.min_glb_lt; [ exact Hpos8 | exact Hpos16 ]. }
  intros x [Hxa Hxb] Hclose.
  assert (Htx : ~ (x * x - 2 == 0)) by (intro Hc; apply (no_rational_sqrt2 x); lra).
  assert (Hcl8 : Qabs (x - x0) < c0 / 8)
    by (apply Qlt_le_trans with (Qmin (c0 / 8) (eps * c0 * c0 / 16)); [ exact Hclose | apply Q.le_min_l ]).
  assert (Hcl16 : Qabs (x - x0) < eps * c0 * c0 / 16)
    by (apply Qlt_le_trans with (Qmin (c0 / 8) (eps * c0 * c0 / 16)); [ exact Hclose | apply Q.le_min_r ]).
  (* division-free closeness facts *)
  assert (Hd8 : 8 * Qabs (x - x0) < c0).
  { apply Qlt_le_trans with (8 * (c0 / 8)).
    - rewrite (Qmult_lt_l (Qabs (x - x0)) (c0 / 8) 8 ltac:(lra)). exact Hcl8.
    - setoid_replace (8 * (c0 / 8)) with c0 by field. apply Qle_refl. }
  assert (Hd16 : 16 * Qabs (x - x0) < eps * c0 * c0).
  { apply Qlt_le_trans with (16 * (eps * c0 * c0 / 16)).
    - rewrite (Qmult_lt_l (Qabs (x - x0)) (eps * c0 * c0 / 16) 16 ltac:(lra)). exact Hcl16.
    - setoid_replace (16 * (eps * c0 * c0 / 16)) with (eps * c0 * c0) by field. apply Qle_refl. }
  assert (Hsum : Qabs (x + x0) <= 4) by (rewrite Qabs_pos by lra; lra).
  assert (Hxx0nn : 0 <= Qabs (x - x0)) by apply Qabs_nonneg.
  assert (Hdiffsq : Qabs (x * x - x0 * x0) <= 4 * Qabs (x - x0)).
  { setoid_replace (x * x - x0 * x0) with ((x - x0) * (x + x0)) by ring.
    rewrite Qabs_Qmult. nra. }
  assert (HAlow : c0 - Qabs (x * x - x0 * x0) <= Qabs (x * x - 2)).
  { pose proof (Qabs_triangle_reverse (x0 * x0 - 2) (x0 * x0 - x * x)) as HT.
    setoid_replace (x0 * x0 - 2 - (x0 * x0 - x * x)) with (x * x - 2) in HT by ring.
    setoid_replace (Qabs (x0 * x0 - x * x)) with (Qabs (x * x - x0 * x0)) in HT
      by (setoid_replace (x0 * x0 - x * x) with (- (x * x - x0 * x0)) by ring; apply Qabs_opp).
    rewrite Hc0eq. exact HT. }
  assert (HAhalf : c0 < 2 * Qabs (x * x - 2)).
  { apply Qmid with (b := Qabs (x * x - x0 * x0)); [ exact HAlow | ].
    apply Qle_lt_trans with (8 * Qabs (x - x0)); [ nra | exact Hd8 ]. }
  assert (HQpos : 0 < Qabs (x * x - 2)) by lra.
  assert (Hcomm : Qabs (x0 * x0 - x * x) == Qabs (x * x - x0 * x0))
    by (setoid_replace (x0 * x0 - x * x) with (- (x * x - x0 * x0)) by ring; apply Qabs_opp).
  assert (Hfeq : Qabs (f x - f x0) ==
                 Qabs (x0 * x0 - x * x) / (Qabs (x * x - 2) * c0)).
  { unfold f.
    setoid_replace (/ (x * x - 2) - / (x0 * x0 - 2))
      with ((x0 * x0 - x * x) / ((x * x - 2) * (x0 * x0 - 2)))
      by (field; split; assumption).
    rewrite Qabs_div_loc, Qabs_Qmult, <- Hc0eq. reflexivity. }
  rewrite Hfeq.
  apply div_lt.
  - apply Qmult_lt_0_compat; [ exact HQpos | exact Hc0 ].
  - rewrite Hcomm.
    assert (Hn : 4 * Qabs (x * x - x0 * x0) < eps * c0 * c0).
    { apply Qle_lt_trans with (16 * Qabs (x - x0)); [ nra | exact Hd16 ]. }
    assert (Hec : 0 < eps * c0) by (apply Qmult_lt_0_compat; assumption).
    pose proof (Qabs_nonneg (x * x - x0 * x0)) as HAnn.
    nra.
Qed.

(* ===================================================================== *)
(*  Part 2: f is NOT uniformly continuous (the √2-pole, via Pell)           *)
(* ===================================================================== *)

(** |f(xₖ)| = qₖ². *)
Lemma f_abs_val : forall n, Qabs (f (sx n)) == inject_Z (qq n * qq n).
Proof.
  intro n. unfold f. rewrite Qabs_inv, sx_abs_eq, Qinv_involutive. reflexivity.
Qed.

(** Consecutive convergents: |xₖ − xₖ₊₁| = 1/(qₖ qₖ₊₁). *)
Lemma sx_consec_abs : forall n, Qabs (sx n - sx (S n)) == / inject_Z (qq n * qq (S n)).
Proof.
  intro n.
  destruct (pell_inv n) as [Hqn _]. destruct (pell_inv (S n)) as [HqSn _].
  assert (Hd1 : ~ inject_Z (qq n) == 0) by (apply injZ_neq0; lia).
  assert (Hd2 : ~ inject_Z (qq (S n)) == 0) by (apply injZ_neq0; lia).
  assert (Hd12 : ~ inject_Z (qq n * qq (S n)) == 0) by (apply injZ_neq0; nia).
  assert (Hpos12 : 0 < inject_Z (qq n * qq (S n))) by (apply injZ_pos; nia).
  assert (Hsub : sx n - sx (S n) ==
                 inject_Z (pp n * qq (S n) - pp (S n) * qq n) / inject_Z (qq n * qq (S n))).
  { unfold sx.
    setoid_replace (inject_Z (pp n) / inject_Z (qq n) - inject_Z (pp (S n)) / inject_Z (qq (S n)))
      with ((inject_Z (pp n) * inject_Z (qq (S n)) - inject_Z (pp (S n)) * inject_Z (qq n))
            / (inject_Z (qq n) * inject_Z (qq (S n))))
      by (field; split; assumption).
    rewrite injZ_sub. repeat rewrite inject_Z_mult. reflexivity. }
  rewrite Hsub.
  destruct (pell_S n) as [HpS HqS].
  assert (Hdet : (pp n * qq (S n) - pp (S n) * qq n = pp n * pp n - 2 * (qq n * qq n))%Z)
    by (rewrite HpS, HqS; ring).
  rewrite Hdet.
  destruct (pell_pm n) as [Hpm | Hpm]; rewrite Hpm.
  - setoid_replace (inject_Z 1) with 1 by reflexivity.
    setoid_replace (1 / inject_Z (qq n * qq (S n))) with (/ inject_Z (qq n * qq (S n)))
      by (field; exact Hd12).
    rewrite Qabs_pos; [ reflexivity | apply Qlt_le_weak; apply Qinv_lt_0_compat; exact Hpos12 ].
  - setoid_replace (inject_Z (-1)) with (-(1)) by reflexivity.
    setoid_replace (-(1) / inject_Z (qq n * qq (S n))) with (- / inject_Z (qq n * qq (S n)))
      by (field; exact Hd12).
    rewrite Qabs_neg.
    + ring.
    + assert (0 < / inject_Z (qq n * qq (S n))) by (apply Qinv_lt_0_compat; exact Hpos12). lra.
Qed.

(** |xₖ − xₖ₊₁| ≤ 1/(k+1). *)
Lemma sx_consec_small : forall n, Qabs (sx n - sx (S n)) <= / inject_Z (Z.of_nat (S n)).
Proof.
  intro n. rewrite sx_consec_abs. apply Qinv_antitone.
  - apply injZ_pos. lia.
  - apply injZ_le. destruct (pell_inv (S n)) as [HqSn _]. pose proof (qq_ge n) as Hqn. nia.
Qed.

Lemma nat_archimedean : forall q : Q, exists n : nat, q < inject_Z (Z.of_nat n).
Proof.
  intro q. destruct (Qarchimedean q) as [p Hp].
  exists (Pos.to_nat p). rewrite positive_nat_Z. exact Hp.
Qed.

Theorem cantor_heine_not_uniform : ~ uniformly_continuous_on f 1 2.
Proof.
  intro H. unfold uniformly_continuous_on in H.
  destruct (H 1 ltac:(lra)) as [delta [Hdelta Hbound]].
  destruct (nat_archimedean (/ delta)) as [m Hm].
  set (n := m).
  assert (HSn_big : / delta < inject_Z (Z.of_nat (S n))).
  { assert (inject_Z (Z.of_nat m) <= inject_Z (Z.of_nat (S n))) by (apply injZ_le; unfold n; lia).
    lra. }
  (* the two points are close *)
  assert (Hsmall : Qabs (sx n - sx (S n)) < delta).
  { apply Qle_lt_trans with (/ inject_Z (Z.of_nat (S n))); [ apply sx_consec_small | ].
    assert (HSkpos : 0 < inject_Z (Z.of_nat (S n))) by (apply injZ_pos; lia).
    assert (Hone : 1 < delta * inject_Z (Z.of_nat (S n))).
    { assert (Hdd : delta * / delta < delta * inject_Z (Z.of_nat (S n)))
        by (rewrite (Qmult_lt_l (/ delta) (inject_Z (Z.of_nat (S n))) delta Hdelta); exact HSn_big).
      setoid_replace (delta * / delta) with 1 in Hdd by (field; lra). exact Hdd. }
    setoid_replace (/ inject_Z (Z.of_nat (S n))) with (1 / inject_Z (Z.of_nat (S n)))
      by (field; apply injZ_neq0; lia).
    apply div_lt; [ exact HSkpos | exact Hone ]. }
  pose proof (sx_range n) as [Hn1 Hn2].
  pose proof (sx_range (S n)) as [HSn1 HSn2].
  pose proof (Hbound (sx n) (sx (S n)) (conj Hn1 Hn2) (conj HSn1 HSn2) Hsmall) as Hlt1.
  (* magnitude gap: |f(sx n) - f(sx(S n))| >= q_{n+1}² - q_n² >= 1 *)
  assert (Hbig : 1 <= Qabs (f (sx n) - f (sx (S n)))).
  { pose proof (Qabs_triangle_reverse (f (sx (S n))) (f (sx n))) as HT.
    rewrite (f_abs_val (S n)) in HT. rewrite (f_abs_val n) in HT.
    assert (Hcomm : Qabs (f (sx n) - f (sx (S n))) == Qabs (f (sx (S n)) - f (sx n)))
      by (setoid_replace (f (sx n) - f (sx (S n))) with (- (f (sx (S n)) - f (sx n))) by ring;
          apply Qabs_opp).
    rewrite Hcomm.
    assert (HZgap : (1 <= qq (S n) * qq (S n) - qq n * qq n)%Z).
    { destruct (pell_inv n) as [Hqn [Hle _]]. destruct (pell_S n) as [_ HqS].
      rewrite HqS. nia. }
    assert (Hgap : 1 <= inject_Z (qq (S n) * qq (S n)) - inject_Z (qq n * qq n)).
    { rewrite <- injZ_sub. change (1 : Q) with (inject_Z 1). apply injZ_le. exact HZgap. }
    set (G := Qabs (f (sx (S n)) - f (sx n))) in *. clearbody G. lra. }
  set (G2 := Qabs (f (sx n) - f (sx (S n)))) in *. clearbody G2. lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — Cantor–Heine fails over ℚ                                   *)
(* ===================================================================== *)

(** F-21 closed: on [1,2]∩ℚ, f(x)=1/(x²−2) is continuous at every point but NOT uniformly continuous — the
    Cantor–Heine theorem genuinely fails over ℚ.  The pole at the absent √2 lets f swing by ≥1 across
    arbitrarily small windows (Pell convergents).  Compactness fails there too (QIntervalNotCompact.v);
    ToS replaces Cantor–Heine with uniformity-as-explicit-rule + the Lipschitz route.  Level: a new
    negative theorem (Cantor–Heine over ℚ refuted with a concrete witness). *)
Theorem cantor_heine_fails_Q :
  continuous_on f 1 2 /\ ~ uniformly_continuous_on f 1 2.
Proof. split; [ exact cantor_heine_continuous | exact cantor_heine_not_uniform ]. Qed.
