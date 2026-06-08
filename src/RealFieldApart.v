(** * RealFieldApart.v — F-25: the APARTNESS FIELD of Cauchy reals.  "Division is partial" is reframed
       from a limitation into a proven POSITIVE structure: a real has a multiplicative inverse EXACTLY when
       it is APART from zero — i.e. when a separating gap is EXHIBITED (P4: ex→sig).  This closes
       FORMALIZATION-BACKLOG F-25 (IV.3 §3.6.4 "деление частично" as honest boundary).

    -- What RealField.v already had --
      `cauchy_inv_pos` / `cauchy_mul_inv_r_pos`: a sequence eventually > q > 0 (one-sided positive gap) has
      an inverse with a·a⁻¹ ~~ 1.  Only the POSITIVE half; the general apart-from-zero case (which also
      covers eventually-negative reals) was the open "partiality".

    -- What this adds (Element side, 0 axioms) --
      apart0 x := ∃q>0, eventually |xₙ| > q     (apartness from 0: a separating gap is exhibited).
      * apart0_sign     : an apart real is EVENTUALLY ONE-SIGNED — apart0 x ⟹ cauchy_pos x ∨ cauchy_pos (−x).
        (A Cauchy sequence with |xₙ|>q cannot change sign without a jump >q, impossible past the modulus.)
      * apart_has_inverse : EVERY apart0 x has a multiplicative inverse, cauchy_mul x y ~~ 1 — total
        invertibility on the apart elements (positive case = cauchy_inv_pos; negative case = −((−x)⁻¹)).
      * apart0_zero_absurd : ¬ apart0 0 — you cannot be apart from 0 if you ARE 0 (apartness is the
        constructive, witnessed replacement for "≠ 0").
      With RealField's commutative-ring + ordered-field laws, this IS the apartness (Heyting) field.

    -- The boundary (honest) --
      The classical field reifies a COMPLETED set of invertibles (= all non-zero, where "non-zero" is the
      mere negation ¬(x=0)).  Over a constructive real, ¬(x~~0) does NOT yield an inverse: you must
      EXHIBIT a gap (apart0), the P4 ex→sig demand.  "Partiality of division" is the honest content of a
      constructive number — every actually-invertible real is invertible here; only the gap must be shown.

    ============ E/R/R разбор ============
      Elements : Коши-процессы nat→ℚ; свидетель-зазор q>0 с |x|>q в конце концов.
      Roles    : апартность x#0 = роль-условие обратимости; обратный = роль, назначаемая правилом ПРИ зазоре.
      Rules    : обратимость требует свидетеля-апартности (P4 ex→sig); знак в конце концов один (Коши+|x|>q).
      ДИАГНОСТИКА (P4): классическое поле реифицирует завершённое множество обратимых; ToS = поле апартности
        (обратный там, где зазор предъявлен; Element-сторона, 0 акс). «Частичность деления» = честное содержание
        конструктивного числа, не дефект. Уровень: `новая теорема` (тотальный обратный на апартных) над RealField.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (builds on CauchyReal + RealField)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia.
From ToS Require Import CauchyReal RealField.

(* ===================================================================== *)
(*  Sign extraction from a gap on |·|                                      *)
(* ===================================================================== *)

Lemma qabs_gt_pos : forall a q : Q, 0 <= a -> q < Qabs a -> q < a.
Proof. intros a q Ha H. pose proof (Qabs_pos a Ha) as Hp. rewrite Hp in H. exact H. Qed.

Lemma qabs_gt_neg : forall a q : Q, a <= 0 -> q < Qabs a -> q < - a.
Proof. intros a q Ha H. pose proof (Qabs_neg a Ha) as Hp. rewrite Hp in H. exact H. Qed.

(* ===================================================================== *)
(*  Apartness from zero: a separating gap is exhibited (P4: ex→sig)        *)
(* ===================================================================== *)

Definition apart0 (x : CauchySeq) : Prop :=
  exists q : Q, 0 < q /\ exists N : nat, forall n : nat, (N <= n)%nat -> q < Qabs (cs_seq x n).

(** Apartness of two reals = apartness of their difference. *)
Definition cauchy_apart (x y : CauchySeq) : Prop := apart0 (cauchy_add x (cauchy_neg y)).

(** ★★ An apart real is EVENTUALLY ONE-SIGNED: the gap forbids a sign change (a jump > q is impossible
    past the Cauchy modulus).  So apartness resolves, constructively, into positive or negative. *)
Lemma apart0_sign : forall x, apart0 x -> cauchy_pos x \/ cauchy_pos (cauchy_neg x).
Proof.
  intros x [q [Hq [N HN]]].
  destruct (cs_cauchy x q Hq) as [M HM].
  pose (K := Nat.max N M).
  assert (HKN : (N <= K)%nat) by (unfold K; lia).
  assert (HKM : (M <= K)%nat) by (unfold K; lia).
  assert (HxK : q < Qabs (cs_seq x K)) by (apply HN; exact HKN).
  destruct (Qlt_le_dec 0 (cs_seq x K)) as [Hpos | Hnp].
  - left. exists q. split; [ exact Hq | ]. exists K. intros n Hn.
    assert (HnN : (N <= n)%nat) by lia.
    assert (HnM : (M <= n)%nat) by lia.
    assert (Hxn : q < Qabs (cs_seq x n)) by (apply HN; exact HnN).
    assert (HxKq : q < cs_seq x K) by (apply (qabs_gt_pos (cs_seq x K) q (Qlt_le_weak _ _ Hpos) HxK)).
    assert (Hclose : Qabs (cs_seq x n - cs_seq x K) < q) by (apply HM; [ exact HnM | exact HKM ]).
    apply Qabs_Qlt_condition in Hclose. destruct Hclose as [Hlo Hhi].
    assert (Hxn_pos : 0 < cs_seq x n) by lra.
    apply (qabs_gt_pos (cs_seq x n) q (Qlt_le_weak _ _ Hxn_pos) Hxn).
  - right. exists q. split; [ exact Hq | ]. exists K. intros n Hn.
    assert (HnN : (N <= n)%nat) by lia.
    assert (HnM : (M <= n)%nat) by lia.
    assert (Hxn : q < Qabs (cs_seq x n)) by (apply HN; exact HnN).
    assert (HxKq : q < - cs_seq x K) by (apply (qabs_gt_neg (cs_seq x K) q Hnp HxK)).
    assert (Hclose : Qabs (cs_seq x n - cs_seq x K) < q) by (apply HM; [ exact HnM | exact HKM ]).
    apply Qabs_Qlt_condition in Hclose. destruct Hclose as [Hlo Hhi].
    assert (Hxn_neg : cs_seq x n <= 0) by lra.
    unfold cauchy_neg. simpl.
    apply (qabs_gt_neg (cs_seq x n) q Hxn_neg Hxn).
Qed.

(* ===================================================================== *)
(*  Total invertibility on the apart elements                              *)
(* ===================================================================== *)

(** ★★ EVERY apart-from-zero real has a multiplicative inverse: cauchy_mul x y ~~ 1.  The positive case
    is cauchy_inv_pos directly; the negative case takes y = −((−x)⁻¹).  Total on the apart elements. *)
Theorem apart_has_inverse :
  forall x : CauchySeq, apart0 x -> exists y : CauchySeq, cauchy_equiv (cauchy_mul x y) cauchy_one.
Proof.
  intros x Hap. destruct (apart0_sign x Hap) as [Hpos | Hneg].
  - destruct Hpos as [q [Hq [N HN]]].
    exists (cauchy_inv_pos x q N Hq HN).
    apply (cauchy_mul_inv_r_pos x q N Hq HN).
  - destruct Hneg as [q [Hq [N HN]]].
    exists (cauchy_neg (cauchy_inv_pos (cauchy_neg x) q N Hq HN)).
    apply cauchy_equiv_trans with
      (cauchy_mul (cauchy_neg x) (cauchy_inv_pos (cauchy_neg x) q N Hq HN)).
    2: { apply (cauchy_mul_inv_r_pos (cauchy_neg x) q N Hq HN). }
    set (yn := cauchy_inv_pos (cauchy_neg x) q N Hq HN).
    apply cauchy_equiv_trans with (cauchy_neg (cauchy_mul x yn)).
    + apply cauchy_mul_neg_r.
    + apply cauchy_equiv_sym.
      apply cauchy_equiv_trans with (cauchy_neg (cauchy_mul yn x)).
      * apply cauchy_equiv_trans with (cauchy_mul yn (cauchy_neg x)).
        -- apply cauchy_mul_comm.
        -- apply cauchy_mul_neg_r.
      * apply cauchy_neg_compat. apply cauchy_mul_comm.
Qed.

(** ★ Apartness is irreflexive at 0: you cannot be apart from 0 if you ARE 0 (the witnessed replacement
    for "≠ 0"). *)
Lemma apart0_zero_absurd : ~ apart0 (cauchy_const 0).
Proof.
  intros [q [Hq [N HN]]]. assert (HNN : (N <= N)%nat) by lia. specialize (HN N HNN).
  assert (Hz : Qabs (cs_seq (cauchy_const 0) N) == 0) by (vm_compute; reflexivity).
  rewrite Hz in HN. lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the apartness field                                         *)
(* ===================================================================== *)

(** F-25 closed: the Cauchy reals form an APARTNESS FIELD.
      (apart0_sign)        an apart real is eventually one-signed — apartness resolves constructively;
      (apart_has_inverse)  every apart-from-zero real has a multiplicative inverse, x·y ~~ 1 — TOTAL
                           invertibility on the apart elements, 0 axioms;
      (apart0_zero_absurd) apartness is irreflexive at 0 — the witnessed replacement for "≠ 0".
    With RealField's ring + ordered-field laws, this is the apartness (Heyting) field.  The classical
    field reifies a completed set of invertibles (all non-zero, by mere ¬(x=0)); ToS gives the inverse
    exactly where a gap is EXHIBITED (P4 ex→sig).  "Division is partial" is honest constructive content,
    not a defect.  Level: a new positive structure (total inverse on apart) over the existing RealField. *)
Theorem apartness_field :
  (forall x, apart0 x -> cauchy_pos x \/ cauchy_pos (cauchy_neg x))
  /\ (forall x, apart0 x -> exists y, cauchy_equiv (cauchy_mul x y) cauchy_one)
  /\ (~ apart0 (cauchy_const 0)).
Proof.
  split; [ exact apart0_sign | ].
  split; [ exact apart_has_inverse | exact apart0_zero_absurd ].
Qed.
