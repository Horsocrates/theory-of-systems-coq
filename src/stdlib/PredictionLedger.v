(** * PredictionLedger.v — the comparative ledger: the fit↔derived "binary" is really a GRADED
      SPECTRUM.  Several cluster predictions are audited side by side, ranked by honesty tier, and
      given a posit-ECONOMY (data matched minus posits paid).  Quantitative completion of the
      fit/derived thread (DerivationAudit, JustificationRegress): from "is there a gap?" (binary)
      to "how many posits, of what kind, what economy?" (graded, counted).

      THE FOUR PREDICTIONS.
        series   (Lyman/Balmer = 27/5 etc.) — [Structural; Structural], 4 forced ratios — GOLD;
        isotope  (λ_H/λ_D, λ_H/λ_T)         — [Structural; Indep×3], 2 shifts — derived, no model;
        weinberg (sin²θ_W=3/13 & m_W/m_Z)   — [Structural; Posited; Indep], 2 data — rides on SU(5);
        fit      (a bare constant ≈ p/q)    — [Target], 1 datum — a back-fit.

      RANK (by the worst leaf): Target (gap) → 0; else a Posited model → 1; else an Indep input → 2;
      else only Structural → 3.  Proven: rank series=3 > isotope=2 > weinberg=1 > fit=0 — a strict
      total order.

      ECONOMY (data minus cost; cost = the framework posit (1) + model posits; Indep measurements are
      free, they are independently fixed data, not free knobs): series 4−1 = +3, isotope 2−1 = +1,
      weinberg 2−2 = 0.  So 27/5 predicts more than it posits (+3); the isotope shift breaks even
      favourably (+1, only the framework + independent masses); the GUT prediction breaks even (0 —
      it posits a whole model for 2 numbers).  A bare fit is captured by rank 0.

      NOTHING IS ZERO-POSIT (the honest floor).  Even the gold standard 27/5 rests on ONE posit — the
      framework (the counting/level law) — `series_one_posit = 1`; the Weinberg chain rests on 3
      (framework, SU(5), scale).  The difference is not "posit-free vs posited" but HOW MANY and of
      WHAT KIND.  The floor is 1 (the framework); "zero-posit" is the role-limit (JustificationRegress).

    Elements: the four audits; the rank/economy values; the posit chains (L1 + P4)
    Roles:    each prediction plays a tier (strict/derived/rides/fit) and an economy; the framework
              posit is the irreducible shared floor (the cheapest tier still pays 1)
    Rules:    rank by the worst leaf; economy = data − (framework + model posits); Indep is free

    ============ E/R/R разбор ============
      Rules (L5): ранг по худшему листу (gap>model>indep>structural); экономика = данные−(рамка+модельные
                  постулаты), Indep бесплатны.
      Roles (L4): предсказание играет ярус + экономику; постулат-рамка = неустранимый общий пол (≥1).
      Elements  : четыре аудита; значения ранга/экономики; цепи постулатов.
    ДИАГНОСТИКА (P4): «выведено/подогнано» = градуированный спектр (конечный ранг + Z-экономика, машинно).
    Ничто не ноль-постулатно (27/5 стоит на рамке, пол=1); честное сравнение = экономика постулатов; «ноль» = role-limit.

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia ZArith.
From ToS Require Import stdlib.DerivationAudit.
From ToS Require Import stdlib.JustificationRegress.

(* ===================================================================== *)
(*  The four predictions, audited side by side                            *)
(* ===================================================================== *)

(** 27/5 etc.: only structural leaves (the counting integers n), 4 forced series ratios. *)
Definition series_ledger : Audit := mkAudit (Structural :: Structural :: nil) 4.
(** isotope shift: structural law + 3 independently measured masses, 2 spectroscopic shifts. *)
Definition isotope_ledger : Audit := mkAudit (Structural :: Indep :: Indep :: Indep :: nil) 2.
(** sin²θ_W=3/13 & m_W/m_Z=10/13: structural + the SU(5) posit + the scale, 2 data from one sector. *)
Definition weinberg_ledger : Audit := mkAudit (Structural :: Posited :: Indep :: nil) 2.
(** a bare constant ≈ p/q: one tuned knob, one datum. *)
Definition fit_ledger : Audit := mkAudit (Target :: nil) 1.

(* ===================================================================== *)
(*  RANK: a finite comparator by the worst leaf                            *)
(* ===================================================================== *)

Definition rank (a : Audit) : nat :=
  if (0 <? n_gaps a)%nat then 0
  else if (0 <? n_posited a)%nat then 1
  else if (0 <? n_indep a)%nat then 2
  else 3.

Lemma rank_series : rank series_ledger = 3.
Proof. reflexivity. Qed.

Lemma rank_isotope : rank isotope_ledger = 2.
Proof. reflexivity. Qed.

Lemma rank_weinberg : rank weinberg_ledger = 1.
Proof. reflexivity. Qed.

Lemma rank_fit : rank fit_ledger = 0.
Proof. reflexivity. Qed.

(** ★ The honesty spectrum is a strict total order: fit < weinberg < isotope < series. *)
Lemma ledger_order :
  (rank fit_ledger < rank weinberg_ledger)%nat
  /\ (rank weinberg_ledger < rank isotope_ledger)%nat
  /\ (rank isotope_ledger < rank series_ledger)%nat.
Proof.
  rewrite rank_fit, rank_weinberg, rank_isotope, rank_series.
  split; [ lia | split; lia ].
Qed.

(* ===================================================================== *)
(*  TIERS: the meaning of each rank, via the predicates                    *)
(* ===================================================================== *)

(** Gold (rank 3): only structural counts — first-principles-strict. *)
Lemma series_strict : first_principles_strict series_ledger.
Proof.
  unfold first_principles_strict, series_ledger, n_gaps, n_indep, n_posited. simpl.
  split; [ reflexivity | split; reflexivity ].
Qed.

(** Derived, no model (rank 2): no back-fit, no posit — but uses independent measurements. *)
Lemma isotope_derived : derived isotope_ledger.
Proof. unfold derived, isotope_ledger, n_gaps. reflexivity. Qed.

Lemma isotope_not_strict : ~ first_principles_strict isotope_ledger.
Proof.
  unfold first_principles_strict, isotope_ledger, n_gaps, n_indep, n_posited. simpl.
  intros (_ & H & _). discriminate.
Qed.

Lemma isotope_no_model : ~ rides_on_model isotope_ledger.
Proof. unfold rides_on_model, isotope_ledger, n_posited. simpl. lia. Qed.

(** Rides on a model (rank 1): no back-fit, but imports the SU(5) posit. *)
Lemma weinberg_derived : derived weinberg_ledger.
Proof. unfold derived, weinberg_ledger, n_gaps. reflexivity. Qed.

Lemma weinberg_rides : rides_on_model weinberg_ledger.
Proof. unfold rides_on_model, weinberg_ledger, n_posited. simpl. lia. Qed.

(** Fit (rank 0): a back-fit — not derived. *)
Lemma fit_not_derived : ~ derived fit_ledger.
Proof. unfold derived, fit_ledger, n_gaps. simpl. discriminate. Qed.

(* ===================================================================== *)
(*  ECONOMY: data matched minus posits paid (Indep measurements are free)  *)
(* ===================================================================== *)

(** Cost = the framework posit (1, always paid) + the model posits.  Independent measurements are
    NOT counted — they are independently fixed data, not free knobs. *)
Definition cost (a : Audit) : nat := 1 + n_posited a.

Definition economy (a : Audit) : Z := Z.of_nat (data_points a) - Z.of_nat (cost a).

Lemma series_economy : economy series_ledger = 3%Z.
Proof. reflexivity. Qed.

Lemma isotope_economy : economy isotope_ledger = 1%Z.
Proof. reflexivity. Qed.

Lemma weinberg_economy : economy weinberg_ledger = 0%Z.
Proof. reflexivity. Qed.

(** ★ The economy ranks them: the GUT prediction merely breaks even (posits a model for 2 numbers),
    the isotope shift gains (+1), the series ratios gain most (+3, from one framework posit). *)
Lemma economy_order :
  (economy weinberg_ledger < economy isotope_ledger)%Z
  /\ (economy isotope_ledger < economy series_ledger)%Z.
Proof.
  rewrite series_economy, isotope_economy, weinberg_economy. split; lia.
Qed.

(* ===================================================================== *)
(*  NOTHING IS ZERO-POSIT: even the gold standard rests on the framework   *)
(* ===================================================================== *)

(** The gold standard's justification chain: ONE posit — the framework (the counting/level law). *)
Definition series_just : Just := Posit.

Lemma series_one_posit : n_posits series_just = 1.
Proof. reflexivity. Qed.

(** ★ Even 27/5 is not zero-posit (it rests on the framework, 1); the Weinberg chain rests on 3
    (framework, SU(5), scale — JustificationRegress.deriv_3_13).  The floor is 1; "zero-posit" is a
    role-limit.  The honest difference is the COUNT, not posit-free-vs-posited. *)
Lemma nothing_zero_posit :
  (1 <= n_posits series_just)%nat /\ (1 <= n_posits deriv_3_13)%nat.
Proof.
  split.
  - rewrite series_one_posit. lia.
  - rewrite weinberg_chain_three_posits. lia.
Qed.

(* ===================================================================== *)
(*  Synthesis: the honesty spectrum, graded and counted                    *)
(* ===================================================================== *)

(** The prediction ledger:
      (order) fit < weinberg < isotope < series — a strict honesty rank (`ledger_order`);
      (tiers) series strict, isotope derived-no-model, weinberg derived-rides-on-model, fit a
        back-fit (`series_strict`, `isotope_*`, `weinberg_*`, `fit_not_derived`);
      (economy) weinberg breaks even (0), isotope gains (+1), series gains most (+3)
        (`economy_order`);
      (floor) nothing is zero-posit — even 27/5 rests on the framework (`nothing_zero_posit`).
    The fit↔derived binary is a graded, counted spectrum; the floor is one (the framework);
    "zero-posit" is the role-limit. *)
Theorem prediction_ledger :
  ((rank fit_ledger < rank weinberg_ledger)%nat
   /\ (rank weinberg_ledger < rank isotope_ledger)%nat
   /\ (rank isotope_ledger < rank series_ledger)%nat)
  /\ first_principles_strict series_ledger
  /\ (derived isotope_ledger /\ ~ rides_on_model isotope_ledger)
  /\ (derived weinberg_ledger /\ rides_on_model weinberg_ledger)
  /\ ~ derived fit_ledger
  /\ ((economy weinberg_ledger < economy isotope_ledger)%Z
      /\ (economy isotope_ledger < economy series_ledger)%Z)
  /\ ((1 <= n_posits series_just)%nat /\ (1 <= n_posits deriv_3_13)%nat).
Proof.
  split; [ exact ledger_order | ].
  split; [ exact series_strict | ].
  split; [ split; [ exact isotope_derived | exact isotope_no_model ] | ].
  split; [ split; [ exact weinberg_derived | exact weinberg_rides ] | ].
  split; [ exact fit_not_derived | ].
  split; [ exact economy_order | exact nothing_zero_posit ].
Qed.
