(** * DerivedVsNumerological.v — sharpening the demarcation (after PhysicsDemarcation.v): WITHIN the
       "parameter-free prediction" bucket, separate a DATA-SELECTED DERIVED prediction from a mere
       NUMEROLOGICAL COINCIDENCE.  H39 counted 2 confirmed predictions (sin²θ_W=3/13, neutrino (5/16)³).
       Surveying the repo: the 3 and the 13 of sin²θ_W come from an independent DOF counting
       (WeinbergAngleDerivation.v / ThetaFromL2L3.v), but 5/16 is NOWHERE derived as a neutrino quantity —
       it appears only unrelatedly (a Dirac eigenvalue in DiracOnGraph.v, a Slater constant in
       LithiumLattice.v, an RG gap).  So (5/16)³ ≈ 0.031 is a number that MATCHES, not a value that is FORCED.

    -- Why an un-forced match carries no information (the deflation) --
      The rationals are DENSE: for ANY target and ANY tolerance there is a rational match — so "some simple
      fraction matches the datum" is GUARANTEED, never evidence.  What discriminates a prediction from
      numerology is whether the SPECIFIC value is data-SELECTED: is it the simplest fraction at that
      precision, or does a far simpler fraction match equally well?
        • neutrino (5/16)³ = 125/4096 (denominator 4096) matches ≈ 0.031 — but so does the FAR simpler 1/32
          (= 0.03125), and 1/32 ≠ 125/4096.  The datum does NOT select (5/16)³.  → numerological.
        • sin²θ_W = 3/13 (= 0.230769) matches 0.23121 within 1/2000 — and the simpler 1/4 and 2/9 BOTH MISS
          that window.  3/13 is the continued-fraction convergent: the datum SELECTS it.  → data-selected,
          and the 3, 13 are independently derived.  → derived prediction.

    -- The honest recount --
      Of H39's 2 confirmed predictions, exactly 1 is a DATA-SELECTED DERIVED prediction (sin²θ_W) and 1 is a
      NUMEROLOGICAL coincidence (neutrino).  So the strict count of genuinely derived parameter-free
      predictions is 1 — matching the strategic conclusion that sin²θ_W is "the one quasi-parameter-free
      candidate" (singular).  ⚠ And even that 1 carries H39's postdiction shadow (r = 3/10 ↦ 3/13): if the
      DOF route is rejected, the floor is 0.  Honest range: AT MOST 1 cleanly derived prediction.

    WHAT THE REPO HAS (surveyed): PhysicsDemarcation.v (H39: prediction/postdiction/reframing, 2 confirmed);
    PredictionHonesty.v (the (5/16)³ number, asserted not derived); ProcessAccuracySummary.v /
    ProcessCouplingAnalysis.v (`(5#16)³ == 125#4096`, no derivation of 5/16); WeinbergAngleDerivation.v /
    ThetaFromL2L3.v (the 3/13 DOF route).  GAP: the derived-vs-numerological sub-distinction, the density
    deflation, and the honest downgrade of the count from 2 to 1.  This adds it, self-contained.

    ============ E/R/R разбор ============
      Elements : цель-датум (31/1000, 23121/100000); конкурирующие дроби (1/32, 1/4, 2/9); значения 3/13, 125/4096.
      Roles    : DerivedPrediction = данные ВЫБИРАЮТ значение + целые независимо выведены; NumerologicalMatch = совпало, но проще дробь тоже.
      Rules    : плотность ℚ ⟹ совпадение-в-допуске ВСЕГДА есть (не улика); дискриминатор = ВЫБРАНО ли данными.
      ДИАГНОСТИКА (P4): нейтрино (5/16)³ НЕ выбрано (1/32 проще и тоже попадает) ⟹ нумерология; sin²θ_W=3/13 ВЫБРАНО
      (1/4, 2/9 мимо; конвергента цепной дроби) + 3,13 выведены ⟹ выводимое предсказание. Честный пересчёт: 1 (не 2);
      с тенью постдикции (r=3/10↦3/13) пол = 0. Уровень: `синтез+наблюдение` (плотность тривиальна; дефляция нумерологии — наблюдение).

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (self-contained: QArith / Lqa / Lia / List)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia List.
Import ListNotations.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  ★ The deflation: density ⟹ a match within tolerance is ALWAYS available *)
(* ===================================================================== *)

(** ★ For ANY target t and ANY tolerance eps > 0 there is a rational q ≠ t inside (t−eps, t+eps).  So "some
    value matches the datum to within eps" is GUARANTEED by the density of ℚ — it is never, by itself,
    evidence for a particular formula.  Only a value the data SELECTS (or that is independently derived)
    discriminates a prediction from numerology. *)
Lemma match_always_available :
  forall (t eps : Q), 0 < eps -> exists q : Q, ~ (q == t) /\ (t - eps) < q /\ q < (t + eps).
Proof.
  intros t eps Heps. exists (t + eps * (1#2)).
  repeat split.
  - intro Hc. lra.
  - lra.
  - lra.
Qed.

(* ===================================================================== *)
(*  ★ Neutrino (5/16)³: NOT data-selected — a far simpler fraction matches *)
(* ===================================================================== *)

(** The asserted value (5/16)³ = 125/4096 (ProcessAccuracySummary.accuracy_structural). *)
Lemma neutrino_value : (5#16)*(5#16)*(5#16) == 125#4096.
Proof. vm_compute. reflexivity. Qed.

(** ★ The neutrino datum ≈ 31/1000 does NOT select (5/16)³: the FAR simpler 1/32 (denominator 32 vs 4096)
    matches the same datum to within 1/500 (≈1.5%), and 1/32 ≠ 125/4096.  A complex fraction matched by a
    simpler one carries no information — the match is numerological, not a forced prediction. *)
Lemma neutrino_match_nonunique :
  ((31#1000) - (1#500) < 125#4096 /\ (125#4096) < (31#1000) + (1#500))   (* (5/16)³ matches *)
  /\ ((31#1000) - (1#500) < 1#32 /\ (1#32) < (31#1000) + (1#500))        (* simpler 1/32 matches too *)
  /\ ~ ((1#32) == 125#4096).                                            (* and they differ *)
Proof.
  repeat split; try lra; unfold Qeq; simpl; lia.
Qed.

(* ===================================================================== *)
(*  ★ sin²θ_W = 3/13: data-SELECTED — the simpler fractions miss          *)
(* ===================================================================== *)

(** ★ The sin²θ_W datum 0.23121 DOES select 3/13: the simpler fractions 1/4 and 2/9 both MISS the 1/2000
    window around 0.23121 (1/4 too big, 2/9 too small), while 3/13 = 0.230769 sits inside it (H39's
    prediction_matches).  3/13 is the continued-fraction convergent — the datum picks it out — and its 3
    and 13 are independently derived (the DOF route).  This is the discriminator from the neutrino case. *)
Lemma sin2_selected :
  (23121#100000) + (1#2000) < (1#4)          (* 1/4 = 0.25 is above the window *)
  /\ (2#9) < (23121#100000) - (1#2000)        (* 2/9 = 0.2222 is below the window *)
  /\ ((23121#100000) - (1#2000) < 3#13 /\ (3#13) < (23121#100000) + (1#2000)).  (* 3/13 is inside *)
Proof.
  repeat split; lra.
Qed.

(* ===================================================================== *)
(*  The honest recount: 1 derived, 1 numerological (not 2 confirmed)       *)
(* ===================================================================== *)

Inductive Evidence := DerivedPrediction | NumerologicalMatch.

(** H39's two "confirmed predictions". *)
Inductive ConfPred := CsinThetaW | Cneutrino.

(** The strict classification: sin²θ_W is data-selected & derived; the neutrino is a numerological match. *)
Definition evidence (c : ConfPred) : Evidence :=
  match c with
  | CsinThetaW => DerivedPrediction    (* selected (1/4, 2/9 miss); 3, 13 derived — with the r-shadow caveat *)
  | Cneutrino  => NumerologicalMatch   (* not selected (1/32 simpler & matches); 5/16 nowhere derived *)
  end.

Definition all_confpred : list ConfPred := [CsinThetaW; Cneutrino].

Definition evidence_eqb (a b : Evidence) : bool :=
  match a, b with
  | DerivedPrediction, DerivedPrediction | NumerologicalMatch, NumerologicalMatch => true
  | _, _ => false
  end.

Definition count_evidence (e : Evidence) : nat :=
  length (filter (fun c => evidence_eqb (evidence c) e) all_confpred).

(** ★★ The honest recount: exactly ONE data-selected derived prediction (sin²θ_W) — not the 2 a casual
    read of "confirmed predictions" suggests.  The neutrino is reclassified as a numerological coincidence. *)
Lemma n_derived : count_evidence DerivedPrediction = 1%nat.
Proof. reflexivity. Qed.

Lemma n_numerological : count_evidence NumerologicalMatch = 1%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Derived prediction vs numerological coincidence:
      (deflation)   density of ℚ ⟹ a match within ANY tolerance is always available — never, alone, evidence;
      (neutrino)    (5/16)³ = 125/4096 is matched by the FAR simpler 1/32 (distinct) — NOT data-selected;
      (sin²θ_W)     0.23121 selects 3/13 — the simpler 1/4, 2/9 miss the 1/2000 window — and 3, 13 are derived;
      (recount)     of H39's 2 confirmed predictions, 1 is a data-selected DERIVED prediction, 1 is numerology.
    So the strict count of genuinely derived parameter-free predictions is 1 (sin²θ_W) — "the one quasi-
    parameter-free candidate".  ⚠ Honest floor: even that 1 carries H39's postdiction shadow (r = 3/10 ↦
    3/13); reject the DOF route and the count is 0.  Level: synthesis + observation — the density deflation
    is trivial, the discriminator (a simpler fraction matches ⟹ numerology) is the honest observation. *)
Theorem derived_vs_numerological :
  (forall (t eps : Q), 0 < eps -> exists q : Q, ~ (q == t) /\ (t - eps) < q /\ q < (t + eps))
  /\ (5#16)*(5#16)*(5#16) == 125#4096
  /\ (((31#1000) - (1#500) < 1#32 /\ (1#32) < (31#1000) + (1#500)) /\ ~ ((1#32) == 125#4096))
  /\ ((23121#100000) + (1#2000) < (1#4) /\ (2#9) < (23121#100000) - (1#2000))
  /\ count_evidence DerivedPrediction = 1%nat
  /\ count_evidence NumerologicalMatch = 1%nat.
Proof.
  split; [ exact match_always_available | ].
  split; [ exact neutrino_value | ].
  split; [ destruct neutrino_match_nonunique as [_ [H1 H2]]; exact (conj H1 H2) | ].
  split; [ destruct sin2_selected as [H1 [H2 _]]; exact (conj H1 H2) | ].
  split; [ exact n_derived | ].
  exact n_numerological.
Qed.
