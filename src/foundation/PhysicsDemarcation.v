(** * PhysicsDemarcation.v — the Popperian DEMARCATION axis for ToS's physics claims: separating a genuine
       PARAMETER-FREE FALSIFIABLE PREDICTION from a POSTDICTION (a tuned parameter) and a REFRAMING (a known
       result re-derived in ToS notation, which CANNOT be wrong).  Two audit axes already exist in the repo —
       PredictionHonesty.v ({Success|Failure|Open}, the ACCURACY axis) and ProcessDerivedVsConsistent.v
       ({Forced|Natural|Chosen}, the LOGICAL-DEPENDENCE axis).  Neither draws Popper's line: a "success" can
       be a reframing (true by construction, no empirical content) and a "derivation" can be a postdiction
       (a parameter tuned to the answer).  This adds the missing EPISTEMIC-CONTENT axis, with teeth.

    -- The three statuses, each with a machine-checked discriminator --
      PREDICTION  (parameter-free, falsifiable, SYNTHETIC): a fixed value the theory could NOT tune, that
                  agrees with data within tolerance — and the predicted value is symbolically DIFFERENT from
                  the measured value (≠ as rationals) yet numerically CLOSE.  Teeth: 3/13 is sharp (≠ 1/4,
                  ≠ 1/5), is SYNTHETIC (3/13 ≠ 23121/100000 — predicted ≠ measured, not an identity), and
                  MATCHES (|3/13 − 0.23121| < 1/2000, ≈ 0.19% relative).
      POSTDICTION (a tuned parameter): a value f(p) where p was chosen to fit.  Teeth: the ratio model
                  r ↦ r/(1+r) FITS ANY target s ≠ 1 (for every s there is an r) — so until r is independently
                  fixed it predicts NOTHING.  And r = 3/10 reproduces the SAME 3/13 — the flagship value has
                  a postdiction SHADOW; it is a prediction ONLY via the forced DOF route, not via tuned r.
      REFRAMING   (a known result re-derived): the predicted value IS the observable by definition, so the
                  claim has the form v == v — ANALYTIC, provable, no potential falsifier (it cannot be wrong).
                  Teeth: the SHO ladder gap == 2n+1 is a theorem for ALL n (definitional) — unfalsifiable.

    -- The honest count (grounded in the repo's actual claims) --
      Of 10 headline physics claims: 4 are genuine falsifiable PREDICTIONS (sin²θ_W=3/13, neutrino (5/16)³,
      m_e/m_μ, m_μ/m_τ), 3 are POSTDICTIONS (Weinberg via chosen r, mass gap via chosen SU(2)/β, Higgs tree),
      3 are REFRAMINGS (SHO 2n+1, periodic table 2n², Lyman/Balmer 27/5).  Of the 4 predictions, exactly 2 are
      CONFIRMED (sin²θ_W, neutrino) and 2 are FALSIFIED (the charged-lepton ratios) — and ONLY a genuine
      prediction CAN be falsified, which is precisely what the reframings cannot do.  So the honest tally of
      confirmed parameter-free predictions is 2, not "many successes": the demarcation strips the reframings
      and postdictions out of the success column.

    WHAT THE REPO HAS (surveyed): PredictionHonesty.v (accuracy: 3 succ / 3 fail / 1 open);
    ProcessDerivedVsConsistent.v (dependence: 4 forced / 5 natural / 3 chosen); WeinbergAngleDerivation /
    ThetaFromL2L3 (the 3/13 DOF route); ProcessWeinbergAngle (the r-ratio route).  No Popperian demarcation.
    GAP: the falsifiability axis + the discriminating teeth (postdiction fits anything; reframing is v==v;
    prediction is sharp, synthetic, matches).  This adds it, self-contained (QArith only).

    ============ E/R/R разбор ============
      Elements : значение-предсказание (рациональное 3/13); параметр постдикции r; тождество переформулировки v==v.
      Roles    : Prediction = без параметра + фальсифицируемо + синтетично; Postdiction = подогнанный r; Reframing = аналитично.
      Rules    : постдикция r/(1+r) ловит ЛЮБОЕ s≠1 (нефальсифицируемо до фикс. r); переформулировка = v==v (не может быть ложной);
                 предсказание sharp+синтетично (3/13 ≠ 0.23121 символьно, но |Δ|<1/2000) — может НЕ совпасть, но совпало.
      ДИАГНОСТИКА (P4): синтетическое предсказание = «Element-подобно» (определённый свидетель 3/13, КОТОРЫЙ мог не совпасть —
      пересекает границу к данным); переформулировка = аналитична (истинна по построению, границу не пересекает). Демаркация =
      та же финитизационная граница: выводимое-из-данных против истинного-по-определению. Тень постдикции (r=3/10 ↦ 3/13)
      показывает: 3/13 — предсказание ТОЛЬКО если DOF-маршрут (3 и 13) принудителен; иначе подгонка. Честный счёт: 2 подтв.
      Уровень: `синтез+наблюдение` (критерий Поппера + аналитич/синтетич, применённые к claim'ам репозитория, с машинными зубами).

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (self-contained: QArith / Lqa / Lia / List)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia List.
Import ListNotations.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The epistemic-content statuses and the claim ledger                    *)
(* ===================================================================== *)

(** Popper's axis: what KIND of claim, epistemically. *)
Inductive EpiStatus := Prediction | Postdiction | Reframing.

(** The actual headline physics claims of the repo. *)
Inductive Claim :=
  | CsinTheta            (* sin²θ_W = 3/13                — parameter-free, CONFIRMED *)
  | Cneutrino            (* neutrino mass ratio (5/16)³   — parameter-free, CONFIRMED *)
  | CeMu                 (* m_e/m_μ = (1/3)²              — parameter-free, FALSIFIED *)
  | CmuTau               (* m_μ/m_τ = 1/3                 — parameter-free, FALSIFIED *)
  | CweinbergR           (* sin²θ via r = g'²/g² = 3/10   — tuned parameter r *)
  | CmassGap             (* YM mass gap via SU(2), β=1    — chosen Role structure *)
  | ChiggsTree           (* Higgs tree mass              — input-driven *)
  | Csho                 (* SHO ladder E_n/E_0 = 2n+1     — known QM, re-derived *)
  | Cperiodic            (* periodic table 2,8,18,32 = 2n² — known counting *)
  | Clyman.              (* Lyman/Balmer = 27/5           — known Rydberg ratio *)

(** The demarcation map: each claim's epistemic status. *)
Definition status (c : Claim) : EpiStatus :=
  match c with
  | CsinTheta | Cneutrino | CeMu | CmuTau => Prediction   (* parameter-free, falsifiable *)
  | CweinbergR | CmassGap | ChiggsTree    => Postdiction  (* a tuned / chosen input *)
  | Csho | Cperiodic | Clyman             => Reframing    (* known result re-expressed *)
  end.

(** Among the predictions, which actually matched the data (the other two were falsified). *)
Definition matched (c : Claim) : bool :=
  match c with CsinTheta | Cneutrino => true | _ => false end.

Definition all_claims : list Claim :=
  [CsinTheta; Cneutrino; CeMu; CmuTau; CweinbergR; CmassGap; ChiggsTree; Csho; Cperiodic; Clyman].

(* ===================================================================== *)
(*  ★ PREDICTION teeth: sin²θ_W = 3/13 is sharp, synthetic, and matches    *)
(* ===================================================================== *)

(** ★ SHARP: the prediction picks out a SPECIFIC value — it is not the "natural round" 1/4 or 1/5.
    A genuine prediction EXCLUDES alternatives; that exclusion is its empirical content. *)
Lemma prediction_sharp : ~ (3#13 == 1#4) /\ ~ (3#13 == 1#5).
Proof. split; unfold Qeq; simpl; lia. Qed.

(** ★ SYNTHETIC (could-have-failed): the predicted value 3/13 and the MEASURED value 0.23121 are DIFFERENT
    rationals — the claim is NOT an identity v == v.  This is exactly what makes it falsifiable: a synthetic
    agreement, not a definition.  (Contrast the reframing teeth below, which ARE v == v.) *)
Lemma prediction_synthetic : ~ (3#13 == 23121#100000).
Proof. unfold Qeq; simpl; lia. Qed.

(** ★ MATCHES: yet the two agree to within 1/2000 absolute (≈ 0.19% relative, 573/300000) — the synthetic
    coincidence that confirms the prediction.  Two-sided bound (no Qabs). *)
Lemma prediction_matches :
  (3#13) < (23121#100000) /\ (23121#100000) < (3#13) + (1#2000).
Proof. split; lra. Qed.

(* ===================================================================== *)
(*  ★ POSTDICTION teeth: the ratio model fits ANY target — no content      *)
(* ===================================================================== *)

(** ★ FITS ANYTHING: the Weinberg ratio model sin²θ = r/(1+r) — in cleared form r·(1−s) = s — has, for EVERY
    target s ≠ 1, a fitting parameter r.  So before r is independently fixed it predicts NOTHING: it is
    unfalsifiable.  (Division-free proof: r := s·/(1−s) and Qmult_inv_r.) *)
Lemma postdiction_fits_anything :
  forall s : Q, ~ (s == 1) -> exists r : Q, r * (1 - s) == s.
Proof.
  intros s Hs. exists (s * / (1 - s)).
  assert (Hne : ~ (1 - s == 0)) by (intro Hc; apply Hs; lra).
  rewrite <- Qmult_assoc.
  rewrite (Qmult_comm (/ (1 - s)) (1 - s)).
  rewrite (Qmult_inv_r (1 - s) Hne).
  ring.
Qed.

(** ★ THE SHADOW: the SAME flagship value 3/13 is reproduced by the tuned parameter r = 3/10 — i.e.
    (3/10)/(1 + 3/10) = 3/13.  So sin²θ_W = 3/13 is a genuine PREDICTION only via the forced DOF route
    (the 3 and the 13 fixed by the distinction structure); reached via a tuned r it is a POSTDICTION.
    The demarcation is real, not academic: one number, two epistemic routes. *)
Lemma postdiction_shadow : (3#10) / (1 + (3#10)) == 3#13.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  ★ REFRAMING teeth: the SHO ladder is ANALYTIC — it cannot be wrong     *)
(* ===================================================================== *)

(** The harmonic-oscillator ladder gap, AS DEFINED in the ToS model. *)
Definition sho_gap (n : Q) : Q := 2*n + 1.

(** ★ ANALYTIC: the "prediction" E_n/E_0 = 2n+1 is the gap BY DEFINITION — the claim is v == v, provable for
    ALL n.  A statement that cannot be false has no potential falsifier: it re-expresses known QM, it does not
    predict.  This is the discriminator from a genuine prediction (which is synthetic: predicted ≠ measured). *)
Lemma reframing_analytic : forall n : Q, sho_gap n == 2*n + 1.
Proof. intro n. unfold sho_gap. reflexivity. Qed.

(** ★ ...and concretely the ground gap is 1 and the first gap is 3 (2·0+1, 2·1+1) — the ladder is fixed
    by the formula, nothing is measured against it. *)
Lemma reframing_concrete : sho_gap 0 == 1 /\ sho_gap 1 == 3.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  The honest count: strip reframings and postdictions out of "successes" *)
(* ===================================================================== *)

Definition status_eqb (a b : EpiStatus) : bool :=
  match a, b with
  | Prediction, Prediction | Postdiction, Postdiction | Reframing, Reframing => true
  | _, _ => false
  end.

Definition count_status (s : EpiStatus) : nat :=
  length (filter (fun c => status_eqb (status c) s) all_claims).

(** ★ FOUR genuine falsifiable predictions (sin²θ_W, neutrino, and the two charged-lepton ratios). *)
Lemma n_prediction : count_status Prediction = 4%nat.
Proof. reflexivity. Qed.

(** ★ THREE postdictions (Weinberg via tuned r, mass gap via chosen SU(2)/β, Higgs tree input). *)
Lemma n_postdiction : count_status Postdiction = 3%nat.
Proof. reflexivity. Qed.

(** ★ THREE reframings (SHO 2n+1, periodic table 2n², Lyman/Balmer 27/5) — known results, no new content. *)
Lemma n_reframing : count_status Reframing = 3%nat.
Proof. reflexivity. Qed.

Definition confirmed_predictions : nat :=
  length (filter (fun c => andb (status_eqb (status c) Prediction) (matched c)) all_claims).

(** ★★ The punchline: exactly TWO confirmed parameter-free predictions (sin²θ_W, neutrino) — NOT the dozen
    "successes" a casual read suggests.  The reframings (analytic, can't be wrong) and the postdictions
    (tuned, fit anything) are removed from the success column; of the 4 genuine predictions, 2 matched and
    2 were falsified — and only genuine predictions CAN be falsified. *)
Lemma n_confirmed : confirmed_predictions = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The Popperian demarcation of ToS's physics claims:
      (prediction)  sin²θ_W = 3/13 is SHARP (≠ 1/4, 1/5), SYNTHETIC (≠ the measured 0.23121, not an
                    identity), and MATCHES (within 1/2000, ≈ 0.19%) — a parameter-free falsifiable claim;
      (postdiction) the ratio model r/(1+r) fits ANY target s ≠ 1 — unfalsifiable until r is fixed — and
                    r = 3/10 reproduces the very same 3/13 (the flagship has a postdiction shadow);
      (reframing)   the SHO ladder gap == 2n+1 is ANALYTIC (v == v, provable ∀n) — it cannot be wrong;
      (count)       of 10 claims: 4 predictions, 3 postdictions, 3 reframings; only 2 predictions confirmed.
    So the honest demarcation strips reframings (can't be wrong) and postdictions (fit anything) out of the
    success column, leaving TWO confirmed parameter-free predictions.  Level: synthesis + observation —
    Popper's falsifiability and the analytic/synthetic distinction, applied to the repo's own claims with
    machine-checked discriminators.  Honest: this classifies; it proves no new physics. *)
Theorem physics_demarcation :
  (* PREDICTION is sharp, synthetic, and matches *)
  (~ (3#13 == 1#4) /\ ~ (3#13 == 1#5))
  /\ ~ (3#13 == 23121#100000)
  /\ ((3#13) < (23121#100000) /\ (23121#100000) < (3#13) + (1#2000))
  (* POSTDICTION fits anything, and shadows the flagship value *)
  /\ (forall s : Q, ~ (s == 1) -> exists r : Q, r * (1 - s) == s)
  /\ (3#10) / (1 + (3#10)) == 3#13
  (* REFRAMING is analytic — cannot be wrong *)
  /\ (forall n : Q, sho_gap n == 2*n + 1)
  (* the honest count *)
  /\ count_status Prediction = 4%nat
  /\ count_status Postdiction = 3%nat
  /\ count_status Reframing = 3%nat
  /\ confirmed_predictions = 2%nat.
Proof.
  split; [ exact prediction_sharp | ].
  split; [ exact prediction_synthetic | ].
  split; [ exact prediction_matches | ].
  split; [ exact postdiction_fits_anything | ].
  split; [ exact postdiction_shadow | ].
  split; [ exact reframing_analytic | ].
  split; [ exact n_prediction | ].
  split; [ exact n_postdiction | ].
  split; [ exact n_reframing | ].
  exact n_confirmed.
Qed.
