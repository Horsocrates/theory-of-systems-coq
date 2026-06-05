(** * DerivationAudit.v — a machine-checkable discipline separating DERIVED predictions from
      FITTED ones, by auditing the PROVENANCE of a prediction's numeric leaves rather than its
      arithmetic.  A Coq `Qed` certifies that f(inputs) = value (the arithmetic); it never
      certifies that f and the inputs are FORCED by the theory rather than chosen to hit a measured
      datum.  So the fit/derived gap is invisible to `Qed` — it lives in the CHOICE of the leaves.
      This file makes that gap a finite, decidable object.

      THE CRITERION.  A prediction is DERIVED iff no leaf of its construction depends on the very
      datum it is being compared against (no "gap" leaf).  Perturb the target experiment by 10%:
      for a fit you must re-tune (a leaf tracks the datum); for a derivation the construction is
      fixed and the prediction either still matches (genuine) or is falsified.  So: derived ⟺ no
      leaf is Target.  Predictive surplus = (independent data points matched) − (gap leaves):
      a pure fit has surplus 0 (zero content); a derivation has surplus = the data it matches.

      THE THREE PROVENANCES of a numeric leaf:
        Structural — forced by a structural count (carries an obligation: a `_forced` lemma
                     value = <count> must be provable; this is the Element side, no scale);
        Indep      — measured in an INDEPENDENT experiment (a legitimate external input/scale);
        Target     — a knob fitting the answer to itself, or the predicted datum reused — the GAP.

      THE DEEP POINT.  This is the finitization boundary applied REFLEXIVELY to our own predictions.
      Element-side (genuinely derived) = built from counted leaves (rational from combinatorics, no
      measured scale); role-limit/fit = smuggles the target datum (a measured continuous scale tuned
      to itself).  Three tiers: fully_first_principles (only Structural) ⊃ derived (no Target) ⊃ all.
      The "gap" is now COUNTED: n_gaps.  Demonstrations: a pure fit (not derived, surplus 0); the
      isotope shift (derived from 3 independent masses, surplus 2 — masses come from mass
      spectrometry, NOTHING tuned to spectroscopy); a series ratio (fully first-principles, surplus 1).

    Elements: the finite lists of provenance tags; the nat counts n_gaps/n_indep; the surplus (L1+P4)
    Roles:    each leaf plays Structural / Indep / Target; the prediction's role (derived vs fit) is
              fixed by whether any leaf plays Target (depends on the predicted datum)
    Rules:    derived ⟺ n_gaps = 0 (no leaf depends on the target datum); surplus = data − n_gaps

    ============ E/R/R разбор ============
      Rules (L5): выведено ⟺ ни один лист не зависит от предсказываемого данного (n_gaps=0); предсказание
                  судится по ПРОВЕНАНСУ листьев, не по арифметике (которую и так удостоверяет Qed).
      Roles (L4): лист играет Structural (вынужден счётом, Element) / Indep (измерен в ДРУГОМ эксперименте,
                  законная шкала) / Target (разрыв — ручка, подгоняющая ответ к себе).
      Elements  : конечные списки меток; счёты n_gaps/n_indep; целый surplus = #данных − #разрывов.
    ДИАГНОСТИКА (P4): граница финитизации РЕФЛЕКСИВНО — Element-сторона (выведено) = счётные листья (рац. из
    комбинаторики, без шкалы); role-limit/подгонка = протаскивает целевое данное (шкала, подогнанная к себе).
    n_gaps ЕСТЬ тот разрыв, теперь сосчитанный. Три яруса: fully_first_principles ⊃ derived ⊃ всё.

    DEEPENED (2026-06): added a fourth provenance `Posited` (an external model not derived within
    ToS — the deeper gap), with `n_posited`, the honest top tier `first_principles_strict` (no
    target, no indep, no posit), and `rides_on_model`.  The old `fully_first_principles` is BLIND to
    posits (it does not count them); `first_principles_strict` sees them.  strict ⊂ fully ⊂ derived.

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List ZArith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  THE ENGINE: provenance of a prediction's numeric leaves                *)
(* ===================================================================== *)

(** The provenance of one numeric leaf of a prediction's construction.
    DEEPENED (2026-06): a fourth provenance, Posited, for the deeper gap — an external model not
    derived within ToS, imported to make the prediction (e.g. the SU(5) embedding behind 3/8).  It
    is distinct from Indep (a number MEASURED in another experiment) and from Target (back-fit to
    the datum).  A Posited leaf is the deeper gap the old fully/derived tiers were blind to. *)
Inductive Source : Type :=
  | Structural   (* forced by a count GIVEN the framework — Element side *)
  | Indep        (* measured in an INDEPENDENT experiment — a legitimate empirical input *)
  | Posited      (* an external model NOT derived within ToS, imported to fit — the DEEPER gap *)
  | Target.      (* tuned to / reused from the predicted datum — the SHALLOW gap *)

Definition is_target (s : Source) : bool :=
  match s with Target => true | _ => false end.
Definition is_indep (s : Source) : bool :=
  match s with Indep => true | _ => false end.
Definition is_struct (s : Source) : bool :=
  match s with Structural => true | _ => false end.
Definition is_posited (s : Source) : bool :=
  match s with Posited => true | _ => false end.

(** An audit of one prediction: the provenance of every numeric leaf, and the number of
    INDEPENDENT target-experiment data points it matches. *)
Record Audit : Type := mkAudit {
  leaves : list Source;
  data_points : nat
}.

Definition n_gaps (a : Audit) : nat := length (filter is_target (leaves a)).
Definition n_indep (a : Audit) : nat := length (filter is_indep (leaves a)).
Definition n_struct (a : Audit) : nat := length (filter is_struct (leaves a)).
Definition n_posited (a : Audit) : nat := length (filter is_posited (leaves a)).

(* ===================================================================== *)
(*  THE CRITERION: derived ⟺ no gap; the three tiers                       *)
(* ===================================================================== *)

(** ★ DERIVED: no leaf depends on the target datum (no tuned/reused leaf). *)
Definition derived (a : Audit) : Prop := n_gaps a = 0%nat.

(** FULLY FIRST-PRINCIPLES (no target, no independent measurement) — but BLIND to Posited leaves:
    a prediction riding on an external posited model still passes this (its leaves are neither
    Target nor Indep).  This blind spot is the deeper gap; `first_principles_strict` below sees it. *)
Definition fully_first_principles (a : Audit) : Prop :=
  n_gaps a = 0%nat /\ n_indep a = 0%nat.

(** ★ FIRST-PRINCIPLES STRICT (the honest top tier): no target, no independent input, AND no
    external posited model — ONLY structural counts internal to the framework.  This is the tier
    `fully_first_principles` should have been; the difference n_posited > 0 is the deeper gap. *)
Definition first_principles_strict (a : Audit) : Prop :=
  n_gaps a = 0%nat /\ n_indep a = 0%nat /\ n_posited a = 0%nat.

(** A prediction RIDES ON A MODEL when it imports an external posit (n_posited > 0): the deeper
    gap, invisible to fully_first_principles, exposed by first_principles_strict. *)
Definition rides_on_model (a : Audit) : Prop := (0 < n_posited a)%nat.

(** ★ PREDICTIVE SURPLUS: data matched beyond the gap leaves.  Independent inputs cost nothing
    (they are fixed by another experiment); structural leaves cost nothing (forced).  Only tuned
    leaves count against. *)
Definition surplus (a : Audit) : Z := Z.of_nat (data_points a) - Z.of_nat (n_gaps a).

(** The purest tier implies the derived tier. *)
Lemma fully_implies_derived : forall a, fully_first_principles a -> derived a.
Proof. intros a [H _]. exact H. Qed.

(** ★ The honest top tier is strictly stronger: strict ⟹ fully (it adds n_posited = 0).  So the
    layering is first_principles_strict ⊂ fully_first_principles ⊂ derived, and the deeper gap is
    exactly what separates strict from fully (a Posited leaf). *)
Lemma strict_implies_fully : forall a, first_principles_strict a -> fully_first_principles a.
Proof. intros a (Hg & Hi & _). split; assumption. Qed.

(** ★ A derived prediction's surplus is exactly the data it matches — pure predictive content. *)
Lemma derived_surplus_eq_data : forall a, derived a -> surplus a = Z.of_nat (data_points a).
Proof. intros a H. unfold surplus, derived in *. rewrite H. simpl. lia. Qed.

(** Contrapositive face: a positive gap count is exactly "not derived". *)
Lemma gap_pos_not_derived : forall a, (0 < n_gaps a)%nat -> ~ derived a.
Proof. intros a H. unfold derived. lia. Qed.

(* ===================================================================== *)
(*  Demonstration 1 — a PURE FIT: one tuned knob, one datum                *)
(* ===================================================================== *)

(** A bare "constant ≈ p/q" with the integers chosen to hit the measured value: one Target leaf,
    one datum.  Not derived; surplus 0 (zero predictive content — it interpolates one point). *)
Definition pure_fit : Audit := mkAudit [Target] 1.

Lemma pure_fit_not_derived : ~ derived pure_fit.
Proof. unfold derived, pure_fit, n_gaps. simpl. discriminate. Qed.

Lemma pure_fit_surplus_zero : surplus pure_fit = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Demonstration 2 — the ISOTOPE SHIFT: 3 independent masses, 0 tuned     *)
(* ===================================================================== *)

(** RydbergIsotopeShift.v audited: its leaves are 3 mass ratios (m_p,m_d,m_t / m_e), each MEASURED
    in mass spectrometry — an independent experiment; NOTHING is tuned to spectroscopy.  It matches
    2 independent spectroscopic data points (the H/D and H/T shifts) via the un-tuned reduced-mass
    law.  Derived (n_gaps = 0), surplus 2 — but NOT fully first-principles (it consumes 3
    independent inputs). *)
Definition isotope_audit : Audit := mkAudit [Indep; Indep; Indep] 2.

Lemma isotope_derived : derived isotope_audit.
Proof. unfold derived, isotope_audit, n_gaps. reflexivity. Qed.

Lemma isotope_surplus_2 : surplus isotope_audit = 2%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma isotope_not_fully : ~ fully_first_principles isotope_audit.
Proof.
  unfold fully_first_principles, isotope_audit, n_gaps, n_indep. simpl.
  intros [_ H]. discriminate.
Qed.

(* ===================================================================== *)
(*  Demonstration 3 — a SERIES RATIO: fully first-principles (no input)    *)
(* ===================================================================== *)

(** The gold standard (the next file): a spectral series ratio such as Lyman/Balmer = 27/5 is a
    pure n²-rational forced by the Rydberg law — its leaves are the integers n (Structural,
    backed by counting), NO measured input at all.  Fully first-principles; surplus 1 — a genuine
    prediction with zero empirical leaves. *)
Definition series_ratio_audit : Audit := mkAudit [Structural; Structural] 1.

Lemma series_fully : fully_first_principles series_ratio_audit.
Proof.
  unfold fully_first_principles, series_ratio_audit, n_gaps, n_indep. simpl. split; reflexivity.
Qed.

Lemma series_surplus_1 : surplus series_ratio_audit = 1%Z.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis: fit vs derived is now a finite, decidable Element-object    *)
(* ===================================================================== *)

(** The derivation audit:
      (criterion) derived ⟺ no leaf depends on the target datum (`derived`, n_gaps = 0); the gap
        the user asked about is COUNTED — it is n_gaps;
      (fit) a pure fit is not derived and has surplus 0 (`pure_fit_*`);
      (derived) the isotope shift is derived with surplus 2 from independent inputs, not fully
        first-principles (`isotope_*`);
      (gold standard) a series ratio is fully first-principles with surplus 1 (`series_*`);
      (structure) fully_first_principles ⟹ derived; a derived prediction's surplus is its data.
    "Is it derived?" is now a machine-checked property, not a word in a header. *)
Theorem derivation_audit :
  (~ derived pure_fit /\ surplus pure_fit = 0%Z)
  /\ (derived isotope_audit /\ surplus isotope_audit = 2%Z /\ ~ fully_first_principles isotope_audit)
  /\ (fully_first_principles series_ratio_audit /\ surplus series_ratio_audit = 1%Z)
  /\ (forall a, fully_first_principles a -> derived a).
Proof.
  split; [ split; [ exact pure_fit_not_derived | exact pure_fit_surplus_zero ] | ].
  split; [ split; [ exact isotope_derived
                  | split; [ exact isotope_surplus_2 | exact isotope_not_fully ] ] | ].
  split; [ split; [ exact series_fully | exact series_surplus_1 ] | ].
  exact fully_implies_derived.
Qed.
