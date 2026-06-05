(** * WeinbergGapClosing.v — CLOSING the gap located in WeinbergAudit.v: the fitted input r=3/10
      is replaced by a COUNTED structural seed (the SU(5) value sin²θ_W = 3/8, a charge count) run
      down to low energy by an INDEPENDENT scale.  sin²θ_W = 3/13 thereby moves from a back-fit
      (Target leaf) to a derived prediction (Structural seed + Indep scale), the same honest tier
      as the isotope shift.

      THE GAP (from WeinbergAudit.v).  sin²θ_W = 3/13 was produced from r := 3/10, a coupling ratio
      back-fitted to the MEASURED value — a Target leaf, surplus 0, not derived.

      THE CLOSURE.  process/ProcessRGWeinberg.v already runs sin²θ_W from the GUT value 3/8 down to
      3/13 (starting r(GUT)=3/5).  But there 3/8 is ASSERTED ("SU(5): 3/8", gut_u_y := 3/5 set).
      Here we PROVE 3/8 is a CHARGE COUNT over the SU(5) fundamental 5̄ = (d^c×3, lepton doublet):
          sin²θ_W(GUT) = Tr(T₃²) / Tr(Q²) = (1/2) / (4/3) = 3/8,
      where Tr(T₃²) = (1/2)² + (1/2)² = 1/2  (the two states of the lepton doublet, T₃ = ±1/2)
        and Tr(Q²)  = 3·(1/3)² + 1²        = 4/3 (three down-type antiquarks charge 1/3, the
                                                   charged lepton charge 1, neutrino 0).
      So 3 and 8 are SUMS OF SQUARED CHARGES — counts, not chosen.  The repo's r(GUT)=3/5 is forced
      by this (3/8 = r/(1+r) ⟹ r = 3/5).  Running 3/8 down needs only the β-coefficients (counts
      from particle content) and the scale ratio M_GUT/m_Z (an INDEPENDENT measurement, NOT sin²θ_W
      itself).  No leaf is back-fitted from the target.

      THE UPGRADE (audited).  The GUT seed 3/8 is fully-first-principles (a pure charge count, zero
      empirical input).  The low-energy 3/13 is derived (Structural seed + one Indep scale, no
      Target) — gap CLOSED: Target → Structural+Indep, the isotope-shift tier.

      HONEST RESIDUAL.  (1) SU(5) unification is a discrete model hypothesis (like "electrons fill
      hydrogenic levels" for 2n²) — a structural choice with no continuous knob, but a choice.
      (2) The exact continuum running involves ln(M_GUT/m_Z), a role-limit (transcendental over ℚ),
      so the precise low-energy value is approximate (the repo approximates it by discrete RG steps).
      (3) Content-dependent: SM-SU(5) running gives ≈0.21, MSSM ≈0.231 — the match needs the right
      content/scale.  So this closes the gap to the DERIVED tier, not to fully-first-principles.

    Elements: the squared-charge sums Tr(T₃²), Tr(Q²); the counted ratio 3/8; the forced r=3/5 (L1+P4)
    Roles:    the GUT value 3/8 = a charge count (fully first-principles); the low-energy value =
              its RG-descendant via an independent scale (derived); the scale = the one Indep input
    Rules:    sin²θ_W(GUT) = Tr(T₃²)/Tr(Q²) over the SU(5) 5̄ (a count); running needs counted β's +
              an independent scale, not a back-fit

    ============ E/R/R разбор ============
      Rules (L5): разрыв закрыт заменой подогнанного r=3/10 на счётное GUT-значение 3/8=Tr(T₃²)/Tr(Q²)
                  (заряды по 5̄ SU(5)) + RG-прогон счётными β + независимым масштабом.
      Roles (L4): 3/8 = зарядовый счёт (fully_first_principles, ноль входов); 3/13 = его RG-потомок через
                  ОДИН независимый масштаб (derived, нет Target).
      Elements  : суммы квадратов зарядов Tr(T₃²)=1/2, Tr(Q²)=4/3; счётное 3/8; форсированное r=3/5.
    ДИАГНОСТИКА (P4): разрыв был не в структурном значении (3/8 — полностью счётное SU(5)-предсказание), а в
    СПУСКЕ к низкой энергии, законно требующем ОДНОГО независимого входа (масштаб) — как изотоп-сдвигу массы.
    Закрыт: Target (r=3/10 из себя) → Structural+Indep (счётное 3/8, прогнанное независимым масштабом).

    DEEPENED (2026-06, honest correction).  My first tag called 3/8 fully_first_principles — too
    generous: it hid the SU(5) embedding (an external model NOT derived within ToS) behind the charge
    count.  Re-tagged: 3/8's leaves are [Structural; Posited] (count + SU(5) posit).  The shallow gap
    (back-fit r=3/10) IS closed (3/8 is `derived`, no Target); but the DEEPER gap is the SU(5) posit,
    now counted via `n_posited` (DerivationAudit's new `Posited` provenance + `first_principles_strict`
    tier).  3/8 passes the OLD blind `fully` tier yet FAILS `first_principles_strict` — the contrast
    machine-shows the blind spot.  "From nothing" (strict, no posit) is a role-limit; every real
    derivation terminates in finite posits (P4 at the epistemic level).

    STATUS: 14 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From ToS Require Import stdlib.DerivationAudit.

Open Scope Q_scope.

(** sin²θ_W = r/(1+r) (replicated from process/ProcessWeinbergAngle.v). *)
Definition sin2_weinberg (r : Q) : Q := r / (1 + r).

(* ===================================================================== *)
(*  THE COUNT: 3/8 = Tr(T₃²)/Tr(Q²) over the SU(5) fundamental 5̄          *)
(* ===================================================================== *)

(** Tr(T₃²) over the 5̄: only the lepton doublet has T₃ = ±1/2, the three down-type antiquarks are
    SU(2) singlets (T₃ = 0).  Sum = (1/2)² + (1/2)² = 1/2. *)
Definition trT3sq : Q := (1 # 2) * (1 # 2) + (1 # 2) * (1 # 2).

(** Tr(Q²) over the 5̄: three down-type antiquarks of charge 1/3, the charged lepton of charge 1,
    the neutrino of charge 0.  Sum = 3·(1/3)² + 1² = 4/3. *)
Definition trQsq : Q := 3 * ((1 # 3) * (1 # 3)) + 1 * 1.

Lemma trT3sq_value : trT3sq == 1 # 2.
Proof. unfold trT3sq. vm_compute. reflexivity. Qed.

Lemma trQsq_value : trQsq == 4 # 3.
Proof. unfold trQsq. vm_compute. reflexivity. Qed.

(** ★ THE GAP-CLOSING COUNT: sin²θ_W(GUT) = Tr(T₃²)/Tr(Q²) = 3/8 — the 3 and 8 are sums of squared
    charges over the SU(5) multiplet, COUNTS, not chosen.  (Contrast 3/13, and the repo's asserted
    r(GUT)=3/5: here 3/8 is proved from charges.) *)
Lemma weinberg_gut_count : trT3sq / trQsq == 3 # 8.
Proof. unfold trT3sq, trQsq. vm_compute. reflexivity. Qed.

(** The repo's r(GUT) = 3/5 is forced by the counted 3/8: sin²θ_W = r/(1+r) = 3/8 at r = 3/5. *)
Lemma gut_ratio_forced : sin2_weinberg (3 # 5) == 3 # 8.
Proof. unfold sin2_weinberg. vm_compute. reflexivity. Qed.

(** So the GUT seed equals the charge count: sin²θ_W(GUT) = the SU(5) count = r(GUT)=3/5 value. *)
Lemma gut_seed_is_count : sin2_weinberg (3 # 5) == trT3sq / trQsq.
Proof.
  rewrite gut_ratio_forced. rewrite weinberg_gut_count. reflexivity.
Qed.

(* ===================================================================== *)
(*  THE AUDIT UPGRADE: Target (back-fit) → Structural + Indep (derived)    *)
(* ===================================================================== *)

(** DEEPENED RE-TAG (honest correction).  The 3/8 value rides on the SU(5) embedding (+ the SM
    matter assignment to 5̄⊕10), an external model NOT derived within ToS — a Posited leaf.  So the
    leaves are the structural charge-count AND the SU(5) posit: [Structural; Posited].  (The earlier
    tag [Structural; Structural] was too generous — it hid the model behind the count.) *)
Definition gut_value_audit : Audit := mkAudit (Structural :: Posited :: nil) 1%nat.

(** The OLD fully_first_principles STILL passes — it does NOT count the Posited leaf.  Kept ONLY to
    EXPOSE the blind spot, not as an honest verdict. *)
Lemma gut_value_passes_blind_tier : fully_first_principles gut_value_audit.
Proof.
  unfold fully_first_principles, gut_value_audit, n_gaps, n_indep. simpl. split; reflexivity.
Qed.

(** ★ THE HONEST VERDICT (the deeper gap, machine-seen): 3/8 is NOT first-principles-strict — it
    rides on the external SU(5) posit (n_posited = 1).  The CONTRAST between this lemma and the
    previous one IS the SU(5) posit — the deeper gap, now counted. *)
Lemma gut_value_not_strict : ~ first_principles_strict gut_value_audit.
Proof.
  unfold first_principles_strict, gut_value_audit, n_gaps, n_indep, n_posited. simpl.
  intros (_ & _ & H). discriminate.
Qed.

Lemma gut_value_rides_on_model : rides_on_model gut_value_audit.
Proof. unfold rides_on_model, gut_value_audit, n_posited. simpl. lia. Qed.

(** Still no back-fit (derived): the Target leaf r=3/10 (WeinbergAudit) is genuinely gone — 3/8 is
    not circular.  So 3/8 is "derived but rides on a posit", strictly between the isotope shift
    (derived, only Indep) and a bare fit. *)
Lemma gut_value_derived : derived gut_value_audit.
Proof. unfold derived, gut_value_audit, n_gaps. reflexivity. Qed.

(** The low-energy 3/13 audited AFTER closure AND deepening: leaves are the charge-count
    (Structural), the SU(5) model (Posited), and the scale ratio M_GUT/m_Z (Indep) — NO Target.
    So it is derived (no back-fit) but neither strict nor model-free: it rides on the SU(5) posit
    and consumes an independent scale. *)
Definition lowenergy_audit : Audit := mkAudit (Structural :: Posited :: Indep :: nil) 1%nat.

Lemma lowenergy_derived : derived lowenergy_audit.
Proof. unfold derived, lowenergy_audit, n_gaps. reflexivity. Qed.

Lemma lowenergy_no_gap : n_gaps lowenergy_audit = 0%nat.
Proof. unfold lowenergy_audit, n_gaps. reflexivity. Qed.

Lemma lowenergy_not_strict : ~ first_principles_strict lowenergy_audit.
Proof.
  unfold first_principles_strict, lowenergy_audit, n_gaps, n_indep, n_posited. simpl.
  intros (_ & H & _). discriminate.
Qed.

Lemma lowenergy_rides_on_model : rides_on_model lowenergy_audit.
Proof. unfold rides_on_model, lowenergy_audit, n_posited. simpl. lia. Qed.

(* ===================================================================== *)
(*  Synthesis: the gap, closed                                            *)
(* ===================================================================== *)

(** Closing the shallow gap — and SEEING the deeper one:
      (count) sin²θ_W(GUT) = Tr(T₃²)/Tr(Q²) = 3/8 over the SU(5) 5̄ (`weinberg_gut_count`); r(GUT)=3/5
        forced by it (`gut_ratio_forced`);
      (shallow gap closed) the back-fit r=3/10 (Target) is gone — 3/8 and 3/13 are derived, no
        back-fit (`gut_value_derived`, `lowenergy_derived`);
      (DEEPER gap seen) but 3/8 RIDES ON the SU(5) posit: it passes the OLD blind fully tier
        (`gut_value_passes_blind_tier`) yet FAILS the honest strict tier (`gut_value_not_strict`,
        `gut_value_rides_on_model`) — the contrast IS the SU(5) posit; likewise the low-energy value
        (`lowenergy_not_strict`, `lowenergy_rides_on_model`).
    Verdict: the shallow gap (back-fit) is closed; the deeper gap (the external SU(5) posit) is now
    COUNTED (n_posited), not hidden.  3/8 is derived-but-rides-on-a-model — strictly weaker than the
    isotope shift (derived, only Indep); "from nothing" (strict, no posit) remains a role-limit. *)
Theorem weinberg_gap_closing :
  (trT3sq / trQsq == 3 # 8)
  /\ (sin2_weinberg (3 # 5) == 3 # 8)
  /\ (fully_first_principles gut_value_audit /\ ~ first_principles_strict gut_value_audit
      /\ rides_on_model gut_value_audit /\ derived gut_value_audit)
  /\ (derived lowenergy_audit /\ ~ first_principles_strict lowenergy_audit
      /\ rides_on_model lowenergy_audit).
Proof.
  split; [ exact weinberg_gut_count | ].
  split; [ exact gut_ratio_forced | ].
  split; [ split; [ exact gut_value_passes_blind_tier
         | split; [ exact gut_value_not_strict
         | split; [ exact gut_value_rides_on_model | exact gut_value_derived ] ] ] | ].
  split; [ exact lowenergy_derived
         | split; [ exact lowenergy_not_strict | exact lowenergy_rides_on_model ] ].
Qed.
