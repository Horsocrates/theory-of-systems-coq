(** * WeinbergAudit.v — applying the derivation audit (DerivationAudit.v) to the flagship suspect
      sin²(θ_W) = 3/13, and LOCATING the fit/derived gap precisely: it is the input coupling ratio
      r = g'²/g², not the formula.

      THE FINDING (traced from process/ProcessWeinbergAngle.v).  The chain producing 3/13 is:
          r := 3/10                       (* the coupling ratio g'²/g², an INPUT *)
          sin²θ_W = r/(1+r)               (* the formula — standard electroweak, DERIVED *)
                  = 3/13,   13 = 3+10.    (* arithmetic; the denominator is num+den of r *)
      So the FORMULA r/(1+r) is structural (forced by electroweak theory), but the INPUT r = 3/10
      is a FIT: it was chosen as the round value making r/(1+r) ≈ 0.231 = the MEASURED sin²θ_W —
      i.e. r is back-fitted from the very datum being "predicted".  The "13" is not an independent
      count; it is forced to be 3+10 once r is fixed.  Hence sin²θ_W = 3/13 is "derived given a
      fitted input" — which the audit classifies as a FIT (n_gaps = 1, gap = r = 3/10).

      THE CONTRAST.  (i) The isotope shift (RydbergIsotopeShift.v) takes its input (masses) from an
      INDEPENDENT experiment (mass spectrometry, an Indep leaf) — so it is derived.  Here the input
      r is back-fitted from sin²θ_W itself (a Target leaf) — so it is a fit.  (ii) The ONE fully
      structural electroweak value is the GUT point r = 1 (equal couplings, the symmetric point) ⟹
      sin²θ_W = 1/2 — forced, but it is the high-scale value, NOT the measured 0.231.  (RG running
      from r=1 down to m_Z could in principle yield r≈3/10, but that needs empirical scale inputs
      (GUT scale, m_Z) — at best Indep leaves, never fully-first-principles; and as stated, r=3/10
      is a round-number fit, a Target leaf.)

      VERDICT: sin²θ_W = 3/13 is a FIT.  The formula is derived; the low-energy value is fitted via
      the coupling ratio.  The gap, located: r = 3/10.

    Elements: the formula r/(1+r); the fitted ratio r=3/10; the structural GUT point r=1 (L1 + P4)
    Roles:    the coupling ratio r = g'²/g² — the single free input, back-fitted from the measured
              sin²θ_W (a gap); the formula plays the derived structural part
    Rules:    the audit rule (derived ⟺ no leaf depends on the target datum); sin²θ_W = r/(1+r)

    ============ E/R/R разбор ============
      Rules (L5): правило аудита — выведено ⟺ ни один лист не зависит от целевого данного; sin²θ_W=r/(1+r).
      Roles (L4): отношение связей r=g'²/g² — единственный свободный вход, подогнанный из самого sin²θ_W
                  (лист Target = разрыв); формула играет выведенную структурную часть; «13»=3+10, не счёт.
      Elements  : формула r/(1+r); подогнанный r=3/10; структурная GUT-точка r=1⟹1/2.
    ДИАГНОСТИКА (P4): аудит ЛОКАЛИЗУЕТ разрыв — это ВХОДНОЕ отношение связей, не формула. sin²θ_W=3/13 =
    «выведено при подогнанном входе» = ПОДГОНКА (n_gaps=1, разрыв = r=3/10). Контраст: изотоп-сдвиг берёт вход из
    НЕЗАВИСИМОГО эксперимента (Indep) ⟹ выведен; здесь вход подогнан из целевого данного (Target) ⟹ подгонка.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith.
From ToS Require Import stdlib.DerivationAudit.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The electroweak formula (replicated from process/ProcessWeinbergAngle.v) *)
(* ===================================================================== *)

(** sin²θ_W = r/(1+r), where r = g'²/g² is the coupling ratio.  The FORMULA is structural
    (standard electroweak); the value of r is the input. *)
Definition sin2_weinberg (r : Q) : Q := r / (1 + r).

(** ★ The one fully structural value: at r = 1 (equal couplings — the symmetric GUT point)
    sin²θ_W = 1/2.  Forced, no fit; but this is the high-scale value, not the measured 0.231. *)
Lemma weinberg_gut_point : sin2_weinberg 1 == 1 # 2.
Proof. unfold sin2_weinberg. vm_compute. reflexivity. Qed.

(** The 3/13 follows from the FITTED ratio r = 3/10 by the formula (the arithmetic is derived;
    the input is not).  This is the only place 3/13 is "produced". *)
Lemma weinberg_from_fitted_ratio : sin2_weinberg (3 # 10) == 3 # 13.
Proof. unfold sin2_weinberg. vm_compute. reflexivity. Qed.

(** The "13" is not an independent count: sin²θ_W = r/(1+r) with r = 3/10 gives 3/(3+10), so the
    denominator is forced to be 3+10 once r is fixed.  Only r is free. *)
Lemma thirteen_is_three_plus_ten : (3 + 10 = 13)%Z.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The audit of sin²θ_W = 3/13 — the gap, located                         *)
(* ===================================================================== *)

(** ★ The audit of the 3/13 prediction: its construction has ONE gap leaf — the coupling ratio
    r = 3/10, back-fitted from the measured sin²θ_W — and matches one datum.  So it is NOT derived
    (n_gaps = 1), with predictive surplus 0.  The gap is located: r = 3/10. *)
Definition weinberg_audit : Audit := mkAudit (Target :: nil) 1%nat.

Lemma weinberg_not_derived : ~ derived weinberg_audit.
Proof. unfold derived, weinberg_audit, n_gaps. simpl. discriminate. Qed.

Lemma weinberg_surplus_zero : surplus weinberg_audit = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma weinberg_one_gap : n_gaps weinberg_audit = 1%nat.
Proof. unfold weinberg_audit, n_gaps. reflexivity. Qed.

(* ===================================================================== *)
(*  The structural contrast: the GUT point is fully first-principles       *)
(* ===================================================================== *)

(** The GUT point (r = 1, the symmetric equal-coupling point ⟹ sin²θ_W = 1/2) audited: its only
    leaf is structural (the symmetric point r = 1 is forced, not fitted), so it is
    fully-first-principles.  But it predicts 1/2 — the high-scale value, not the measured 0.231.
    This is the ONLY forced electroweak mixing value; the low-energy 3/13 needs the fitted r. *)
Definition gut_point_audit : Audit := mkAudit (Structural :: nil) 1%nat.

Lemma gut_point_fully : fully_first_principles gut_point_audit.
Proof.
  unfold fully_first_principles, gut_point_audit, n_gaps, n_indep. simpl. split; reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis: the honest verdict                                         *)
(* ===================================================================== *)

(** The Weinberg-angle audit:
      (formula derived) sin²θ_W = r/(1+r); the GUT point r=1 ⟹ 1/2 is structurally forced
        (`weinberg_gut_point`, `gut_point_fully` is fully-first-principles);
      (value fitted) 3/13 follows only from the FITTED ratio r = 3/10 (`weinberg_from_fitted_ratio`),
        whose denominator 13 = 3+10 is forced once r is fixed (`thirteen_is_three_plus_ten`);
      (verdict) the 3/13 prediction is NOT derived — one gap leaf, the coupling ratio r=3/10
        (`weinberg_not_derived`, `weinberg_one_gap`), surplus 0.
    The gap, located and machine-checked: sin²θ_W = 3/13 is a fit whose single gap is r = 3/10. *)
Theorem weinberg_audit_verdict :
  (sin2_weinberg 1 == 1 # 2)
  /\ (sin2_weinberg (3 # 10) == 3 # 13)
  /\ fully_first_principles gut_point_audit
  /\ (~ derived weinberg_audit /\ n_gaps weinberg_audit = 1%nat /\ surplus weinberg_audit = 0%Z).
Proof.
  split; [ exact weinberg_gut_point | ].
  split; [ exact weinberg_from_fitted_ratio | ].
  split; [ exact gut_point_fully | ].
  split; [ exact weinberg_not_derived
         | split; [ exact weinberg_one_gap | exact weinberg_surplus_zero ] ].
Qed.
