(** * MinimalLengthDerivation.v — Q2 of the open agenda: can the minimal length be DERIVED (not posited),
      giving a real Fermi-LAT-testable number?  HONEST answer: the dimensionful VALUE is NOT derived (it
      needs one empirical anchor), but the dimensionless STRUCTURE and energy-SCALING ARE derived and
      PARAMETER-FREE — and that scaling is exactly what time-of-flight experiments test.  This is a
      derivation-AUDIT of the minimal length, in the same derived/posited spirit as WeinbergAudit.v.

    -- The factorization --
      The minimal length l enters an observable only through the dimensionless combination l*k (k = probe
      energy/momentum).  The deviation factor is effect l k = (l*k)^2.  Three aspects, three honest tags:
        - ENERGY SCALING (DERIVED, parameter-free): effect(k2)/effect(k1) = (k2/k1)^2 — the l CANCELS, so
          the ratio is a pure number.  ONE anchor (the effect at one energy) fixes the WHOLE curve.
        - the dimensionful SCALE l (POSITED): different l give different effects at the same probe, so l is
          a free dimensionful parameter — one empirical anchor is needed (no pure derivation of meters).
        - the leading COEFFICIENT (REALIZATION-DEPENDENT): a regular lattice gives ~1/24 (linear LV) which
          Fermi-LAT REFUTES (NatureBoundaryLedger.v: predicted ratio 1 < observed floor 6/5); a Lorentz-
          invariant causal set has NO leading-order LV (suppressed).  So the coefficient is not a clean ToS
          output — it depends on the data-constrained realization.

    -- The honest verdict --
      The minimal-length VALUE is NOT derived (one anchor + a realization choice are needed).  Its STRUCTURE
      and energy-scaling ARE derived and parameter-free — testable.  Same split as the rest of the audit:
      ToS gives structure, not the dimensionful free parameter.  No overclaim of "we derived the Planck
      length".

    -- HONEST scope --
      effect = (l*k)^2 models the quadratic case; the exact power (linear vs quadratic LV) is itself
      realization-dependent, but the l-cancellation (parameter-free scaling, one-anchor-fixes-all) holds for
      either power.  This file does NOT derive a dimensionful number; it locates precisely what is and is
      not derivable about the minimal length.

    Elements: effect l k = (l*k)^2; scaling effect(k1)*k2^2 = effect(k2)*k1^2 (l cancels); l free; coeff differ
    Roles:    scaling = Derived (parameter-free); scale = Posited (one anchor); coefficient = RealizationDep
    Rules:    value not derived; structure + scaling derived and parameter-free; one anchor fixes the curve

    ============ E/R/R разбор ============
      Rules (L5): минимальная длина l входит ТОЛЬКО через безразмерную l*k; структура (масштабирование)
                  выводима и параметр-свободна (l сокращается); размерное значение l -- нет (один якорь).
      Roles (L4): масштабирование = Derived (l сокращается); масштаб l = Posited (якорь); коэффициент =
                  RealizationDependent (решётка 1/24 опровергнута H16, causal-set подавлен H17).
      Elements  : effect l k := (l*k)^2; effect(k1)*k2^2 = effect(k2)*k1^2; effect 1 1 <> effect 2 1.
    ДИАГНОСТИКА (P4): ЧЕСТНО -- значение НЕ выводимо (размерный якорь + выбор реализации), но СТРУКТУРА и
    масштабирование выводимы и параметр-свободны (тестируемо: задержка ~ энергия).  Тот же derived/posited
    раскол: ToS даёт структуру, не размерный свободный параметр.  НЕ переклейм "вывели l_Planck".  Q2 =
    аудит минимальной длины; смыкается с DerivationAudit + H16/H17.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The dimensionless deviation factor                                     *)
(* ===================================================================== *)

(** The minimal length l enters only through the dimensionless combination l*k. *)
Definition effect (l k : Q) : Q := (l * k) * (l * k).

(* ===================================================================== *)
(*  DERIVED: the energy scaling is parameter-free (l cancels)              *)
(* ===================================================================== *)

(** ★ The energy-SCALING is independent of l: effect(k1)*k2^2 = effect(k2)*k1^2, i.e.
    effect(k2)/effect(k1) = (k2/k1)^2 for ANY l.  The minimal length cancels — the ratio is a pure number. *)
Lemma scaling_param_free : forall l k1 k2,
  effect l k1 * (k2 * k2) == effect l k2 * (k1 * k1).
Proof. intros l k1 k2. unfold effect. ring. Qed.

(** One anchor fixes the whole curve: the effect at any probe k2 is determined by the effect at the anchor
    probe k1 and the energies — no remaining freedom (the ratio is the parameter-free (k2/k1)^2). *)
Lemma one_anchor_determines : forall l k1 k2,
  effect l k2 * (k1 * k1) == effect l k1 * (k2 * k2).
Proof. intros l k1 k2. unfold effect. ring. Qed.

(** Concrete parameter-free scaling: doubling the probe quadruples the effect, for any l (here l = 3). *)
Lemma ex_scaling : effect 3 2 == 4 * effect 3 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  POSITED: the dimensionful scale is NOT derived                         *)
(* ===================================================================== *)

(** ★ Different minimal lengths give different effects at the same probe — l is a free dimensionful scale,
    so its VALUE is not derived (one empirical anchor is needed). *)
Lemma scale_not_derived : ~ (effect 1 1 == effect 2 1).
Proof. intro H. vm_compute in H. discriminate. Qed.

(* ===================================================================== *)
(*  REALIZATION-DEPENDENT: the leading coefficient                         *)
(* ===================================================================== *)

(** A regular lattice gives a leading coefficient ~1/24 (linear LV, REFUTED by Fermi-LAT); a Lorentz-
    invariant causal set has no leading-order LV (suppressed).  So the coefficient is realization-dependent. *)
Definition lattice_coeff : Q := 1 # 24.
Definition causal_set_leading_coeff : Q := 0.

Lemma coeff_realization_dependent : ~ (lattice_coeff == causal_set_leading_coeff).
Proof. unfold lattice_coeff, causal_set_leading_coeff. intro H. vm_compute in H. discriminate. Qed.

(* ===================================================================== *)
(*  The audit tags                                                         *)
(* ===================================================================== *)

Inductive Aspect := ScaleValue | EnergyScaling | Coefficient.
Inductive Tag := Derived | Posited | RealizationDependent.

Definition audit (a : Aspect) : Tag :=
  match a with
  | ScaleValue    => Posited
  | EnergyScaling => Derived
  | Coefficient   => RealizationDependent
  end.

Lemma audit_verdict :
  audit ScaleValue = Posited /\ audit EnergyScaling = Derived /\ audit Coefficient = RealizationDependent.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the honest minimal-length derivation verdict                 *)
(* ===================================================================== *)

(** Q2 verdict — can the minimal length be derived?
      (scaling) the energy-SCALING is DERIVED and parameter-free: effect(k1)*k2^2 = effect(k2)*k1^2,
                independent of l — ONE anchor fixes the whole curve (testable);
      (scale)   the dimensionful VALUE is POSITED — different l give different effects (one anchor needed);
      (tags)    scale = Posited, scaling = Derived;
      (coeff)   the leading coefficient is realization-dependent (lattice refuted, causal-set suppressed).
    The minimal-length VALUE is NOT derived; its STRUCTURE and scaling ARE.  ToS gives the parameter-free
    energy-scaling (Fermi-LAT-testable), anchors the scale with one measurement, and the coefficient is set
    by the data-constrained realization.  No overclaim of a derived Planck length. *)
Theorem minimal_length_derivation :
  (forall l k1 k2, effect l k1 * (k2 * k2) == effect l k2 * (k1 * k1))
  /\ ~ (effect 1 1 == effect 2 1)
  /\ audit ScaleValue = Posited
  /\ audit EnergyScaling = Derived
  /\ ~ (lattice_coeff == causal_set_leading_coeff).
Proof.
  split; [ exact scaling_param_free | ].
  split; [ exact scale_not_derived | ].
  split; [ reflexivity | ].
  split; [ reflexivity | exact coeff_realization_dependent ].
Qed.
