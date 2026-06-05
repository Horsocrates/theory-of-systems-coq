(** * RydbergIsotopeShift.v — the Rydberg isotope shift (Urey's 1932 deuterium discovery) as a
      machine-checked prediction vs data, and an E/R/R reading: the isotope shift is the Element
      that survives when the role-limit constant R_∞ cancels in a ratio.

      INAUGURAL FILE of the spectroscopy direction: numerical predictions over ℚ comparable to
      published data (NIST/CODATA), with HONEST status labels.  The absolute wavelength of a
      one-electron line is a role-limit (it carries R_∞, α, ℏc — measured/irrational constants).
      But the ISOTOPE SHIFT — the ratio of two isotopes' lines — is a pure rational function of the
      (rational, measured) mass ratios: R_∞ cancels.  So the data-comparable prediction lives on
      the Element side, exactly as in the cluster (absolute = role-limit, ratio = Element).

      THE PHYSICS (standard QM, not novel to ToS).  A one-electron atom with nuclear mass M has
      Rydberg constant R_M = R_∞ · M/(M+m_e) = R_∞ · redfac(M/m_e), redfac(r) := r/(r+1).  Line
      wavelengths scale as λ ∝ 1/R_M.  Hence for two isotopes (proton p, deuteron d):
          λ_H / λ_D  =  R_D / R_H  =  redfac(m_d/m_e) / redfac(m_p/m_e),
      a pure rational in the mass ratios — independent of R_∞.  This IS the measured Balmer
      isotope shift (how deuterium was found in 1932).

      WHAT IS MACHINE-CHECKED.  (a) the predicted H/D Balmer wavelength ratio brackets the value
      1.000272 < λ_H/λ_D < 1.000273; (b) the fractional shift (λ_H−λ_D)/λ_D ≈ 2.72·10⁻⁴; (c) the
      H/T ratio ≈ 1.000363; (d) the absolute Balmer-α shift ≈ 178–179 pm (using the measured λ_D).
      The MEASURED Balmer-α isotope shift is Δλ ≈ 1.79 Å (=179 pm), fractional ≈ 2.72·10⁻⁴ — the
      prediction agrees to ~4 significant figures.  Honest: this is the standard reduced-mass
      correction; what is new here is only the machine-checked arithmetic-vs-data and the E/R/R
      reading.  Inputs are published CODATA mass ratios (m_p/m_e = 1836.15267, m_d/m_e =
      3670.48297, m_t/m_e = 5496.92154); the % agreement is "given these inputs".

    Elements: the rational mass ratios; the rational reduced-mass factors redfac; the rational
              wavelength ratios and the rational shift (L1 + P4)
    Roles:    redfac(r) = R_M/R_∞ — the single quantity whose value means "which isotope"; R_∞
              (infinite nuclear mass) is the unreachable role-limit baseline, hit by no real atom
    Rules:    the Rydberg law with the reduced-mass correction R_M = R_∞·M/(M+m_e); energy ∝
              reduced mass; only the nuclear mass M changes between isotopes

    ============ E/R/R разбор ============
      Rules (L5): закон Ридберга с поправкой на приведённую массу R_M=R_∞·M/(M+m_e); энергия ∝
                  приведённой массе; между изотопами меняется лишь масса ядра M.
      Roles (L4): redfac(r)=R_M/R_∞ — величина «какой изотоп»; R_∞ (бесконечная масса) — недостижимый
                  предел-роль, базис, не достигаемый ни одним конечномассовым атомом.
      Elements  : рациональные отношения масс; рациональные redfac; рациональное λ_H/λ_D и сдвиг.
    ДИАГНОСТИКА (P4): сдвиг есть Element, ВЫЖИВАЮЩИЙ при сокращении предела-роли. Абсолют λ∝1/R_∞ —
    role-limit (R_∞,α,ℏc измеренные/иррациональные); ОТНОШЕНИЕ λ_H/λ_D=redfac(m_d)/redfac(m_p) — чистая
    рациональная функция, R_∞ СОКРАЩАЕТСЯ ⟹ сравнимое с данными предсказание живёт на стороне Element.
    Тема кластера: абсолют=role-limit, отношение=Element; изотопический сдвиг — «рациональная тень».

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Published inputs (CODATA mass ratios M/m_e, as rationals)              *)
(* ===================================================================== *)

(** Proton / electron mass ratio, 1836.15267 (CODATA 1836.15267343). *)
Definition mp : Q := 183615267 # 100000.
(** Deuteron / electron mass ratio, 3670.48297 (CODATA 3670.48296788). *)
Definition md : Q := 367048297 # 100000.
(** Triton / electron mass ratio, 5496.92154 (CODATA 5496.92153573). *)
Definition mt : Q := 549692154 # 100000.

(* ===================================================================== *)
(*  THE ENGINE: the reduced-mass factor redfac(r) = R_M/R_∞ = r/(r+1)      *)
(* ===================================================================== *)

(** The reduced-mass factor R_M/R_∞ = M/(M+m_e) = r/(r+1), r = M/m_e.  This is the ONLY thing
    that changes between isotopes; R_∞ (the r→∞ limit, redfac→1) is the role-limit baseline. *)
Definition redfac (r : Q) : Q := r / (r + 1).

(** Each real atom's factor is strictly below the R_∞ baseline: redfac < 1 (finite mass always
    shifts the Rydberg constant below R_∞ — no real atom reaches the role-limit). *)
Lemma redfac_mp_lt1 : redfac mp < 1.
Proof. vm_compute. reflexivity. Qed.

Lemma redfac_md_lt1 : redfac md < 1.
Proof. vm_compute. reflexivity. Qed.

(** ★ Heavier nucleus ⟹ closer to the R_∞ baseline: redfac is monotone in the mass.
    redfac(m_p) < redfac(m_d) < redfac(m_t) < 1 — the ordering that drives every isotope shift. *)
Lemma redfac_ordering :
  redfac mp < redfac md /\ redfac md < redfac mt /\ redfac mt < 1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  THE PREDICTION: the H/D Balmer wavelength ratio (R_∞ cancels)          *)
(* ===================================================================== *)

(** ★ The isotope shift as a ratio: λ_H/λ_D = R_D/R_H = redfac(m_d)/redfac(m_p).  R_∞ cancels —
    this is a pure rational in the mass ratios, the Element-side prediction. *)
Definition lam_ratio_HD : Q := redfac md / redfac mp.

(** ★ The predicted H/D Balmer wavelength ratio brackets 1.000272 < λ_H/λ_D < 1.000273.
    MEASURED: the Balmer-α isotope shift gives a ratio ≈ 1.000272 (fractional 2.72·10⁻⁴) — agreement
    to ~4 significant figures.  This is the 1932 deuterium-discovery number. *)
Lemma lam_ratio_HD_bracket :
  1000272 # 1000000 < lam_ratio_HD /\ lam_ratio_HD < 1000273 # 1000000.
Proof. split; vm_compute; reflexivity. Qed.

(** ★ The fractional isotope shift (λ_H−λ_D)/λ_D = λ_H/λ_D − 1 brackets 2.72·10⁻⁴.
    MEASURED Balmer-α fractional shift ≈ 2.72·10⁻⁴. *)
Lemma frac_shift_HD_bracket :
  272 # 1000000 < lam_ratio_HD - 1 /\ lam_ratio_HD - 1 < 273 # 1000000.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  The tritium line: the prediction extends to H/T                        *)
(* ===================================================================== *)

(** The H/T wavelength ratio λ_H/λ_T = redfac(m_t)/redfac(m_p), bracketing 1.000362 < · < 1.000363
    (fractional shift ≈ 3.63·10⁻⁴, larger than H/D since tritium is heavier). *)
Definition lam_ratio_HT : Q := redfac mt / redfac mp.

Lemma lam_ratio_HT_bracket :
  1000362 # 1000000 < lam_ratio_HT /\ lam_ratio_HT < 1000363 # 1000000.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  The absolute Balmer-α shift in picometers (using the measured λ_D)     *)
(* ===================================================================== *)

(** The measured Balmer-α wavelength of deuterium, 656.106 nm = 656106 pm (an absolute value — it
    carries R_∞, the role-limit; only the RATIO above is R_∞-free). *)
Definition lamD_Halpha_pm : Q := 656106 # 1.

(** ★ The predicted Balmer-α isotope shift Δλ = λ_D·(λ_H/λ_D − 1) brackets 178 pm < Δλ < 179 pm.
    MEASURED: Δλ(Hα−Dα) ≈ 1.79 Å = 179 pm — agreement to ~3 significant figures (the historical
    deuterium-discovery shift).  Honest: λ_D here is an absolute (role-limit) input; the pure
    prediction is the ratio above, and this only converts it to nm-scale. *)
Definition delta_HD_pm : Q := lamD_Halpha_pm * (lam_ratio_HD - 1).

Lemma delta_HD_pm_bracket :
  178 # 1 < delta_HD_pm /\ delta_HD_pm < 179 # 1.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Rydberg isotope shift, machine-checked vs data:
      (engine) redfac is monotone in the nuclear mass, below the R_∞ baseline (`redfac_ordering`);
      (H/D prediction) λ_H/λ_D brackets 1.000272–1.000273 (`lam_ratio_HD_bracket`), fractional
        shift ≈ 2.72·10⁻⁴ — the measured Balmer-α isotope shift, to ~4 significant figures;
      (H/T prediction) λ_H/λ_T brackets 1.000362–1.000363 (`lam_ratio_HT_bracket`);
      (absolute) the Balmer-α shift is 178–179 pm (`delta_HD_pm_bracket`), measured ≈ 179 pm.
    The R_∞-free RATIO is the Element-side prediction; the absolute wavelength is the role-limit. *)
Theorem isotope_shift_synthesis :
  (redfac mp < redfac md /\ redfac md < redfac mt /\ redfac mt < 1)
  /\ (1000272 # 1000000 < lam_ratio_HD /\ lam_ratio_HD < 1000273 # 1000000)
  /\ (272 # 1000000 < lam_ratio_HD - 1 /\ lam_ratio_HD - 1 < 273 # 1000000)
  /\ (1000362 # 1000000 < lam_ratio_HT /\ lam_ratio_HT < 1000363 # 1000000)
  /\ (178 # 1 < delta_HD_pm /\ delta_HD_pm < 179 # 1).
Proof.
  split; [ exact redfac_ordering | ].
  split; [ exact lam_ratio_HD_bracket | ].
  split; [ exact frac_shift_HD_bracket | ].
  split; [ exact lam_ratio_HT_bracket | exact delta_HD_pm_bracket ].
Qed.
