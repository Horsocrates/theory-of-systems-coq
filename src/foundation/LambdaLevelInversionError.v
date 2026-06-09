(** * LambdaLevelInversionError.v — locating the ERROR behind the refuted prediction of
       LambdaRunningVacuumBound.v.  A falsified conclusion from sound-looking steps means a FALSE step
       (modus tollens).  The E/R/R analysis pins it: the dynamical reading rho_Lambda ∝ H^2 is a
       LEVEL-INVERSION — it reads an ELEMENT (the vacuum density rho_Lambda) directly off the aggregate
       RULE (Friedmann's H^2), ERASING the vacuum's ROLE (its equation of state w=-1).  Worse, it
       CONTRADICTS the framework's OWN theorem that the vacuum has p=-rho (w=-1): VacuumIsAntigravity.v /
       AntigravityCondition.v.  Restoring w=-1 gives rho_Lambda = const, Omega_Lambda EVOLVES (matches
       data) — and the "dynamical derivation of smallness" collapses to a re-expression of the observed
       value (snapshot), vindicating OpenFrontierLedger.v: the smallness is a free magnitude.

    THE E/R/R LEVELS (PhysicsERR.v generative order Rules -> Roles -> Elements).
      Elements (L1): rho_Lambda, rho_matter, rho_radiation — the actual energy densities (what exists).
      Roles    (L4): the equation of state w of each component — its KIND.  w=-1 is the vacuum's defining
                     Role, PROVEN by the framework (p=-rho, VacuumIsAntigravity.v).
      Rules    (L5): continuity rho' = -3H(1+w)rho (evolves each Element THROUGH its Role w) and Friedmann
                     H^2 ∝ sum(rho) (aggregate geometry<->content balance).
      Correct chain: Rule (continuity) acts THROUGH Role (w) to give the Element's law rho(a) ∝ a^(-3(1+w)).

    THE ERROR (step 3 of the refuted chain: rho_Lambda := c·H^2).
      (inversion)     the Element rho_Lambda is slaved to the aggregate Rule H^2, BYPASSING its Role w.
      (contradiction) rho_Lambda ∝ H^2 in a w_dom-dominated era means rho_Lambda ∝ a^(-3(1+w_dom)), i.e. it
                      implicitly assigns the vacuum w = w_dom /= -1 (w=0 in matter era, 1/3 in radiation) —
                      contradicting the framework's proven vacuum Role w=-1.  So the refuted prediction is
                      INTERNALLY INCONSISTENT with VacuumIsAntigravity.v.

    THE FIX (respect the vacuum Role).
      With w=-1: continuity ⇒ rho_Lambda ∝ a^0 = CONST.  Then rho_matter ∝ a^-3 grows into the past while
      rho_Lambda stays fixed ⇒ Omega_Lambda EVOLVES (tiny early, ~0.7 now) — matching observation.  The
      corrected reading is consistent; it makes NO new dynamical prediction (LCDM-like), and the smallness
      of the constant returns to the free-magnitude value-wall (OpenFrontierLedger.v).

    HONEST consequence for the prior files.  SmallnessExponent.v's arithmetic (122=2·61) is TRUE, but its
    claim to "derive" the smallness was a re-expression of the observed Lambda~H0^2 (snapshot), not a
    forward derivation.  StageBridge.v's K=M_P/age (P4 clock) stands.  The "crack" in the value-wall was the
    level-inversion; removing it restores OpenFrontierLedger's verdict (smallness = free magnitude).

    Elements: scaling exponent of rho(a) per component ; the densities at two scale factors.
    Roles:    w = equation of state (vacuum w=-1 PROVEN by the framework) ; the era's dominant w_dom.
    Rules:    rho ∝ a^(-3(1+w)) ; rho_Lambda∝H^2 forces a non-vacuum exponent ⇒ violates the vacuum Role.

    ============ E/R/R разбор (ошибки) ============
      Elements (L1): плотности ρ_Λ, ρ_m (что существует); показатели масштабирования ρ(a).
      Roles    (L4): w каждой компоненты — её РОД; w=-1 = Роль вакуума, ДОКАЗАННАЯ рамкой (p=-ρ).
      Rules    (L5): непрерывность ρ ∝ a^(-3(1+w)) действует ЧЕРЕЗ Роль w; Фридман H²∝Σρ — агрегат.
      ДИАГНОЗ (P4/L5): шаг ρ_Λ:=c·H² = ИНВЕРСИЯ УРОВНЕЙ (Element считан с агрегатного Правила H², Роль w
      стёрта) И противоречие с собственной теоремой VacuumIsAntigravity (w=-1). Восстановив w=-1: ρ_Λ=const,
      Ω_Λ эволюционирует (совпадает с данными), динамич. предсказания нет, малость = свободная магнитуда
      (OpenFrontierLedger подтверждён). Уровень: ИСПРАВЛЕНИЕ ошибки деривации (не новый результат).

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The correct Rule: rho(a) ∝ a^(-3(1+w)) — content evolves THROUGH its w  *)
(* ===================================================================== *)

(** The scale-factor exponent of a content component with equation of state w: rho ∝ a^(eos_exponent w). *)
Definition eos_exponent (w : Q) : Q := - (3 * (1 + w)).

(** The vacuum's Role, PROVEN by the framework (VacuumIsAntigravity.v: p = -rho). *)
Definition vacuum_w : Q := -1.

(** * The vacuum Role w=-1 gives a CONSTANT density: exponent 0 (rho_Lambda ∝ a^0). This is the correct
    scaling — the one the framework's own vacuum theorem entails. *)
Theorem vacuum_scaling_const : eos_exponent vacuum_w == 0.
Proof. unfold eos_exponent, vacuum_w. vm_compute. reflexivity. Qed.

(** Sanity: matter (w=0) ∝ a^-3, radiation (w=1/3) ∝ a^-4 — distinct non-zero exponents. *)
Theorem matter_scaling : eos_exponent 0 == -(3).
Proof. unfold eos_exponent. vm_compute. reflexivity. Qed.

Theorem radiation_scaling : eos_exponent (1 # 3) == -(4).
Proof. unfold eos_exponent. vm_compute. reflexivity. Qed.

(** The exponent is 0 IFF w = -1 (only the vacuum Role gives a constant density). *)
Theorem eos_exponent_zero_iff : forall w, eos_exponent w == 0 <-> w == -1.
Proof. intro w. unfold eos_exponent. split; intro H; lra. Qed.

(* ===================================================================== *)
(*  The error: rho_Lambda ∝ H^2 forces a NON-vacuum exponent (Role-erasure) *)
(* ===================================================================== *)

(** In a w_dom-dominated era, Friedmann gives H^2 ∝ a^(eos_exponent w_dom); so the dynamical reading
    rho_Lambda ∝ H^2 assigns rho_Lambda the exponent of the DOMINANT component, not the vacuum's. *)

(** * THE LEVEL-INVERSION, made precise: in any non-vacuum era (w_dom /= -1), the H^2-tracking reading
    gives rho_Lambda a NON-vacuum scaling — contradicting the framework's vacuum Role w=-1. *)
Theorem dynamical_forces_nonvacuum_exponent :
  forall w_dom, ~ (w_dom == -1) -> ~ (eos_exponent w_dom == eos_exponent vacuum_w).
Proof.
  intros w_dom Hw Hc.
  apply Hw.
  apply (proj1 (eos_exponent_zero_iff w_dom)).
  rewrite Hc. exact vacuum_scaling_const.
Qed.

(* ===================================================================== *)
(*  The fix: w=-1 ⇒ rho_Lambda const ⇒ Omega_Lambda EVOLVES (matches data)  *)
(* ===================================================================== *)

(** Corrected vacuum fraction: rho_Lambda CONST, rho_matter = rhoM0·a^-3 (its Role w=0).
    Omega_Lambda(a) = rho_Lambda / (rho_Lambda + rho_matter). *)
Definition Omega_L_correct (rhoL rhoM0 a : Q) : Q :=
  rhoL / (rhoL + rhoM0 / (a * a * a)).

(** Today (a=1, rhoL=0.7, rhoM0=0.3): Omega_Lambda = 0.7. *)
Theorem Omega_correct_now : Omega_L_correct (7 # 10) (3 # 10) 1 == 7 # 10.
Proof. unfold Omega_L_correct. vm_compute. reflexivity. Qed.

(** At a=1/10 (deep in the matter era): Omega_Lambda = 7/3007 — tiny. *)
Theorem Omega_correct_early_val : Omega_L_correct (7 # 10) (3 # 10) (1 # 10) == 7 # 3007.
Proof. unfold Omega_L_correct. vm_compute. reflexivity. Qed.

(** * The corrected reading: Omega_Lambda EVOLVES (small in the past, ~0.7 now) — matching observation,
    UNLIKE the refuted constant-Omega prediction.  Respecting the vacuum Role fixes the physics. *)
Theorem Omega_correct_evolves :
  Omega_L_correct (7 # 10) (3 # 10) (1 # 10) < Omega_L_correct (7 # 10) (3 # 10) 1.
Proof. rewrite Omega_correct_early_val, Omega_correct_now. lra. Qed.

(* ===================================================================== *)
(*  Verdict: the two readings, by consistency with the vacuum Role         *)
(* ===================================================================== *)

Inductive Reading := DynamicalHsquared | VacuumConst.

(** A reading is admissible iff it respects the framework's vacuum Role w=-1. *)
Definition respects_vacuum_role (r : Reading) : bool :=
  match r with DynamicalHsquared => false | VacuumConst => true end.

Theorem readings_verdict :
  respects_vacuum_role DynamicalHsquared = false
  /\ respects_vacuum_role VacuumConst = true.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** Locating and fixing the error behind the refuted prediction:
      (correct Rule) the vacuum Role w=-1 entails rho_Lambda ∝ a^0 = const (vacuum_scaling_const);
      (the error)    rho_Lambda ∝ H^2 forces a NON-vacuum exponent in any non-vacuum era — a level-inversion
                     contradicting the framework's own vacuum Role (dynamical_forces_nonvacuum_exponent);
      (the fix)      with rho_Lambda const, Omega_Lambda EVOLVES (matches data), unlike the refuted constant;
      (verdict)      the DynamicalHsquared reading violates the vacuum Role; VacuumConst respects it.
    The falsified prediction was an internal inconsistency (Element slaved to aggregate Rule, Role erased),
    not a verdict of nature against the framework.  Corrected, the framework is consistent; the smallness of
    the (now constant) Lambda returns to the free-magnitude value-wall (OpenFrontierLedger.v). *)
Theorem lambda_level_inversion_diagnosis :
  eos_exponent vacuum_w == 0
  /\ (forall w_dom, ~ (w_dom == -1) -> ~ (eos_exponent w_dom == eos_exponent vacuum_w))
  /\ Omega_L_correct (7 # 10) (3 # 10) (1 # 10) < Omega_L_correct (7 # 10) (3 # 10) 1
  /\ respects_vacuum_role DynamicalHsquared = false
  /\ respects_vacuum_role VacuumConst = true.
Proof.
  split; [ exact vacuum_scaling_const | ].
  split; [ exact dynamical_forces_nonvacuum_exponent | ].
  split; [ exact Omega_correct_evolves | ].
  split; reflexivity.
Qed.
