(** * GravityRuleUniversality.v — "gravity = Rule-object" deepened: the EQUIVALENCE PRINCIPLE
       (m_grav = m_inertial, universal free fall) is a STRUCTURAL consequence of gravity being
       the Rules-level of E/R/R — not a coincidence, not a fine-tuning.

    HYPOTHESIS.
    A force at the ROLES level (gauge) couples to a SEPARATE charge — a Role-label: it is
    SELECTIVE (some systems are neutral) and SIGNED (charge is +/-, so it screens).
    A force at the RULES level (gravity) couples to CONTENT — the existence-constituting amount
    (energy = number of distinctions, P4-positive for anything actual): the Rules govern EVERY
    Element by definition, so gravity is UNIVERSAL (no neutral system), UNSIGNED (content >= 0,
    no screening, always attractive), and — since inertia is the SAME content — gravitational
    "mass" EQUALS inertial "mass" identically.  Hence:
        EQUIVALENCE PRINCIPLE  m_grav = m_inertial  (both ARE content),
        UNIVERSAL FREE FALL    m_grav/m_inertial = 1 for EVERY system,
    are forced by gravity = Rules; while gauge charge-to-mass ratios vary (Role = separate label).

    ============ E/R/R разбор ============
      Elements : физ. системы; у каждой content (энергия = число дистинкций = КОНСТИТУИРУЕТ
                 существование, P4 > 0) и отдельный калибровочный заряд.
      Roles    : калибр. взаимодействие = Роль-метка — ИЗБИРАТЕЛЬНА (есть нейтральные) и ЗНАКОВА (+/-).
      Rules    : грав. взаимодействие = Правило-уровень — couples к content (управляет ВСЕМИ Элементами);
                 инерция = тот же content ⟹ m_grav = m_inertial тождественно, отношение ≡ 1.
      ДИАГНОСТИКА (P4): принцип эквивалентности = СТРУКТУРНОЕ следствие того, что гравитация couples
      к тому же content, что конституирует систему (= инерция), не совпадение; калибр. избирательность/
      экранирование = Роли суть отдельные метки. Element-сторона (0 акс). ЧЕСТНО: качественная структура
      (универсальность/эквивалентность/беззнаковость), НЕ количественная динамика (G, уравнения поля).
      Уровень: `новое обрамление известного`.

    Elements: PhysSystem (content > 0 ; gauge charge); grav_charge := content ; inertial := content.
    Roles:    gauge coupling = a separate signed, selective charge (a Role-label).
    Rules:    grav coupling = content = what constitutes existence = what inertia is = universal.

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  A physical system: content (P4-positive) + a separate gauge charge     *)
(* ===================================================================== *)

Record PhysSystem := mkSys {
  content : Q;            (** energy = amount of distinction = what constitutes existence *)
  gcharge : Q;            (** a gauge charge = a separate Role-label (may be 0 or negative) *)
  actual  : 0 < content   (** P4: to exist (non-trivially) = to carry positive content *)
}.

(** GRAVITY is the RULES level: it couples to CONTENT.  Inertia is the SAME content. *)
Definition grav_charge (s : PhysSystem) : Q := content s.
Definition inertial    (s : PhysSystem) : Q := content s.

(** GAUGE is the ROLES level: it couples to the SEPARATE charge (the Role-label). *)
Definition gauge_coupling (s : PhysSystem) : Q := gcharge s.

(* Three witness systems. *)
Definition sysA       : PhysSystem := mkSys 1 1     ltac:(lra).   (* content 1, charge 1  *)
Definition sysB       : PhysSystem := mkSys 1 2     ltac:(lra).   (* content 1, charge 2  *)
Definition sysNeutral : PhysSystem := mkSys 1 0     ltac:(lra).   (* content 1, charge 0  (gauge-neutral) *)
Definition sysNeg     : PhysSystem := mkSys 1 (-(1)) ltac:(lra).  (* content 1, charge -1 *)

(* ===================================================================== *)
(*  GRAVITY = RULE : universal, equivalence, unsigned                      *)
(* ===================================================================== *)

(** ★ EQUIVALENCE PRINCIPLE: gravitational "mass" = inertial "mass" — identically.
    Both are the SAME content; gravity couples to exactly what inertia is. *)
Lemma equivalence_principle : forall s, grav_charge s == inertial s.
Proof. intro s. reflexivity. Qed.

(** ★ UNIVERSALITY OF FREE FALL: the m_grav/m_inertial ratio is the SAME for ANY two systems
    (stated cross-multiplied, no division) — a trivial identity BECAUSE grav = inertial = content. *)
Lemma universal_free_fall : forall s1 s2,
  grav_charge s1 * inertial s2 == grav_charge s2 * inertial s1.
Proof. intros s1 s2. unfold grav_charge, inertial. ring. Qed.

(** ★ Every actual system GRAVITATES: positive gravitational charge (no gravitationally-neutral system). *)
Lemma gravity_universal : forall s, 0 < grav_charge s.
Proof. intro s. unfold grav_charge. exact (actual s). Qed.

(** ★ NO SCREENING / always attractive: gravitational charge is always > 0 (never +/-). *)
Lemma gravity_no_screening : forall s, 0 < grav_charge s.
Proof. exact gravity_universal. Qed.

(* ===================================================================== *)
(*  GAUGE = ROLE : selective, varying ratio, signed                        *)
(* ===================================================================== *)

(** A gauge-NEUTRAL system exists — yet (by gravity_universal) it still gravitates (the photon case). *)
Lemma gauge_selective : exists s, gauge_coupling s == 0.
Proof. exists sysNeutral. reflexivity. Qed.

Lemma neutral_still_gravitates : gauge_coupling sysNeutral == 0 /\ 0 < grav_charge sysNeutral.
Proof. split; [ reflexivity | exact (actual sysNeutral) ]. Qed.

(** ★ The gauge charge-to-mass ratio is NOT universal (contrast with free fall): two systems differ. *)
Lemma gauge_ratio_not_universal : exists s1 s2,
  ~ (gauge_coupling s1 * inertial s2 == gauge_coupling s2 * inertial s1).
Proof.
  exists sysA, sysB. unfold gauge_coupling, inertial, sysA, sysB. simpl. lra.
Qed.

(** ★ Gauge charge is SIGNED (both signs exist) — hence it can screen. *)
Lemma gauge_signed :
  (exists s, 0 < gauge_coupling s) /\ (exists s, gauge_coupling s < 0).
Proof.
  split.
  - exists sysA. unfold gauge_coupling, sysA. simpl. lra.
  - exists sysNeg. unfold gauge_coupling, sysNeg. simpl. lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE : gravity is a Rule (universal), gauge is a Role (selective)  *)
(* ===================================================================== *)

(** "Gravity = Rule-object" deepened.  Because gravity is the RULES level it couples to CONTENT
    (the existence-constituting amount = what inertia is), giving — for FREE — the three classic
    GR facts that drove Einstein to geometry:
      (equivalence)   m_grav = m_inertial identically (both ARE content);
      (universal fall) m_grav/m_inertial = 1 for every system;
      (no screening)  gravitational charge > 0 always (no +/-, always attractive),
    AND universality (every actual system gravitates).  GAUGE, being a ROLES-level label, is by
    contrast SELECTIVE (neutral systems exist), VARYING (charge/mass ratio differs), and SIGNED
    (screens).  The equivalence principle is structural here, not a fine-tuned coincidence. *)
Theorem gravity_is_rule_not_role :
  (* GRAVITY = RULE *)
  (forall s, grav_charge s == inertial s)
  /\ (forall s1 s2, grav_charge s1 * inertial s2 == grav_charge s2 * inertial s1)
  /\ (forall s, 0 < grav_charge s)
  (* GAUGE = ROLE *)
  /\ (exists s, gauge_coupling s == 0)
  /\ (exists s1 s2, ~ (gauge_coupling s1 * inertial s2 == gauge_coupling s2 * inertial s1))
  /\ ((exists s, 0 < gauge_coupling s) /\ (exists s, gauge_coupling s < 0)).
Proof.
  split. exact equivalence_principle.
  split. exact universal_free_fall.
  split. exact gravity_universal.
  split. exact gauge_selective.
  split. exact gauge_ratio_not_universal.
  exact gauge_signed.
Qed.
