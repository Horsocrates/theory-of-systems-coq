(** * VariationalEinsteinSourced.v — field-level lift, step 2: the SOURCED discrete Einstein equation
       (curvature = kappa * matter) as the stationary MINIMUM of the Regge+matter action; the variational
       principle read as L4 (sufficient reason) at the field level.

    WHAT THE REPO ALREADY HAS (surveyed): ProcessRegge.v (action S = sum deficit*area, "Regge = Einstein-
    Hilbert") and ProcessReggeVariation.v (dS/dl by finite differences; stationary & l>0 => deficit = 0,
    the VACUUM equation; the L4 -> Variational -> Einstein path).  GAP: there the matter coupling is
    zeroth-order (matter_action_derivative := 0, "higher order" deferred), so the SOURCED equation
    curvature = kappa*matter is NOT formalized, and there is no link to the "gravity = Rule" arc.

    WHAT THIS ADDS.  A kappa-scaled Regge+matter action  S(delta) = delta^2 - 2*kappa*m*delta  whose
    stationarity residual is  delta - kappa*m :
      - VACUUM  (m=0): stationary at delta = 0   (flat — recovers ProcessReggeVariation);
      - SOURCED (m<>0): stationary at delta = kappa*m  (CURVATURE = kappa*MATTER — the Rule responds to
                        the content; the case the repo deferred);
      - it is a genuine MINIMUM: S(delta) - S(kappa*m) = (delta - kappa*m)^2 >= 0 (completing the square).
    Read as L4: the actual geometry is the self-grounded extremum (no unspent variation).  This is the
    variational ORIGIN of the Rule=content matching (EinsteinRuleElementCoupling), now with a source.

    ============ E/R/R разбор ============
      Elements : дефицит delta (значение кривизны), масса m (содержание/источник в вершине).
      Roles    : варьируемая конфигурация геометрии (то, по чему берётся вариация).
      Rules    : действие S = Rule-содержание + связь с содержанием; уравнение поля delta=kappa*m =
                 Правило (кривизна) отвечает на содержание (материю).
      ДИАГНОСТИКА (L4): стационарность delta S=0 ЕСТЬ L4 (достаточное основание) на поле — актуальная
      геометрия самообоснована (нет неизрасходованной вариации); вакуум m=0=>delta=0, источник=>delta=kappa*m
      (НОВОЕ), подлинный минимум (квадрат>=0). Дно: L4 (актуальное=самообоснованный экстремум) + Правило=содержание.
      ЧЕСТНО: модельное квадратичное действие над Q, НЕ вывод полного действия ЭГ из геометрии. Уровень:
      `синтез+наблюдение` (сорсированное уравнение + L4-прочтение поверх существующего вакуумного Regge-слоя).

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The kappa-scaled Regge + matter action and its stationarity residual   *)
(* ===================================================================== *)

(** Action (kappa-scaled): S(delta) = delta^2 - 2*kappa*m*delta  (gravity ~ delta^2, matter ~ -m*delta). *)
Definition action (kappa m delta : Q) : Q := delta*delta - 2*kappa*m*delta.

(** Stationarity residual: dS/d(delta) = 2*(delta - kappa*m); the field equation is residual = 0. *)
Definition stationarity (kappa m delta : Q) : Q := delta - kappa*m.

(** The finite-difference derivative of the action is 2*stationarity (+ O(eps)) — as in ProcessReggeVariation. *)
Lemma action_finite_diff : forall kappa m delta eps,
  action kappa m (delta + eps) - action kappa m delta
  == 2*(delta - kappa*m)*eps + eps*eps.
Proof. intros. unfold action. ring. Qed.

(* ===================================================================== *)
(*  The field equation: stationary <-> delta = kappa*m  (curvature = kappa*matter) *)
(* ===================================================================== *)

(** ★ Stationarity IS the discrete Einstein equation: curvature delta = kappa * matter m. *)
Lemma field_equation : forall kappa m delta,
  stationarity kappa m delta == 0 <-> delta == kappa * m.
Proof. intros. unfold stationarity. split; intro H; lra. Qed.

(** VACUUM (m = 0): stationary at delta = 0 — flat space (recovers ProcessReggeVariation). *)
Lemma vacuum_flat : forall kappa, stationarity kappa 0 0 == 0.
Proof. intro kappa. unfold stationarity. ring. Qed.

(** ★ SOURCED (matter present): delta = kappa*m is stationary — curvature responds to content. *)
Lemma sourced_einstein : forall kappa m, stationarity kappa m (kappa*m) == 0.
Proof. intros. unfold stationarity. ring. Qed.

(* ===================================================================== *)
(*  It is a genuine MINIMUM (L4: the self-grounded extremum)               *)
(* ===================================================================== *)

Lemma q_sq_nonneg : forall a : Q, 0 <= a * a.
Proof.
  intro a. destruct (Qlt_le_dec a 0) as [Hlt | Hge].
  - assert (H : 0 < (- a) * (- a)) by (apply Qmult_lt_0_compat; lra).
    assert (Heq : (- a) * (- a) == a * a) by ring.
    rewrite Heq in H. lra.
  - destruct (Qlt_le_dec 0 a) as [Hlt0 | Hle0].
    + apply Qlt_le_weak. apply Qmult_lt_0_compat; assumption.
    + assert (Ha0 : a == 0) by (apply Qle_antisym; assumption).
      assert (Haa : a * a == 0) by (rewrite Ha0; ring).
      rewrite Haa. apply Qle_refl.
Qed.

(** Completing the square: S(delta) - S(kappa*m) = (delta - kappa*m)^2. *)
Lemma action_above_min : forall kappa m delta,
  action kappa m delta - action kappa m (kappa*m) == (delta - kappa*m) * (delta - kappa*m).
Proof. intros. unfold action. ring. Qed.

(** ★ The field-equation solution delta = kappa*m is the GLOBAL MINIMUM of the action (L4: self-grounded). *)
Lemma einstein_is_minimum : forall kappa m delta,
  action kappa m (kappa*m) <= action kappa m delta.
Proof.
  intros kappa m delta.
  assert (H := action_above_min kappa m delta).
  assert (Hsq := q_sq_nonneg (delta - kappa*m)).
  lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Variational origin of the sourced Einstein equation:
      (field eq)  stationarity <-> delta = kappa*m  (curvature = kappa*matter);
      (vacuum)    m = 0 => delta = 0 (flat — the repo's existing result);
      (sourced)   delta = kappa*m is stationary (the Rule responds to the content — the NEW case);
      (minimum)   delta = kappa*m globally minimizes the action (L4: the self-grounded extremum);
      (derivative) the finite-difference dS = 2*stationarity*eps + O(eps^2).
    The variational principle is L4 (sufficient reason) at the field level: the actual geometry is the
    one with no unspent variation; the field equation is the Rule (curvature) self-grounding against the
    content (matter). *)
Theorem variational_einstein :
  (forall kappa m delta, stationarity kappa m delta == 0 <-> delta == kappa * m)
  /\ (forall kappa, stationarity kappa 0 0 == 0)
  /\ (forall kappa m, stationarity kappa m (kappa*m) == 0)
  /\ (forall kappa m delta, action kappa m (kappa*m) <= action kappa m delta)
  /\ (forall kappa m delta eps,
        action kappa m (delta + eps) - action kappa m delta == 2*(delta - kappa*m)*eps + eps*eps).
Proof.
  split. exact field_equation.
  split. exact vacuum_flat.
  split. exact sourced_einstein.
  split. exact einstein_is_minimum.
  exact action_finite_diff.
Qed.
