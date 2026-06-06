(** * AntigravityCondition.v — metaphysics-hint ①: the STRUCTURE the framework gives for "antigravity".
       Gravity = Rule reads the trace-reversed source rho + 3p (not just energy rho); attraction <-> rho+3p>0,
       ANTIGRAVITY (repulsion) <-> rho+3p<0, achievable with negative pressure (tension).  The cosmological
       constant (p = -rho) IS antigravity.  This refines GravityRuleUniversality's gravity_no_screening
       (which was the pressureless rho>=0 case).

    WHAT THE REPO HAS (surveyed): cosmological-constant smallness (LambdaSmallnessDescent.v), vacuum energy
    (ProcessCosmologicalConst / cc_process).  GAP: NO effective source rho+3p, no energy condition, no
    attraction/repulsion (antigravity) condition.

    THE STRUCTURE (over Q, D=4).
      source(rho,p) = rho + 3p   (Raychaudhuri / Tolman: the geodesic-focusing source for a perfect fluid;
                                  the "3" = D-1 = the spatial Roles = the 3 rotations / gauge SU(2), H1').
      attracts   <-> source > 0;   antigravity <-> source < 0.
      Positive energy + non-negative pressure ALWAYS attracts (refines gravity_no_screening).
      ANTIGRAVITY requires tension: 3p < -rho  (p < -rho/3).
      Cosmological constant (equation of state p = -rho): source = -2 rho < 0  -> ANTIGRAVITY.
    The "mechanism that produces a gravitational field" = configuring the source; an antigravity mechanism
    = producing negative pressure (the vacuum / Lambda is the canonical instance).

    ============ E/R/R разбор ============
      Elements : энергия rho (содержание, P4: >=0) и давление p (как содержание НАПРЯЖЕНО по направлениям, может быть <0).
      Roles    : направления (пространственные Роли); p = напряжение содержания по Ролям.
      Rules    : гравитация (Правило) читает след-обращённый источник rho+3p; притяжение<->rho+3p>0, антигравитация<->rho+3p<0.
      ДИАГНОСТИКА: энергия всегда >=0 (P4), но давление — свободная конфигурация (натяжение). Антигравитация = достаточное
      отрицательное давление (p<-rho/3); Lambda/вакуум (p=-rho) = каноническая антигравитация. «Механизм g-поля» =
      конфигурация источника. Уточняет gravity_no_screening (частный случай p>=0). «3»=D-1=пространственные Роли=SU(2)
      (H1'). ЧЕСТНО: формализую УСЛОВИЕ (rho+3p<0<->отталкивание) и ИНСТАНС (Lambda), НЕ «устройство» и НЕ реализуемость
      произвольного отрицательного давления; не «доказываю антигравитацию реальной». Уровень: `новое обрамление известного`.

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The effective gravitational source rho + 3p, and attraction/repulsion  *)
(* ===================================================================== *)

(** The geodesic-focusing source (Raychaudhuri/Tolman), D=4: rho + 3p.
    The "3" = D-1 = the number of spatial Roles (= the 3 rotations / gauge SU(2), H1'). *)
Definition source (rho p : Q) : Q := rho + 3 * p.

Definition attracts    (rho p : Q) : Prop := 0 < source rho p.
Definition antigravity (rho p : Q) : Prop := source rho p < 0.

Lemma attracts_iff : forall rho p, attracts rho p <-> 0 < rho + 3 * p.
Proof. intros. unfold attracts, source. tauto. Qed.

Lemma antigravity_iff : forall rho p, antigravity rho p <-> rho + 3 * p < 0.
Proof. intros. unfold antigravity, source. tauto. Qed.

(** The "3" in rho+3p is D-1 = the spatial dimensions (= the 3 rotation / gauge generators, H1'). *)
Lemma three_is_spatial_dims : (4 - 1 = 3)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Equation of state p = w*rho ; the threshold w = -1/3                    *)
(* ===================================================================== *)

(** With p = w*rho the source is rho*(1+3w): the sign is set by w. *)
Lemma source_eos : forall rho w, source rho (w * rho) == rho * (1 + 3 * w).
Proof. intros. unfold source. ring. Qed.

(** The threshold w = -1/3 (p = -rho/3): zero net gravitational source. *)
Lemma threshold_zero : forall rho, source rho ((-(1#3)) * rho) == 0.
Proof. intros. unfold source. ring. Qed.

(* ===================================================================== *)
(*  Cases: dust / radiation attract ; the cosmological constant repels      *)
(* ===================================================================== *)

(** Dust (p = 0) attracts. *)
Lemma dust_attracts : forall rho, 0 < rho -> attracts rho 0.
Proof. intros rho H. unfold attracts, source. lra. Qed.

(** Radiation (p = rho/3, w = 1/3) attracts (source = 2 rho). *)
Lemma radiation_attracts : forall rho, 0 < rho -> attracts rho (rho * (1#3)).
Proof. intros rho H. unfold attracts, source. lra. Qed.

(** Positive energy + non-negative pressure ALWAYS attracts — refines gravity_no_screening. *)
Lemma positive_pressure_attracts : forall rho p,
  0 < rho -> 0 <= p -> attracts rho p.
Proof. intros rho p Hrho Hp. unfold attracts, source. lra. Qed.

(** ★ The cosmological constant / vacuum (p = -rho, w = -1): source = -2 rho < 0 = ANTIGRAVITY. *)
Lemma lambda_antigravity : forall rho, 0 < rho -> antigravity rho (- rho).
Proof. intros rho H. unfold antigravity, source. lra. Qed.

(* ===================================================================== *)
(*  The antigravity condition: tension (negative pressure)                 *)
(* ===================================================================== *)

(** ★ Antigravity REQUIRES tension: 3p < -rho (i.e. p < -rho/3) — the "mechanism" is negative pressure. *)
Lemma antigravity_needs_tension : forall rho p, antigravity rho p -> 3 * p < - rho.
Proof. intros rho p H. unfold antigravity, source in H. lra. Qed.

(** Antigravity is realizable: a positive-energy negative-pressure configuration exists (the vacuum / Lambda). *)
Lemma antigravity_realizable : exists rho p, 0 < rho /\ antigravity rho p.
Proof. exists 1, (-(1)). split; unfold antigravity, source; lra. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The structure the framework gives for antigravity:
      (def)        attracts <-> rho+3p>0 ; antigravity <-> rho+3p<0  (source = trace-reversed rho+3p);
      (dust)       dust (p=0) attracts;
      (pressure)   positive energy + non-negative pressure always attracts (refines gravity_no_screening);
      (tension)    antigravity requires negative pressure (3p < -rho);
      (Lambda)     the cosmological constant (p=-rho) IS antigravity (source = -2 rho < 0);
      (realizable) a positive-energy negative-pressure (antigravity) configuration exists.
    The "mechanism that produces a gravitational field" = configuring the source rho+3p; an antigravity
    mechanism = producing negative pressure.  (The CONDITION and an INSTANCE, not a device / a claim of
    physical realizability of arbitrary negative pressure.) *)
Theorem antigravity_structure :
  (forall rho p, attracts rho p <-> 0 < rho + 3 * p)
  /\ (forall rho p, antigravity rho p <-> rho + 3 * p < 0)
  /\ (forall rho, 0 < rho -> attracts rho 0)
  /\ (forall rho p, 0 < rho -> 0 <= p -> attracts rho p)
  /\ (forall rho p, antigravity rho p -> 3 * p < - rho)
  /\ (forall rho, 0 < rho -> antigravity rho (- rho))
  /\ (exists rho p, 0 < rho /\ antigravity rho p).
Proof.
  split. exact attracts_iff.
  split. exact antigravity_iff.
  split. exact dust_attracts.
  split. exact positive_pressure_attracts.
  split. exact antigravity_needs_tension.
  split. exact lambda_antigravity.
  exact antigravity_realizable.
Qed.
