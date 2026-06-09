(** * PolarizableVacuumIndex.v — the optical / refractive-index picture of gravity as a variable
       DISTINCTION-DENSITY field, bridging Puthoff's polarizable-vacuum (PV) model of GR to the ToS
       graph-density gravity already in EnergyDeterminesGraph.v / CurvatureFromGraph.v.

    THE HINT (Puthoff 2002, "Polarizable-vacuum approach to GR", Found. Phys. 32:927; after Dicke).
      Gravity is re-described as a vacuum with a variable refractive index K(x): the speed of light is
      c = c0/K, K is higher near mass, so light slows and bends TOWARD the mass, and clocks deeper in the
      well (higher K) run slower (gravitational redshift).  K = exp(2*phi) for the potential depth phi
      (c=1); the model reproduces the classic WEAK-FIELD tests (redshift, light bending, perihelion).

    WHY IT IS A ToS HINT (genuine convergence, not a stretch).
      EnergyDeterminesGraph.v already says: "mass raises the local graph degree -> slower propagation ->
      gravitational time dilation."  That IS a discrete polarizable vacuum: local graph degree = local
      refractive index K = local distinction density.  This file makes the bridge explicit: the PV index K
      is the ToS local distinction/graph density; propagation_time ∝ K (∝ degree); the K-dependent clock
      rate is the proper_time of ObserverSystemTime.v (slower where K is higher).

    WEAK-FIELD ELEMENT-SIDE.  We formalize the rational, weak-field linearization K(phi) = 1 + 2*phi
    (the Element-side truncation; the full nonlinear K = exp(2*phi) is the role-limit, a Cauchy process).
    The linear term 2*phi IS twice the Newtonian potential — the leading metric correction.

    HONEST SCOPE.  PV is a SCALAR heuristic (Puthoff's own words: "a heuristic tool to provide insight"),
    equivalent to GR only in the WEAK field; it is NOT full tensor GR (no strong-field / gravitational-wave
    polarization / frame-dragging content).  This file formalizes the optical re-description of ORDINARY
    gravity and its convergence with ToS graph-density gravity.  It is NOT an endorsement of "metric
    engineering" / propulsion / UAP claims — those are speculative extrapolations (needing exotic negative
    energy, the Alcubierre barrier) and outside what this mathematics asserts.

    Elements: the index value K(phi), c_eff, the potential depth phi, the local graph degree.
    Roles:    K = medium role (refractive index / vacuum polarizability / graph degree) ; c_eff = speed ;
              phi = potential depth (source) ; the K-dependent clock = proper-time role.
    Rules:    K = 1+2*phi (weak field; exp(2*phi) role-limit) ; c_eff = 1/K ; index↑ near mass ⟹ light
              slows, bends toward mass, deep clocks dilate (redshift).

    ============ E/R/R разбор ============
      Elements (L1): значение индекса K(phi), c_eff, глубина phi, локальная степень графа. Носитель —
                     локальный индекс = локальная плотность различений.
      Roles    (L4): K = роль среды (показатель преломления / поляризуемость / степень графа); c_eff =
                     скорость; phi = глубина (источник); K-зависимые часы = собственное время.
      Rules    (L5): K=1+2*phi (слабое поле; exp(2*phi) role-limit); c_eff=1/K; индекс↑ у массы ⟹ свет
                     медленнее, гнётся к массе, глубокие часы замедляются (красное смещение).
      ДИАГНОСТИКА (P4): Element-сторона (рациональная, слабое поле); полный exp(2*phi) = role-limit.
      Мост EnergyDeterminesGraph (степень=индекс) ↔ ObserverSystemTime (ход часов=собственное время).
      ЧЕСТНО: скалярный эвристический приём, ТОЛЬКО слабое поле, не полная ОТО; НЕ одобрение двигателей/НЛО
      (спекуляция, требует экзотической энергии). Уровень: мост (PV ↔ ToS-граф-гравитация).

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The vacuum index K(phi) and the effective light speed                  *)
(* ===================================================================== *)

(** Weak-field vacuum refractive index (Element-side linearization of K = exp(2*phi); c=1).
    phi >= 0 is the gravitational potential DEPTH (phi = GM/r for a point mass; phi -> 0 far away). *)
Definition vac_index (phi : Q) : Q := 1 + 2 * phi.

(** Effective speed of light in the medium: c = c0 / K  (c0 = 1). *)
Definition c_eff (phi : Q) : Q := 1 / vac_index phi.

(** Propagation time per step ∝ K  (= the local graph degree of EnergyDeterminesGraph.v;
    also the local clock PERIOD = proper-time per tick of ObserverSystemTime.v). *)
Definition propagation_time (phi : Q) : Q := vac_index phi.

(** Gravitational redshift factor: ratio of indices between emission (deep) and observation (shallow). *)
Definition redshift_ratio (phi_emit phi_obs : Q) : Q := vac_index phi_emit / vac_index phi_obs.

(* ===================================================================== *)
(*  Index basics: =1 in vacuum, >=1, higher and positive near mass         *)
(* ===================================================================== *)

(** Far from any mass (phi=0) the index is 1 — flat space, c = c0. *)
Theorem index_vacuum : vac_index 0 == 1.
Proof. unfold vac_index. ring. Qed.

(** The index is at least 1 everywhere (the vacuum never speeds light up). *)
Theorem index_ge_one : forall phi, 0 <= phi -> 1 <= vac_index phi.
Proof. intros phi H. unfold vac_index. lra. Qed.

(** * Deeper in the well = higher index (vacuum polarizes more near mass). *)
Theorem index_increasing : forall p1 p2, p1 < p2 -> vac_index p1 < vac_index p2.
Proof. intros p1 p2 H. unfold vac_index. lra. Qed.

Theorem index_pos : forall phi, 0 <= phi -> 0 < vac_index phi.
Proof. intros phi H. unfold vac_index. lra. Qed.

(** The deviation of the index from flat is exactly twice the Newtonian potential (the weak-field term). *)
Theorem index_minus_newtonian : forall phi, vac_index phi - 1 == 2 * phi.
Proof. intro phi. unfold vac_index. ring. Qed.

(* ===================================================================== *)
(*  Light slows / clocks dilate near mass (propagation_time ∝ index)       *)
(* ===================================================================== *)

(** * Light SLOWS and clocks DILATE deeper in the well: propagation time per step grows with the index
    (∝ local graph degree).  This is the division-free statement of "c_eff decreases near mass". *)
Theorem propagation_slows_deeper :
  forall p1 p2, p1 < p2 -> propagation_time p1 < propagation_time p2.
Proof. intros p1 p2 H. unfold propagation_time. apply index_increasing; exact H. Qed.

(** In vacuum the effective speed is exactly c0 = 1. *)
Theorem c_eff_vacuum : c_eff 0 == 1.
Proof. unfold c_eff, vac_index. vm_compute. reflexivity. Qed.

(** * Light is never superluminal: c_eff = 1/K <= 1 (= 1 only in vacuum). *)
Theorem c_eff_not_superluminal : forall phi, 0 <= phi -> c_eff phi <= 1.
Proof.
  intros phi H. unfold c_eff.
  apply Qle_shift_div_r.
  - apply index_pos; exact H.
  - rewrite Qmult_1_l. apply index_ge_one; exact H.
Qed.

(* ===================================================================== *)
(*  Light bends toward mass; deeper sources are redshifted                 *)
(* ===================================================================== *)

(** * Light bends TOWARD the mass: the index is higher on the near (deeper) side, so by Fermat's
    principle rays curve into the region of higher index. *)
Theorem bending_toward_mass :
  forall phi_far phi_near, phi_far < phi_near -> vac_index phi_far < vac_index phi_near.
Proof. intros pf pn H. apply index_increasing; exact H. Qed.

(** * Gravitational redshift: light emitted DEEPER (higher phi) and observed SHALLOWER is redshifted —
    the index ratio exceeds 1. *)
Theorem redshift_when_deeper :
  forall phi_emit phi_obs,
    0 <= phi_obs -> phi_obs < phi_emit -> 1 < redshift_ratio phi_emit phi_obs.
Proof.
  intros pe po Hpo Hlt. unfold redshift_ratio.
  apply Qlt_shift_div_l.
  - apply index_pos; exact Hpo.
  - rewrite Qmult_1_l. apply index_increasing; exact Hlt.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** The polarizable-vacuum / refractive-index picture of gravity, Element-side (weak field):
      (vacuum)     index = 1 far from mass (flat space, c = c0);
      (>= 1)       the index is at least 1 everywhere — never superluminal;
      (near mass)  the index rises toward mass (light slows, clocks dilate, propagation_time grows);
      (no SL)      c_eff = 1/K <= 1;
      (redshift)   light emitted deeper is redshifted (index ratio > 1);
      (Newtonian)  the index's deviation from flat is exactly 2*phi (the weak-field metric correction).
    Gravity = a variable distinction-density (refractive-index) field; this is the optical re-description
    of ORDINARY gravity, converging with the ToS graph-density gravity (EnergyDeterminesGraph.v: degree =
    index) and the proper-time clock of ObserverSystemTime.v.  Weak-field scalar heuristic, not full GR. *)
Theorem polarizable_vacuum_index :
  vac_index 0 == 1
  /\ (forall phi, 0 <= phi -> 1 <= vac_index phi)
  /\ (forall p1 p2, p1 < p2 -> vac_index p1 < vac_index p2)
  /\ (forall phi, 0 <= phi -> c_eff phi <= 1)
  /\ (forall pe po, 0 <= po -> po < pe -> 1 < redshift_ratio pe po)
  /\ (forall phi, vac_index phi - 1 == 2 * phi).
Proof.
  split; [ exact index_vacuum | ].
  split; [ exact index_ge_one | ].
  split; [ exact index_increasing | ].
  split; [ exact c_eff_not_superluminal | ].
  split; [ exact redshift_when_deeper | ].
  exact index_minus_newtonian.
Qed.
