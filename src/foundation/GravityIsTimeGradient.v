(** * GravityIsTimeGradient.v — the DIRECT gravity<->time link, walked from first principles:
       GRAVITY = THE GRADIENT OF THE RATE OF TIME.  Things fall toward where time runs slower; the rate of
       time = 1/(local distinction density K); the Newtonian potential = the time-rate deficit Phi ~ (1-rate)/2.

    THE CHAIN (where time and gravity are born, and how they connect).
      (Step 2-3) TIME = the irreversible succession of distinction-acts (L5 order + P4: S has no predecessor)
                 -> proper time = the stage-count (the "now"); irreversibility = ontological, not thermodynamic.
      (Step 4)   SPACE = reversible co-presence of Roles ; time = irreversible succession -> Lorentzian (-,+,+,+)
                 is the record of "succession =/= role-relation" (CausalSignature.v).
      (Step 4.5) PRIMITIVE GRAVITY = non-uniform distinction density (graph degree varies) ALREADY affects
                 time (EnergyDeterminesGraph.v: mass -> higher degree -> slower propagation -> time dilation).
      (Step 5)   METRIC = Sym^2(Roles) = GRAVITY (GravitySymSquareGauge.v).  Its g_00 component IS the rate of
                 proper time.  So gravity and the time-rate are ONE object; the rate is a COMPONENT of gravity.
      (Step 6)   GRAVITY (the falling tendency) = the VARIATION of the metric; in the weak field for slow
                 matter the dominant part is grad(g_00) = the gradient of the time-rate.  Objects fall toward
                 slower time.  Time-rate = c_eff = 1/K, K = local distinction density (PolarizableVacuumIndex.v).
      (Step 7)   EQUIVALENCE PRINCIPLE: content = distinctions = the source of the time-rate; the SAME field
                 phi (distinction depth) sets the clock rate AND is what content falls toward -> m_grav=m_inert.

    THIS FILE formalizes Step 6-7 (Element-side, weak field), reusing K = 1+2*phi from PolarizableVacuumIndex.v:
      time_rate(phi) = 1/K(phi) = clock rate (proper time per coordinate time);
      clocks run SLOWER deeper in the well (clock_slower_deeper); the gravitational pull = the DROP in time-rate
      going inward (grav_pull > 0, = time_rate(far) - time_rate(near)) = the discrete gradient of the time-rate;
      the Newtonian-potential identity 1 - time_rate = 2*phi*time_rate (weak field ~ 2*phi = 2x potential);
      rate * density = 1 (the clock rate IS the reciprocal of the local distinction density).

    INSIGHT (what the ToS methodology adds).  KNOWN: in the weak field gravity ~ curvature of TIME
    (Phi = (g_00 - 1)/2; clocks slow near mass) -- standard GR.  NEW (ToS framing): WHY g_00 varies is DERIVED
    -- g_00 = the time-rate = 1/(distinction density), and mass = distinction density; and the equivalence
    principle becomes structural (one field phi, two roles: it sets the clock rate AND drives the fall).

    HONEST SCOPE.  Weak-field, slow-matter, scalar Element-side picture (the role-limit is the full nonlinear
    metric).  "Gravity = curvature of time" is the standard weak-field statement; the new content is the
    ontological derivation (time-rate = 1/distinction-density) and the equivalence-principle structure.  NOT
    full tensor GR; NOT a claim beyond the weak field.

    Elements: time_rate(phi), the distinction density K=vac_index(phi), the potential depth phi.
    Roles:    time_rate = proper-clock rate ; K = local distinction density (= graph degree) ; phi = depth/source.
    Rules:    time_rate = 1/K ; clocks slower where K higher ; gravity (pull) = the gradient (drop) of time_rate.

    ============ E/R/R разбор ============
      Elements (L1): скорость времени time_rate(phi), плотность различений K=vac_index(phi), глубина phi.
      Roles    (L4): time_rate = ход собственных часов; K = локальная плотность различений (= степень графа);
                     phi = глубина/источник (= ньютонов потенциал).
      Rules    (L5): time_rate = 1/K; часы медленнее там, где K выше; гравитация (тяга) = градиент (падение)
                     скорости времени; падение = к более медленному времени = к большей плотности различений.
      ДИАГНОСТИКА (P4): время (преемство) ПРИМИТИВНЕЕ гравитации (метрики); метрика Sym^2(Roles) уже СОДЕРЖИТ
      скорость времени как g_00 -> связь = вложенность, не взаимодействие. ПЭ: один источник phi -- две роли
      (задаёт такт И влечёт падение) -> m_grav=m_inert. ЧЕСТНО: слабое поле, скалярная Element-сторона; «грав.
      = кривизна времени» -- стандарт; ново -- вывод «скорость времени = 1/плотность-различений» + структурный ПЭ.
      Уровень: `новое обрамление / синтез`.

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only; K replicated from PolarizableVacuumIndex.v)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Setoid.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The local distinction density K, the clock rate, the potential        *)
(* ===================================================================== *)

(** Local distinction density K = 1 + 2*phi (weak-field; = graph degree, EnergyDeterminesGraph.v;
    replicated from PolarizableVacuumIndex.v). *)
Definition vac_index (phi : Q) : Q := 1 + 2 * phi.

(** The rate of proper time = c_eff = 1/K : proper time per unit coordinate time (the clock rate). *)
Definition time_rate (phi : Q) : Q := 1 / vac_index phi.

(** The Newtonian potential DEPTH phi = GM/r (>=0, larger nearer the mass). *)
Definition grav_potential (phi : Q) : Q := phi.

(** Gravitational PULL between a near (deep) and a far (shallow) shell = the DROP in time-rate going inward. *)
Definition grav_pull (phi_near phi_far : Q) : Q := time_rate phi_far - time_rate phi_near.

(* ===================================================================== *)
(*  Index basics                                                          *)
(* ===================================================================== *)

Lemma index_pos : forall phi, 0 <= phi -> 0 < vac_index phi.
Proof. intros phi H. unfold vac_index. lra. Qed.

Lemma index_increasing : forall p1 p2, p1 < p2 -> vac_index p1 < vac_index p2.
Proof. intros p1 p2 H. unfold vac_index. lra. Qed.

(** Reciprocal is antitone on the positives: a < b (both > 0) => 1/b < 1/a. *)
Lemma Qinv_antitone : forall a b : Q, 0 < a -> a < b -> 1 / b < 1 / a.
Proof.
  intros a b Ha Hab. assert (Hb : 0 < b) by lra.
  apply Qlt_shift_div_r; [ exact Hb | ].
  setoid_replace (1 / a * b) with (b / a) by (field; lra).
  apply Qlt_shift_div_l; [ exact Ha | ].
  rewrite Qmult_1_l. exact Hab.
Qed.

(* ===================================================================== *)
(*  The rate of time IS the reciprocal of the distinction density          *)
(* ===================================================================== *)

(** * rate * density = 1 : the clock rate is exactly 1/(local distinction density). *)
Lemma rate_times_density : forall phi, 0 <= phi -> time_rate phi * vac_index phi == 1.
Proof.
  intros phi H. unfold time_rate, vac_index. field. lra.
Qed.

(* ===================================================================== *)
(*  Clocks run slower deeper; the Newtonian potential = the time-deficit   *)
(* ===================================================================== *)

(** * Deeper in the well (higher phi, nearer the mass) the clock runs SLOWER. *)
Lemma clock_slower_deeper :
  forall p1 p2, 0 <= p1 -> p1 < p2 -> time_rate p2 < time_rate p1.
Proof.
  intros p1 p2 H1 H12. unfold time_rate.
  apply Qinv_antitone; [ apply index_pos; exact H1 | apply index_increasing; exact H12 ].
Qed.

(** * The Newtonian potential = the time-rate DEFICIT: 1 - time_rate = 2*phi*time_rate
    (weak field, time_rate ~ 1, gives 1 - time_rate ~ 2*phi = twice the potential depth). *)
Lemma time_rate_deficit :
  forall phi, 0 <= phi -> 1 - time_rate phi == 2 * grav_potential phi * time_rate phi.
Proof.
  intros phi H. unfold time_rate, grav_potential, vac_index. field. lra.
Qed.

(* ===================================================================== *)
(*  GRAVITY = the gradient (drop) of the time-rate; fall toward slower time *)
(* ===================================================================== *)

(** * The gravitational pull is POSITIVE toward the nearer (deeper, slower-time) shell:
    content falls toward where time runs slower.  grav_pull = the discrete gradient of the time-rate. *)
Lemma grav_pull_positive :
  forall phi_near phi_far,
    0 <= phi_far -> phi_far < phi_near -> 0 < grav_pull phi_near phi_far.
Proof.
  intros pn pf Hf Hlt. unfold grav_pull.
  assert (time_rate pn < time_rate pf) by (apply clock_slower_deeper; [ exact Hf | exact Hlt ]).
  lra.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** Gravity is the gradient of the rate of time:
      (rate=1/density)  time_rate * K = 1 -- the clock rate IS the reciprocal of the distinction density;
      (slower deeper)   deeper in the well the clock runs slower (time_rate p2 < time_rate p1 for p1<p2);
      (Newton=deficit)  1 - time_rate = 2*phi*time_rate -- the potential is the time-rate deficit (~2*phi);
      (fall to slow)    the gravitational pull > 0 toward the slower-time (deeper) shell;
      (pull=gradient)   that pull IS the difference of time-rates -- gravity = the gradient of the time-rate.
    Time (succession) is primitive; the metric (gravity) contains the time-rate as g_00; gravity, as a
    falling tendency, is the gradient of that time-rate.  Objects fall toward slower time = denser distinction. *)
Theorem gravity_is_time_gradient :
  (forall phi, 0 <= phi -> time_rate phi * vac_index phi == 1)
  /\ (forall p1 p2, 0 <= p1 -> p1 < p2 -> time_rate p2 < time_rate p1)
  /\ (forall phi, 0 <= phi -> 1 - time_rate phi == 2 * grav_potential phi * time_rate phi)
  /\ (forall pn pf, 0 <= pf -> pf < pn -> 0 < grav_pull pn pf)
  /\ (forall pn pf, grav_pull pn pf == time_rate pf - time_rate pn).
Proof.
  split; [ exact rate_times_density | ].
  split; [ exact clock_slower_deeper | ].
  split; [ exact time_rate_deficit | ].
  split; [ exact grav_pull_positive | ].
  intros pn pf. unfold grav_pull. reflexivity.
Qed.
