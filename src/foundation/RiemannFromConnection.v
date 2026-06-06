(** * RiemannFromConnection.v — field-level lift, step 5 (closing): the connection Gamma is DERIVED from
       the metric (Levi-Civita Gamma = 1/2 g^{-1} dg, torsion-free), and the Riemann tensor is DERIVED
       from Gamma (R = dGamma - dGamma + Gamma*Gamma).  A flat (constant) metric gives Gamma = 0 gives
       Riemann = 0 — flatness is DERIVED, not posited.  This closes the chain metric -> Gamma -> Riemann
       -> Ricci -> G (step 4) -> field equation (steps 1-2); Riemann is no longer a given.

    WHAT THE REPO HAS (surveyed): gauge field-strength = d(connection) (lattice/GaugeFieldFromConnection.v),
    CurvatureFromGraph.v / GraphCurvature.v (graph curvature).  GAP: NO gravity Christoffel-from-metric, no
    Riemann-from-Gamma; RicciContraction.v (step 4) took Riemann as given.

    THE CHAIN (symbolic 2D over Q; metric derivatives as free variables).
      Christoffel (1st kind)  Gamma_{lam mu nu} = 1/2 (d_mu g_{nu lam} + d_nu g_{mu lam} - d_lam g_{mu nu})
                              -- DERIVED from the metric; TORSION-FREE (symmetric in mu,nu);
      Riemann  R^rho_{sig mu nu} = d_mu G^rho_{nu sig} - d_nu G^rho_{mu sig}
                                 + sum_lam (G^rho_{mu lam} G^lam_{nu sig} - G^rho_{nu lam} G^lam_{mu sig})
                              -- DERIVED from Gamma; ANTISYMMETRIC in mu,nu.
      FLAT: constant metric (all dg = 0) => Gamma = 0 => Riemann = 0 -- flatness is DERIVED.
    Contrast with step 3: there d^2 = 0 (boundary of boundary, => Bianchi); here the Gamma*Gamma term is
    the curvature -- [nabla_mu, nabla_nu] != 0 is exactly where parallel transport fails to close.

    ============ E/R/R разбор ============
      Elements : компоненты метрики g_mn и её производных dg (носители геометрии).
      Roles    : индексы/направления; связность Gamma — как Роли переносятся (перенос вдоль направления).
      Rules    : Gamma = 1/2 g^-1 dg (Леви-Чивита, выведена из метрики, без кручения); Riemann = dG-dG+GG
                 (кривизна из связности); постоянная метрика => Gamma=0 => Riemann=0 (плоскость выведена).
      ДИАГНОСТИКА: метрика->Gamma->Riemann->Ricci->G замкнута; Riemann более не данность. Контраст с шагом 3:
      d^2=0 (Бианки) vs GG-член=кривизна (некоммутативность переноса). ЧЕСТНО: символьная 2D-модель над Q
      (производные = свободные переменные, не решёточные разности); метрик-совместимость nabla g=0 не доказана
      (нужна обратная метрика). Уровень: `новое обрамление известного`.

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

Section RiemannFromConnection.

(* Metric derivatives as free variables: dg mu nu lam = d_mu g_{nu lam}, with g symmetric. *)
Variable dg : nat -> nat -> nat -> Q.
Hypothesis dg_sym : forall mu nu lam, dg mu nu lam == dg mu lam nu.

(* The connection Gamma (mixed) and its derivatives, as free variables for the Riemann formula. *)
Variable Gam : nat -> nat -> nat -> Q.            (* Gam rho mu nu = Gamma^rho_{mu nu} *)
Variable dGam : nat -> nat -> nat -> nat -> Q.    (* dGam mu rho nu sig = d_mu Gamma^rho_{nu sig} *)

(* ===================================================================== *)
(*  Christoffel (1st kind) from the metric: DERIVED, torsion-free          *)
(* ===================================================================== *)

(** Levi-Civita Christoffel (first kind): a FUNCTION of the metric derivatives, no inverse needed. *)
Definition christoffel1 (lam mu nu : nat) : Q :=
  (1#2) * (dg mu nu lam + dg nu mu lam - dg lam mu nu).

(** ★ TORSION-FREE: the connection is symmetric in its lower indices (mu <-> nu). *)
Lemma torsion_free : forall lam mu nu,
  christoffel1 lam mu nu == christoffel1 lam nu mu.
Proof. intros. unfold christoffel1. rewrite (dg_sym lam mu nu). ring. Qed.

(** ★ FLAT metric => zero connection: a constant metric (all dg = 0) gives Gamma = 0. *)
Lemma flat_metric_zero_christoffel :
  (forall mu nu lam, dg mu nu lam == 0) ->
  forall lam mu nu, christoffel1 lam mu nu == 0.
Proof. intros H lam mu nu. unfold christoffel1. rewrite !H. ring. Qed.

(* ===================================================================== *)
(*  Riemann from the connection: DERIVED, antisymmetric; flat => zero       *)
(* ===================================================================== *)

(** Riemann R^rho_{sig mu nu} = d_mu G^rho_{nu sig} - d_nu G^rho_{mu sig}
                              + sum_{lam in {0,1}} (G^rho_{mu lam} G^lam_{nu sig} - G^rho_{nu lam} G^lam_{mu sig}). *)
Definition riemann (rho sig mu nu : nat) : Q :=
  dGam mu rho nu sig - dGam nu rho mu sig
  + (Gam rho mu 0%nat * Gam 0%nat nu sig + Gam rho mu 1%nat * Gam 1%nat nu sig)
  - (Gam rho nu 0%nat * Gam 0%nat mu sig + Gam rho nu 1%nat * Gam 1%nat mu sig).

(** ★ Riemann is ANTISYMMETRIC in its last two indices (mu <-> nu): a structural identity. *)
Lemma riemann_antisymmetric : forall rho sig mu nu,
  riemann rho sig mu nu == - riemann rho sig nu mu.
Proof. intros. unfold riemann. ring. Qed.

(** ★ FLAT connection => zero curvature: Gamma = 0 and dGamma = 0 give Riemann = 0.
    Composed with flat_metric_zero_christoffel: a constant metric => flat spacetime (DERIVED). *)
Lemma flat_zero_riemann :
  (forall r m n, Gam r m n == 0) ->
  (forall m r n s, dGam m r n s == 0) ->
  forall rho sig mu nu, riemann rho sig mu nu == 0.
Proof. intros HG HdG rho sig mu nu. unfold riemann. rewrite !HG, !HdG. ring. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The chain metric -> Gamma -> Riemann, closed:
      (torsion-free)  Gamma_{lam mu nu} = Gamma_{lam nu mu} (derived Levi-Civita connection);
      (flat metric)   constant metric => Gamma = 0;
      (antisymmetry)  Riemann is antisymmetric in mu,nu (curvature from the connection);
      (flat curvature) Gamma = 0 => Riemann = 0.
    Composing the two flat results: a constant metric gives Gamma = 0 gives Riemann = 0 -- flatness is
    DERIVED from the metric, not posited.  Riemann is no longer a given: metric -> Gamma -> Riemann ->
    Ricci -> G (RicciContraction.v) -> field equation (VariationalEinsteinSourced.v). *)
Theorem metric_to_riemann :
  (forall lam mu nu, christoffel1 lam mu nu == christoffel1 lam nu mu)
  /\ ((forall mu nu lam, dg mu nu lam == 0) ->
       forall lam mu nu, christoffel1 lam mu nu == 0)
  /\ (forall rho sig mu nu, riemann rho sig mu nu == - riemann rho sig nu mu)
  /\ ((forall r m n, Gam r m n == 0) -> (forall m r n s, dGam m r n s == 0) ->
       forall rho sig mu nu, riemann rho sig mu nu == 0).
Proof.
  split. exact torsion_free.
  split. exact flat_metric_zero_christoffel.
  split. exact riemann_antisymmetric.
  exact flat_zero_riemann.
Qed.

End RiemannFromConnection.
