(** * LambdaRunningVacuumBound.v — deepening the TESTABLE side of the stage-count law, and confronting it
       with data.  The law Lambda/M_P^4 = c/K^2 (LambdaSmallnessExponent.v, LambdaStageBridge.v), read
       DYNAMICALLY (K = M_P/H at each epoch, so Lambda ∝ H^2), is a running-vacuum model with an O(1)
       coefficient.  This file shows — honestly — that the clean dynamical reading is REFUTED by data,
       and only the (non-distinguishing) SNAPSHOT reading survives.  Empirical discipline, à la
       NatureBoundaryLedger.v (where Fermi-LAT refuted the regular lattice).

    TWO READINGS of  Lambda/M_P^4 = c / K_cosmo^2  (K_cosmo = M_P/H).
      SNAPSHOT  : a present-epoch relation — Lambda is (today) ~ c (H0/M_P)^2 ~ 10^-122.  Reproduces the
                  observed value, but is just the standard coincidence Lambda ~ H0^2 — NOT a distinguishing
                  prediction, indistinguishable from a constant Lambda (LCDM).
      DYNAMICAL : a law at ALL epochs — Lambda(H) = c H^2 M_P^2 (vacuum tracks H^2).  This is a running-
                  vacuum model (RVM) with coefficient nu ~ O(1) (the vacuum is ENTIRELY the H^2 term; no
                  constant piece), i.e. nu = 1.  A SHARP, falsifiable prediction.

    THE CONFRONTATION (why the dynamical reading is refuted).
      (1) RVM bound.  CMB+BAO+SNe fits constrain the H^2-running coefficient to |nu| <~ 10^-3.  The
          framework's clean reading gives nu ~ O(1) (=1) — too big by ~3 orders.
      (2) Omega clash (stronger).  Lambda ∝ H^2 and (Friedmann) rho_crit ∝ H^2 ⇒ Omega_Lambda =
          Lambda/rho_crit is EPOCH-INDEPENDENT (a constant).  But the observed Omega_Lambda EVOLVES:
          ~10^-9 at recombination, ~0.7 today.  A constant cannot match both.  Matched to today (0.7),
          the dynamical law predicts Omega_Lambda = 0.7 at recombination, where it was ~10^-9.  Refuted.

    VERDICT (honest).  Empirical discipline selects the SNAPSHOT reading (Consistent: reproduces Lambda~H0^2)
      and REFUTES the DYNAMICAL reading (the clean, distinguishing one).  So the stage-count law, as a
      present-value statement, survives but predicts nothing new; as a dynamical law it is falsified.
      ESCAPE HATCH (open): a SUPPRESSED coefficient nu <~ 10^-3 would survive — but the framework derives
      nu ~ O(1), so saving it needs structure NOT present here.  This is a refutation that disciplines the
      theory, NOT a confirmation.

    Elements: the vacuum fraction Omega_Lambda (a ratio) ; coefficient nu ; observational anchors.
    Roles:    nu = vacuum fraction (constant under the dynamical law) ; Omega_obs = observed evolution ;
              the bound = the refuting ceiling ; two readings = {Snapshot (consistent), Dynamical (refuted)}.
    Rules:    Lambda ∝ H^2 ⇒ Omega = const (H^2 cancels) ; observed Omega evolves ⇒ clash ; nu=1 ≫ 10^-3.

    ============ E/R/R разбор ============
      Elements (L1): доля вакуума Omega_Lambda, коэффициент nu, якоря (Omega~10^-9 рекомб., ~0.7 сейчас,
                     RVM-граница ~10^-3). Носитель — безразмерная доля/коэффициент.
      Roles    (L4): nu = «доля вакуума» (константа при динамич. законе); Omega_obs = эволюция;
                     граница = опровергающий потолок; прочтения {Snapshot=согласовано, Dynamical=опровергнуто}.
      Rules    (L5): Lambda∝H^2 ⇒ Omega=const (H^2 сокращается); наблюдаемое Omega эволюционирует ⇒ клэш;
                     nu_рамки=1 ≫ 10^-3=граница ⇒ превышено. Эмпирика ОПРОВЕРГАЕТ динамич. прочтение.
      ДИАГНОСТИКА (P4): та же дисциплина, что NatureBoundaryLedger.v (Fermi-LAT опроверг решётку). Чистое
      предсказание ФАЛЬСИФИЦИРОВАНО; честный вердикт — выживает неотличимый snapshot. Escape (крошечное nu)
      требует структуры, которой в рамке нет. Уровень: «честная конфронтация / эмпирическая дисциплина».

    ERROR LOCATED (see LambdaLevelInversionError.v): the refutation here is correct, and the underlying error
    is a LEVEL-INVERSION — rho_Lambda (an Element) was slaved to H^2 (the aggregate Rule), ERASING the
    vacuum's Role w=-1 (p=-rho, PROVEN in VacuumIsAntigravity.v).  Restoring w=-1 gives rho_Lambda=const and an
    EVOLVING Omega_Lambda (matches data); the smallness then returns to the free-magnitude value-wall.

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The running-vacuum coefficient vs the observational bound              *)
(* ===================================================================== *)

(** The framework's clean reading: the vacuum is ENTIRELY the H^2 term ⇒ coefficient nu ~ O(1) (=1). *)
Definition nu_framework : Q := 1.

(** CMB+BAO+SNe bound on the H^2-running coefficient: |nu| <~ 10^-3. *)
Definition nu_obs_max : Q := 1 # 1000.

(** * The framework's coefficient EXCEEDS the observational bound (by ~3 orders): nu=1 vs ~10^-3. *)
Theorem framework_nu_exceeds_bound : nu_obs_max < nu_framework.
Proof. unfold nu_obs_max, nu_framework. lra. Qed.

(* ===================================================================== *)
(*  The Omega clash: Lambda ∝ H^2 ⇒ Omega_Lambda is epoch-INDEPENDENT      *)
(* ===================================================================== *)

(** Critical density (Friedmann): rho_crit = (3/8pi) M_P^2 H^2 ; here k = (3/8pi)M_P^2 is an O(1)>0 scale. *)
Definition rho_crit (k H : Q) : Q := k * (H * H).

(** Dynamical vacuum density: rho_Lambda = nu * rho_crit = nu k H^2 (vacuum tracks H^2). *)
Definition rho_lambda_dyn (nu k H : Q) : Q := nu * (k * (H * H)).

(** The vacuum fraction Omega_Lambda = rho_Lambda / rho_crit. *)
Definition Omega_dyn (nu k H : Q) : Q := rho_lambda_dyn nu k H / rho_crit k H.

Lemma denom_nz : forall k H : Q, ~ (k == 0) -> ~ (H == 0) -> ~ (k * (H * H) == 0).
Proof.
  intros k H Hk HH C.
  destruct (Qmult_integral _ _ C) as [Hk0 | HH0].
  - apply Hk; exact Hk0.
  - destruct (Qmult_integral _ _ HH0) as [H0 | H0]; apply HH; exact H0.
Qed.

(** * The H^2 in numerator and denominator CANCEL: Omega_Lambda = nu, independent of H (the epoch). *)
Theorem omega_dyn_eq_nu :
  forall nu k H : Q, ~ (k == 0) -> ~ (H == 0) -> Omega_dyn nu k H == nu.
Proof.
  intros nu k H Hk HH.
  unfold Omega_dyn, rho_lambda_dyn, rho_crit, Qdiv.
  rewrite <- Qmult_assoc.
  rewrite Qmult_inv_r by (apply denom_nz; assumption).
  ring.
Qed.

(** * Hence under the dynamical law Omega_Lambda is EPOCH-INDEPENDENT (the same constant at every H). *)
Theorem omega_dyn_constant :
  forall nu k H1 H2 : Q,
    ~ (k == 0) -> ~ (H1 == 0) -> ~ (H2 == 0) ->
    Omega_dyn nu k H1 == Omega_dyn nu k H2.
Proof.
  intros nu k H1 H2 Hk H1nz H2nz.
  rewrite (omega_dyn_eq_nu nu k H1 Hk H1nz).
  rewrite (omega_dyn_eq_nu nu k H2 Hk H2nz).
  reflexivity.
Qed.

(* ===================================================================== *)
(*  ...but the OBSERVED Omega_Lambda evolves — so the constant is refuted  *)
(* ===================================================================== *)

(** Observed vacuum fraction at recombination (z~1100): utterly negligible, ~10^-9. *)
Definition Omega_obs_recomb : Q := 1 # 1000000000.
(** Observed vacuum fraction today: ~0.7. *)
Definition Omega_obs_now : Q := 7 # 10.

(** * The observed Omega_Lambda EVOLVES (recombination value /= today's value). *)
Theorem observed_omega_evolves : ~ (Omega_obs_recomb == Omega_obs_now).
Proof. unfold Omega_obs_recomb, Omega_obs_now. intro H. vm_compute in H. discriminate H. Qed.

(** * THE CLASH: matched to today (nu = 0.7), the dynamical law predicts Omega_Lambda = 0.7 at
    recombination — where it was observed to be ~10^-9.  The dynamical reading is refuted. *)
Theorem refuted_at_recombination :
  Omega_dyn (7 # 10) 1 1 == (7 # 10) /\ ~ (Omega_dyn (7 # 10) 1 1 == Omega_obs_recomb).
Proof.
  split.
  - unfold Omega_dyn, rho_lambda_dyn, rho_crit. vm_compute. reflexivity.
  - unfold Omega_dyn, rho_lambda_dyn, rho_crit, Omega_obs_recomb.
    intro H. vm_compute in H. discriminate H.
Qed.

(* ===================================================================== *)
(*  Verdict: snapshot survives, dynamical refuted (empirical discipline)   *)
(* ===================================================================== *)

Inductive Reading := Snapshot | Dynamical.
Inductive Verdict := Consistent | Refuted.

(** Snapshot (present-value) reproduces Lambda~H0^2 (consistent, non-distinguishing); the dynamical
    (all-epoch) law is refuted by the Omega evolution and the RVM bound. *)
Definition verdict (r : Reading) : Verdict :=
  match r with Snapshot => Consistent | Dynamical => Refuted end.

Theorem confrontation_verdict :
  verdict Snapshot = Consistent /\ verdict Dynamical = Refuted.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** Confronting the stage-count law with data (deepening the testable side):
      (bound)     framework coefficient nu ~ O(1) (=1) exceeds the RVM bound |nu| <~ 10^-3 by ~3 orders;
      (constant)  the dynamical law (Lambda ∝ H^2) makes Omega_Lambda EPOCH-INDEPENDENT (H^2 cancels);
      (evolves)   but the observed Omega_Lambda evolves (~10^-9 at recombination, ~0.7 today);
      (clash)     matched to today, the law predicts 0.7 at recombination, observed ~10^-9 — refuted;
      (verdict)   snapshot reading Consistent (non-distinguishing); dynamical reading Refuted.
    Honest: empirical discipline FALSIFIES the clean dynamical (distinguishing) reading and keeps only the
    non-distinguishing snapshot — a refutation that disciplines the theory, like Fermi-LAT vs the lattice. *)
Theorem lambda_running_vacuum_confrontation :
  nu_obs_max < nu_framework
  /\ (forall nu k H1 H2 : Q,
        ~ (k == 0) -> ~ (H1 == 0) -> ~ (H2 == 0) ->
        Omega_dyn nu k H1 == Omega_dyn nu k H2)
  /\ ~ (Omega_obs_recomb == Omega_obs_now)
  /\ ~ (Omega_dyn (7 # 10) 1 1 == Omega_obs_recomb)
  /\ verdict Snapshot = Consistent
  /\ verdict Dynamical = Refuted.
Proof.
  split; [ exact framework_nu_exceeds_bound | ].
  split; [ exact omega_dyn_constant | ].
  split; [ exact observed_omega_evolves | ].
  split; [ exact (proj2 refuted_at_recombination) | ].
  split; reflexivity.
Qed.
