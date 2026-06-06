(** * RGCascadeReal.v — the RENORMALIZATION-GROUP cascade as a GENUINE MULTI-STEP coupling flow over Q
      (the RG-arena instance of scale-flow, parallel to ShellCascadeNS in the energy arena).

   The survey of the repo found that the gauge "RG flow over lattice sizes 2^k" is NOT a real block-spin
   recomputation: gauge/ExactRGProcess.v uses gap_lower_N = gap_2x2 / N_sp -- a 1/N analytic RESCALING of
   a FIXED 2x2 gap, so the "scale dependence" carries no renormalization content.  Real decimation exists
   only as ISOLATED single steps (the Schur complement in lattice/BlockDecimation1D.v).  This file fixes
   that honesty gap: a coupling that is genuinely RECOMPUTED at every rung.

   -- The block-spin decimation map (two bonds in series via an eliminated site combine quadratically):
        rg_step t = t * t.   Iterated: rg_iterate t n = t^(2^n) -- the coupling FLOWS, recomputed each
        rung (t_{n+1} = t_n^2), NOT rescaled.  Fixed points: 0 (stable trivial) and 1 (unstable critical).
   -- Element side (sub-critical, 0 <= t <= 1): the flow CONTRACTS -- rg_iterate is non-increasing and
        stays in [0,1] -- toward the trivial fixed point 0 (the gapped / decoupled phase).  Computable,
        convergent: Element.
   -- Role-limit side (super-critical, t >= 1): the flow RUNS AWAY -- rg_iterate is non-decreasing and
        stays >= 1 -- the critical / continuum-limit direction.  The closure is the role-limit.
   -- The critical point t = 1 is the H1 boundary between the two.

   HONEST SCOPE.  A clean DIMENSIONLESS model of block-spin decimation (t' = t^2, the generic two-bonds-
   to-one form), genuinely multi-step (recomputed each rung) -- the honest contrast to the faked 1/N
   rescaling of ExactRGProcess.  It is NOT a literal port of the Schur-complement BlockDecimation1D, and
   it does NOT take the continuum limit (that closure is the role-limit).  Relocate, not cross.

   Elements: the rational coupling t; the finite iterates rg_iterate t n; the two fixed points.
   Roles:    the RG rungs n; the running coupling t_n; the critical point t=1 (the boundary role).
   Rules:    decimation rg_step t = t^2 (two bonds -> one); sub-critical contracts (Element), super-
             critical runs away (role-limit); t=1 is the fixed boundary.

   ============ E/R/R разбор ============
     Rules (L5): децимация rg_step t = t^2 (две связи -> одна); итерация t_{n+1}=t_n^2 = поток; неподв. 0,1.
     Roles (L4): РГ-ступени n; бегущая связь t_n; критическая точка t=1 (граница).
     Elements  : рациональная связь t; конечные итераты; неподвижные точки.
   ДИАГНОСТИКА (P4): РГ-поток = процесс; докритический = Element (сжимается к неподв. точке), надкритический
   = role-limit (убегает, континуум). НАСТОЯЩИЙ многошаг (пересчёт каждый рунг) = honesty-фикс ExactRGProcess.
   Параллель ShellCascadeNS. ЧЕСТНО: безразмерная модель (t^2), не порт BlockDecimation1D; континуум не берём.

   STATUS: 11 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The block-spin decimation map and the RG flow                          *)
(* ===================================================================== *)

(** One block-spin decimation: two bonds in series via an eliminated site -> quadratic combination. *)
Definition rg_step (t : Q) : Q := t * t.

(** The RG flow: iterate the decimation n times (rg_iterate t n = t^(2^n)). *)
Fixpoint rg_iterate (t : Q) (n : nat) : Q :=
  match n with O => t | S k => rg_step (rg_iterate t k) end.

(** ★ The flow is genuinely MULTI-STEP: the coupling is RECOMPUTED at each rung (t_{n+1} = t_n^2),
    NOT rescaled by 1/N.  This is the definitional fixpoint equation. *)
Lemma rg_iterate_S : forall t n, rg_iterate t (S n) = rg_step (rg_iterate t n).
Proof. reflexivity. Qed.

(** Fixed points: 0 (stable, trivial) and 1 (unstable, critical). *)
Lemma rg_fixed_0 : rg_step 0 == 0.
Proof. unfold rg_step. ring. Qed.
Lemma rg_fixed_1 : rg_step 1 == 1.
Proof. unfold rg_step. ring. Qed.

(* ===================================================================== *)
(*  Element side: sub-critical flow contracts toward the trivial fixed pt  *)
(* ===================================================================== *)

(** The unit interval [0,1] is an invariant region for the sub-critical flow. *)
Lemma rg_iterate_in_unit : forall t n,
  0 <= t -> t <= 1 -> 0 <= rg_iterate t n /\ rg_iterate t n <= 1.
Proof.
  intros t n Ht0 Ht1. induction n as [|k IH].
  - simpl. split; assumption.
  - destruct IH as [Ha Hb]. rewrite rg_iterate_S. unfold rg_step. split.
    + apply Qmult_le_0_compat; assumption.
    + apply Qle_trans with (1 * rg_iterate t k).
      * apply Qmult_le_compat_r; assumption.
      * rewrite Qmult_1_l. assumption.
Qed.

(** ★ Sub-critical CONTRACTION: for 0 <= t <= 1 the flow is non-increasing -- it contracts toward 0.
    This is the Element side: a convergent, computable flow (the gapped / decoupled phase). *)
Theorem rg_sub_decreasing : forall t n,
  0 <= t -> t <= 1 -> rg_iterate t (S n) <= rg_iterate t n.
Proof.
  intros t n Ht0 Ht1.
  destruct (rg_iterate_in_unit t n Ht0 Ht1) as [Ha Hb].
  rewrite rg_iterate_S. unfold rg_step.
  apply Qle_trans with (1 * rg_iterate t n).
  - apply Qmult_le_compat_r; assumption.
  - rewrite Qmult_1_l. apply Qle_refl.
Qed.

(* ===================================================================== *)
(*  Role-limit side: super-critical flow runs away (continuum limit)       *)
(* ===================================================================== *)

(** The super-critical flow stays >= 1 (invariant region [1, infinity)). *)
Lemma rg_iterate_ge_1 : forall t n, 1 <= t -> 1 <= rg_iterate t n.
Proof.
  intros t n Ht. induction n as [|k IH].
  - simpl. assumption.
  - rewrite rg_iterate_S. unfold rg_step.
    assert (H0 : 0 <= rg_iterate t k) by (apply Qle_trans with 1; [lra | exact IH]).
    apply Qle_trans with (rg_iterate t k).
    + exact IH.
    + apply Qle_trans with (1 * rg_iterate t k).
      * rewrite Qmult_1_l. apply Qle_refl.
      * apply Qmult_le_compat_r; [exact IH | exact H0].
Qed.

(** ★ Super-critical RUNAWAY: for t >= 1 the flow is non-decreasing -- it runs away.
    This is the role-limit side: the critical / continuum-limit direction, NOT crossed. *)
Theorem rg_super_increasing : forall t n,
  1 <= t -> rg_iterate t n <= rg_iterate t (S n).
Proof.
  intros t n Ht.
  pose proof (rg_iterate_ge_1 t n Ht) as Hge.
  assert (H0 : 0 <= rg_iterate t n) by (apply Qle_trans with 1; [lra | exact Hge]).
  rewrite rg_iterate_S. unfold rg_step.
  apply Qle_trans with (1 * rg_iterate t n).
  - rewrite Qmult_1_l. apply Qle_refl.
  - apply Qmult_le_compat_r; [exact Hge | exact H0].
Qed.

(* ===================================================================== *)
(*  Concrete witnesses + the H1 boundary                                   *)
(* ===================================================================== *)

(** Sub-critical: t = 1/2 decays (1/2 -> 1/4 -> 1/16 -> 1/256). *)
Example rg_subcritical_decays : rg_iterate (1#2) 3 == 1#256.
Proof. vm_compute. reflexivity. Qed.

(** Super-critical: t = 2 runs away (2 -> 4 -> 16 -> 256). *)
Example rg_supercritical_grows : rg_iterate 2 3 == 256.
Proof. vm_compute. reflexivity. Qed.

(** The two sides of the RG flow's finitization boundary. *)
Inductive RGSide := SubcriticalElement | SupercriticalRoleLimit.
Lemma rg_h1_disjoint : SubcriticalElement <> SupercriticalRoleLimit.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the genuine multi-step RG cascade over Q                      *)
(* ===================================================================== *)

(** The renormalization-group cascade -- a GENUINE multi-step coupling flow (the honesty fix):
      (multi-step) the coupling is recomputed each rung, t_{n+1} = t_n^2 (not rescaled by 1/N);
      (fixed pts)  0 (stable trivial) and 1 (unstable critical);
      (Element)    sub-critical (0<=t<=1): the flow contracts (non-increasing) toward 0 -- convergent;
      (role-limit) super-critical (t>=1): the flow runs away (non-decreasing) -- the continuum limit.
    The RG-arena instance of scale-flow, parallel to the energy-arena ShellCascadeNS: same Element /
    role-limit split on a scale flow over Q.  The continuum limit is the role-limit, located NOT crossed. *)
Theorem rg_cascade_real :
  (forall t n, rg_iterate t (S n) == rg_step (rg_iterate t n))
  /\ (rg_step 0 == 0 /\ rg_step 1 == 1)
  /\ (forall t n, 0 <= t -> t <= 1 -> rg_iterate t (S n) <= rg_iterate t n)
  /\ (forall t n, 1 <= t -> rg_iterate t n <= rg_iterate t (S n)).
Proof.
  split; [intros t n; reflexivity |].
  split; [split; [exact rg_fixed_0 | exact rg_fixed_1] |].
  split; [exact rg_sub_decreasing |].
  exact rg_super_increasing.
Qed.
