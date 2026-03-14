(** * ProcessIVT.v — Intermediate Value Theorem as Process Construction
    Elements: midpoints c(n) of nested intervals via bisection
    Roles:    Cauchy process in [a,b], converging to root
    Rules:    bisection — evaluate sign at midpoint, choose half
    Status:   complete
    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS IVT — Intermediate Value Theorem as Process Construction   *)
(*                                                                            *)
(*  The IVT finds a root of f on [a,b] by bisection.                        *)
(*  Under P4: the root IS the bisection process, not its limit.             *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: midpoints c(n) of nested intervals                           *)
(*    Roles:    Cauchy process in [a,b], converging to root                  *)
(*    Rules:    bisection — evaluate sign at midpoint, choose half           *)
(*                                                                            *)
(*  STATUS: 13 Qed, 0 Admitted                                               *)
(*  AXIOMS: none (inherits classic from IVT_ERR)                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import IVT_ERR.
From ToS Require Import Archimedean_ERR.

(* ================================================================== *)
(*  Part I: Cauchy Compatibility                                       *)
(*                                                                      *)
(*  Archimedean_ERR uses (m > N)%nat, ProcessCore uses (N <= m)%nat   *)
(*  These are equivalent up to N offset.                                *)
(* ================================================================== *)

(** The two Cauchy definitions are equivalent *)
Lemma cauchy_gt_to_le : forall R,
  Archimedean_ERR.is_Cauchy R -> ProcessCore.is_Cauchy R.
Proof.
  intros R Hgt eps Heps.
  assert (Hgt' : eps > 0) by lra.
  destruct (Hgt eps Hgt') as [N HN].
  exists (S N). intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma cauchy_le_to_gt : forall R,
  ProcessCore.is_Cauchy R -> Archimedean_ERR.is_Cauchy R.
Proof.
  intros R Hle eps Heps.
  assert (Hlt : 0 < eps) by lra.
  destruct (Hle eps Hlt) as [N HN].
  exists N. intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma cauchy_compat : forall R,
  Archimedean_ERR.is_Cauchy R <-> ProcessCore.is_Cauchy R.
Proof.
  intro R. split; [apply cauchy_gt_to_le | apply cauchy_le_to_gt].
Qed.

(** Interval definitions are identical *)
Lemma interval_compat : forall a b R,
  IVT_ERR.in_interval a b R <-> ProcessCore.in_interval a b R.
Proof.
  intros a b R. unfold IVT_ERR.in_interval, ProcessCore.in_interval. tauto.
Qed.

(** Equivalence definitions are compatible (> N vs N <=) *)
Lemma equiv_to_process_equiv : forall R1 R2,
  IVT_ERR.equiv R1 R2 -> ProcessCore.process_equiv R1 R2.
Proof.
  intros R1 R2 Heq eps Heps.
  assert (Hgt : eps > 0) by lra.
  destruct (Heq eps Hgt) as [N HN].
  exists (S N). intros n Hn.
  apply HN. lia.
Qed.

Lemma process_equiv_to_equiv : forall R1 R2,
  ProcessCore.process_equiv R1 R2 -> IVT_ERR.equiv R1 R2.
Proof.
  intros R1 R2 Heq eps Heps.
  assert (Hlt : 0 < eps) by lra.
  destruct (Heq eps Hlt) as [N HN].
  exists N. intros n Hn.
  apply HN. lia.
Qed.

Lemma equiv_compat : forall R1 R2,
  IVT_ERR.equiv R1 R2 <-> ProcessCore.process_equiv R1 R2.
Proof.
  intros R1 R2. split; [apply equiv_to_process_equiv | apply process_equiv_to_equiv].
Qed.

(* ================================================================== *)
(*  Part II: IVT in ProcessCore Language                               *)
(* ================================================================== *)

(** The bisection process is Cauchy (ProcessCore version) *)
Theorem bisection_cauchy : forall (f : ContinuousFunction) (a b : Q),
  a < b ->
  ProcessCore.is_Cauchy (bisection_process f a b).
Proof.
  intros f a b Hab.
  apply cauchy_gt_to_le.
  exact (bisection_is_Cauchy f a b Hab).
Qed.

(** The bisection process stays in [a,b] (ProcessCore version) *)
Theorem bisection_bounded : forall (f : ContinuousFunction) (a b : Q),
  a <= b ->
  ProcessCore.in_interval a b (bisection_process f a b).
Proof.
  intros f a b Hab.
  apply interval_compat.
  exact (bisection_in_interval f a b Hab).
Qed.

(** The IVT restated with ProcessCore types *)
Theorem process_IVT : forall (f : ContinuousFunction) (a b : Q),
  a < b ->
  IVT_ERR.uniformly_continuous_on f a b ->
  f a < 0 -> 0 < f b ->
  exists c : RealProcess,
    ProcessCore.is_Cauchy c /\
    ProcessCore.in_interval a b c /\
    ProcessCore.process_equiv (apply_to_process f c) (const_process 0).
Proof.
  intros f a b Hab Hcont Hfa Hfb.
  assert (Hfb' : f b > 0) by lra.
  destruct (IVT_process f a b Hab Hcont Hfa Hfb') as [c [Hc1 [Hc2 Hc3]]].
  exists c. split; [| split].
  - apply cauchy_gt_to_le. exact Hc1.
  - apply interval_compat. exact Hc2.
  - apply equiv_to_process_equiv.
    (* equiv (apply_to_process f c) (fun _ => 0) ↔ equiv ... (const_process 0) *)
    (* const_process 0 = fun _ => 0 definitionally *)
    exact Hc3.
Qed.

(* ================================================================== *)
(*  Part III: E/R/R Annotation                                         *)
(* ================================================================== *)

(** Convergence rate: bisection halves the interval each step *)
(** Width at step n = (b-a)/2^n *)
Lemma bisection_width_bound : forall f a b n,
  bis_right (bisection_iter f (mkBisection a b) n)
  - bis_left (bisection_iter f (mkBisection a b) n) == (b - a) / Qpow2 n.
Proof.
  exact bisection_width.
Qed.

(** The IVT pattern matches the unified process pattern *)
Theorem ivt_is_process_construction : forall f a b,
  a < b -> IVT_ERR.uniformly_continuous_on f a b -> f a < 0 -> 0 < f b ->
  exists c : RealProcess,
    ProcessCore.is_Cauchy c /\
    ProcessCore.in_interval a b c /\
    ProcessCore.process_equiv (apply_to_process f c) (const_process 0).
Proof. exact process_IVT. Qed.

(** IVT convergence rate is 1/2 *)
Definition ivt_convergence_rate : Q := 1 # 2.

Lemma ivt_rate_valid : 0 < ivt_convergence_rate /\ ivt_convergence_rate < 1.
Proof. unfold ivt_convergence_rate. split; lra. Qed.
