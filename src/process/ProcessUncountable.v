(** * ProcessUncountable.v — Cantor's Theorem as Process Construction
    Elements: nested intervals avoiding each enumerated process
    Roles:    diagonal process differs from every enumerated one
    Rules:    at step n, avoid E(n) by choosing the other third
    Status:   complete
    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS UNCOUNTABLE — Cantor's Theorem as Process Construction     *)
(*                                                                            *)
(*  Under P4: "uncountable" means "no enumeration process captures all       *)
(*  Cauchy processes" — a statement about processes, not about a set.        *)
(*                                                                            *)
(*  E/R/R:                                                                    *)
(*    Elements: nested intervals [a_n, b_n] avoiding E(n)                    *)
(*    Roles:    diagonal process differs from every enumerated one            *)
(*    Rules:    at step n, E(n) is in at most one third → choose another    *)
(*                                                                            *)
(*  STATUS: 7 Qed, 0 Admitted                                               *)
(*  AXIOMS: classic (inherited from ShrinkingIntervals_ERR)                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import ShrinkingIntervals_ERR.

(* ================================================================== *)
(*  Part I: Cauchy Compatibility                                       *)
(* ================================================================== *)

(** ShrinkingIntervals uses (m > N), ProcessCore uses (N <= m) *)
Lemma si_cauchy_to_process : forall R,
  ShrinkingIntervals_ERR.is_Cauchy R -> ProcessCore.is_Cauchy R.
Proof.
  intros R Hgt eps Heps.
  assert (Hgt' : eps > 0) by (apply Qlt_gt; exact Heps).
  destruct (Hgt eps Hgt') as [N HN].
  exists (S N). intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma process_cauchy_to_si : forall R,
  ProcessCore.is_Cauchy R -> ShrinkingIntervals_ERR.is_Cauchy R.
Proof.
  intros R Hle eps Heps.
  assert (Hlt : 0 < eps) by (apply Qgt_lt; exact Heps).
  destruct (Hle eps Hlt) as [N HN].
  exists N. intros m n Hm Hn.
  apply HN; lia.
Qed.

Lemma si_cauchy_compat : forall R,
  ShrinkingIntervals_ERR.is_Cauchy R <-> ProcessCore.is_Cauchy R.
Proof.
  intro R. split; [apply si_cauchy_to_process | apply process_cauchy_to_si].
Qed.

(* ================================================================== *)
(*  Part II: not_equiv implies ~ process_equiv                         *)
(* ================================================================== *)

(** ShrinkingIntervals not_equiv implies ProcessCore non-equivalence *)
Lemma not_equiv_implies_not_process_equiv : forall R1 R2,
  ShrinkingIntervals_ERR.not_equiv R1 R2 ->
  ~ ProcessCore.process_equiv R1 R2.
Proof.
  intros R1 R2 [eps [Heps Hnot]] Hequiv.
  assert (Hlt : 0 < eps) by (apply Qgt_lt; exact Heps).
  destruct (Hequiv eps Hlt) as [N HN].
  destruct (Hnot N) as [m [HmN Habs]].
  assert (Hle : (N <= m)%nat) by lia.
  specialize (HN m Hle).
  assert (Hle2 : eps <= Qabs (R1 m - R2 m)) by (apply Qge_le; exact Habs).
  lra.
Qed.

(* ================================================================== *)
(*  Part III: Uncountability in ProcessCore Language                    *)
(* ================================================================== *)

(** Uncountability restated with ProcessCore types *)
Theorem process_uncountable :
  forall E : ShrinkingIntervals_ERR.Enumeration,
  ShrinkingIntervals_ERR.valid_regular_enumeration E ->
  exists D : RealProcess,
    ProcessCore.is_Cauchy D /\
    (forall m, 0 <= D m /\ D m <= 1) /\
    (forall n, ~ ProcessCore.process_equiv D (E n)).
Proof.
  intros E Hvalid.
  destruct (unit_interval_uncountable_trisect_v2 E Hvalid) as [D [HD1 [HD2 HD3]]].
  exists D. split; [| split].
  - apply si_cauchy_to_process. exact HD1.
  - exact HD2.
  - intros n. apply not_equiv_implies_not_process_equiv. exact (HD3 n).
Qed.

(* ================================================================== *)
(*  Part IV: P4 Interpretation                                         *)
(* ================================================================== *)

(** P4 interpretation:
    This does NOT say "R is uncountable" (R doesn't exist under P4).
    It says: the process type nat → (nat → Q) cannot be surjected
    onto by nat. The diagonal PROCESS always escapes. *)

(** The diagonal construction follows the process pattern *)
Theorem diagonal_is_process_construction :
  forall E : ShrinkingIntervals_ERR.Enumeration,
  ShrinkingIntervals_ERR.valid_regular_enumeration E ->
  (* There exists a Cauchy process in [0,1] differing from all E(n) *)
  exists D : RealProcess,
    ProcessCore.is_Cauchy D /\
    ProcessCore.in_interval 0 1 D /\
    (forall n, ~ ProcessCore.process_equiv D (E n)).
Proof.
  intros E Hvalid.
  destruct (process_uncountable E Hvalid) as [D [HD1 [HD2 HD3]]].
  exists D. split; [| split].
  - exact HD1.
  - intro n. split; [apply (HD2 n) | apply (HD2 n)].
  - exact HD3.
Qed.

(** Diagonal convergence rate is 1/3 (trisection) *)
Definition diagonal_convergence_rate : Q := 1 # 3.

Lemma diagonal_rate_valid :
  0 < diagonal_convergence_rate /\ diagonal_convergence_rate < 1.
Proof. unfold diagonal_convergence_rate. split; lra. Qed.
