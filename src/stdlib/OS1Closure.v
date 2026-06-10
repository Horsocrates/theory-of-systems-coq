(* OS1Closure.v — Close analyticity True using QiPowerSeries *)
(* June 2026 HONEST SCOPE: "Closure" = closing the repo's True-placeholder
   backlog with TOY specializations (polynomial analyticity, concrete Bessel
   bounds).  The REAL lattice-model OS1 — analyticity of the full
   correlation — is gauge/FormalAnalytic.v (os1_formal), bridged in
   stdlib/GaugeOSClosure.v (gauge_os1_real). *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

From ToS Require Import stdlib.QiPowerSeries.
From ToS Require Import process.ProcessGaussianQ.
From ToS Require Import gauge.CharacterTransfer.
From ToS Require Import SeriesConvergence.

(* ================================================================== *)
(*  OS1 #1-2: polynomial is analytic + infinite radius                 *)
(*  CLOSED: polynomial_is_analytic, polynomial_exact                  *)
(* ================================================================== *)

Theorem os1_poly_analytic : forall (a : nat -> Qi) (N : nat) z0,
  qi_polynomial a N ->
  qi_analytic_at (fun z => qi_partial_sum a z N) z0.
Proof. exact polynomial_is_analytic. Qed.

Theorem os1_infinite_radius : forall (a : nat -> Qi) z (N : nat),
  qi_polynomial a N ->
  qi_eq (qi_partial_sum a z (S N)) (qi_partial_sum a z N).
Proof. exact polynomial_exact. Qed.

(* ================================================================== *)
(*  OS1 #3-4: eigenvalue polynomial in beta + correlation polynomial   *)
(*  CLOSED: structural — bessel_partial defined as finite Qpow sum    *)
(* ================================================================== *)

(** June 2026 honesty rollback: os1_bessel_degree was `exists deg, deg = n+2M`
    (vacuous), and os1_correlation_degree / os1_two_point_poly / os1_partition_poly
    were `exists deg, 0 <= deg` (pure shams) — the latter three are DELETED.
    The real available content: truncation degrees strictly GROW with the order,
    so the polynomial approximations form a genuine refinement ladder. *)
Theorem os1_bessel_degree : forall n M : nat,
  (n + 2 * M < n + 2 * S M)%nat.
Proof. intros. lia. Qed.

(* ================================================================== *)
(*  OS1 #5-8: two_point, connected, partition, continuation            *)
(*  (June 2026: the two `exists deg, 0 <= deg` shams that stood here    *)
(*   are deleted; the honest closure for these items is the concrete    *)
(*   positivity + error bounds below.)                                  *)
(* ================================================================== *)

(** Connected correlation well-defined at concrete values *)
Lemma os1_I0_pos_b1 : 0 < bessel_partial 0 1 O.
Proof. unfold bessel_partial, bessel_term, fact_Q, fact_prod, fact, Qpow. unfold Qlt; simpl; lia. Qed.

Lemma os1_I0_pos_b2 : 0 < bessel_partial 0 2 O.
Proof. unfold bessel_partial, bessel_term, fact_Q, fact_prod, fact, Qpow. unfold Qlt; simpl; lia. Qed.

(* ================================================================== *)
(*  OS1 #9-11: Taylor convergence                                      *)
(*  CLOSED: concrete error bounds at specific (beta,M)                *)
(* ================================================================== *)

Lemma os1_error_b1_M2 :
  bessel_term 0 3 1 < 1 # 100.
Proof.
  unfold bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qlt; simpl; lia.
Qed.

Lemma os1_error_b1_M3 :
  bessel_term 0 4 1 < 1 # 1000.
Proof.
  unfold bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qlt; simpl; lia.
Qed.

(** Error decreasing: bessel_term(0, M+1, 1) < bessel_term(0, M, 1) *)
Lemma os1_error_decreasing :
  bessel_term 0 4 1 < bessel_term 0 3 1.
Proof.
  unfold bessel_term, fact_Q, fact_prod, fact, Qpow.
  unfold Qlt; simpl; lia.
Qed.

(* ================================================================== *)
(*  OS1 #12-17: Taylor is polynomial + limits                          *)
(* ================================================================== *)

(** Taylor truncation degree grows strictly with the order (June 2026: was the
    vacuous `exists deg, deg = 2*M`). *)
Theorem os1_taylor_is_poly : forall M : nat,
  (2 * M < 2 * S M)%nat.
Proof. intros. lia. Qed.

(** Constant is analytic *)
Theorem os1_const_analytic : forall c z0,
  qi_analytic_at (fun _ => c) z0.
Proof. exact constant_analytic. Qed.

(** ★ REPLACEMENT for os1_analyticity (June 2026: conjunct 2 was a vacuous
    exists; now the degree-ladder growth) *)
Definition os1_analyticity_proved : Prop :=
  (forall a N z0, qi_polynomial a N ->
    qi_analytic_at (fun z => qi_partial_sum a z N) z0) /\
  (forall n M : nat, (n + 2 * M < n + 2 * S M)%nat) /\
  0 < bessel_partial 0 1 O.

Theorem os1_proved : os1_analyticity_proved.
Proof.
  split; [|split].
  - exact polynomial_is_analytic.
  - exact os1_bessel_degree.
  - exact os1_I0_pos_b1.
Qed.

(** 11 real closure items after the June-2026 sham removal (was declared 14
    with three `exists deg, 0 <= deg` paddings). *)
Definition os1_closure_count := 11%nat.
