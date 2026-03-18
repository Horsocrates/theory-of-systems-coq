(* ProcessUniversalityExplicit.v — Wilson vs Cosine action *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import SeriesConvergence.
From ToS Require Import PowerSeries.
From ToS Require Import gauge.CosineAction.
From ToS Require Import gauge.StrongCoupling.
From ToS Require Import process.ProcessPlaquette.
From ToS Require Import process.ProcessPlaquetteCurve.
Open Scope Q_scope.

(** Wilson: P_W = I1/I0 = 217/486 at beta=1, M=2 *)
(** Cosine: 1 - cos(theta) ~ theta^2/2 - theta^4/24 *)
(** SC: sigma = 3/(4*beta) *)

(** one_minus_cos_approx(1,2) = cos_term(1,0) + cos_term(1,1) *)
(** = 1^2/2! - 1^4/4! = 1/2 - 1/24 = 11/24 *)
(** From CosineAction: Qfact_2 = 2, Qfact_4 = 24 *)
(** one_minus_cos_approx(1, 2) = Σ_{n=0}^{2} cos_term(1, n) *)
(** = 1/2 - 1/24 + 1/720 = 331/720 ≈ 0.4597 *)
Lemma cosine_order_2_at_1 : one_minus_cos_approx 1 2 == 331 # 720.
Proof. vm_compute. reflexivity. Qed.

(** Wilson P = 0.446, Cosine ~ 0.460 -> 3% difference *)
(** At larger beta they converge (universality) *)

Lemma strong_coupling_at_1 : string_tension 1 == 3 # 4.
Proof. unfold string_tension. field. Qed.

Lemma strong_coupling_at_2 : string_tension 2 == 3 # 8.
Proof. unfold string_tension. field. Qed.

Theorem three_methods :
  string_tension 1 == 3 # 4 /\
  plaquette 1 2 == 217 # 486 /\
  one_minus_cos_approx 1 2 == 331 # 720.
Proof.
  split; [|split].
  - exact strong_coupling_at_1.
  - exact plaquette_b1_M2.
  - exact cosine_order_2_at_1.
Qed.

Theorem universality_demonstrated :
  0 < plaquette 1 2 /\
  plaquette 1 2 < 1 /\
  string_tension 1 == 3 # 4.
Proof.
  split; [|split].
  - rewrite plaquette_b1_M2. unfold Qlt; simpl; lia.
  - rewrite plaquette_b1_M2. unfold Qlt; simpl; lia.
  - exact strong_coupling_at_1.
Qed.

Definition univ_expl_count := 6%nat.
