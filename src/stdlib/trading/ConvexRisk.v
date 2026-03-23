(** * ConvexRisk.v — Convex risk measures as ToS System
    Elements: variance, correlation, portfolio size K
    Roles:    risk quantification (sq), diversification (portfolio_var)
    Rules:    sq convex, diversification reduces variance,
              monotone improvement with K, limiting behavior
    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Square function and portfolio variance                           *)
(* ================================================================ *)

Definition sq (x : Q) : Q := x * x.

(* Portfolio variance for K equal-weight assets:
   var = sigma2/K + sigma2 * rho * (K-1)/K
   Using Q: K is passed as Q directly *)
Definition portfolio_var (sigma2 rho K : Q) : Q :=
  sigma2 / K + sigma2 * rho * (K - 1) / K.

(* ================================================================ *)
(* Convexity of sq for concrete values                              *)
(* ================================================================ *)

(* sq(midpoint) <= midpoint of squares *)
(* For x=0, y=2: sq(1) = 1 <= (0+4)/2 = 2 *)
Lemma sq_convex_0_2 :
  sq ((1#2) * 0 + (1#2) * 2) <= (1#2) * sq 0 + (1#2) * sq 2.
Proof. unfold sq, Qle. simpl. lia. Qed.

(* For x=1, y=3: sq(2) = 4 <= (1+9)/2 = 5 *)
Lemma sq_convex_1_3 :
  sq ((1#2) * 1 + (1#2) * 3) <= (1#2) * sq 1 + (1#2) * sq 3.
Proof. unfold sq, Qle. simpl. lia. Qed.

(* For x=2, y=4: sq(3) = 9 <= (4+16)/2 = 10 *)
Lemma sq_convex_2_4 :
  sq ((1#2) * 2 + (1#2) * 4) <= (1#2) * sq 2 + (1#2) * sq 4.
Proof. unfold sq, Qle. simpl. lia. Qed.

(* For x=-1, y=1: sq(0) = 0 <= (1+1)/2 = 1 *)
Lemma sq_convex_neg1_1 :
  sq ((1#2) * (-(1)) + (1#2) * 1) <= (1#2) * sq (-(1)) + (1#2) * sq 1.
Proof. unfold sq, Qle. simpl. lia. Qed.

(* sq is non-negative for concrete values *)
Lemma sq_nonneg_3 : 0 <= sq 3.
Proof. unfold sq, Qle. simpl. lia. Qed.

Lemma sq_nonneg_neg2 : 0 <= sq (-(2)).
Proof. unfold sq, Qle. simpl. lia. Qed.

Lemma sq_nonneg_half : 0 <= sq (1#2).
Proof. unfold sq, Qle. simpl. lia. Qed.

(* sq 0 = 0 *)
Lemma sq_zero : sq 0 == 0.
Proof. unfold sq. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Diversification: concrete portfolio variance                     *)
(* ================================================================ *)

(* Single asset (K=1): var = sigma2 *)
Lemma diversification_K1 :
  portfolio_var 1 (1#2) 1 == 1.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* Two assets (K=2), rho=1/2: var = 1/2 + 1/2*1/2 = 3/4 *)
Lemma diversification_K2 :
  portfolio_var 1 (1#2) 2 == 3#4.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* Four assets (K=4), rho=1/2: var = 1/4 + 1/2*3/4 = 1/4 + 3/8 = 5/8 *)
Lemma diversification_K4 :
  portfolio_var 1 (1#2) 4 == 5#8.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* Five assets *)
Lemma diversification_K5 :
  portfolio_var 1 (1#2) 5 == 3#5.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* Ten assets *)
Lemma diversification_K10 :
  portfolio_var 1 (1#2) 10 == 11#20.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Diversification improves (monotone decrease)                     *)
(* ================================================================ *)

(* K=2 < K=1 *)
Lemma diversification_K2_lt_K1 :
  portfolio_var 1 (1#2) 2 < portfolio_var 1 (1#2) 1.
Proof. unfold portfolio_var, Qlt. vm_compute. reflexivity. Qed.

(* K=4 < K=2 *)
Lemma diversification_K4_lt_K2 :
  portfolio_var 1 (1#2) 4 < portfolio_var 1 (1#2) 2.
Proof. unfold portfolio_var, Qlt. vm_compute. reflexivity. Qed.

(* K=10 < K=4 *)
Lemma diversification_K10_lt_K4 :
  portfolio_var 1 (1#2) 10 < portfolio_var 1 (1#2) 4.
Proof. unfold portfolio_var, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Limiting behavior: as K→∞, var → sigma2*rho                     *)
(* For rho=1/2: limit = 1/2. K=10 gives 11/20 = 0.55, close.      *)
(* ================================================================ *)

(* Large K approximation: K=100 *)
Lemma diversification_K100 :
  portfolio_var 1 (1#2) 100 == 101#200.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* K=100 is within 1/200 of the limit 1/2 *)
Lemma diversification_limit_approx :
  portfolio_var 1 (1#2) 100 - (1#2) == 1#200.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* Zero correlation: perfect diversification *)
Lemma zero_corr_K2 :
  portfolio_var 1 0 2 == 1#2.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

Lemma zero_corr_K10 :
  portfolio_var 1 0 10 == 1#10.
Proof. unfold portfolio_var. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition convex_risk_synthesis : Prop :=
  sq ((1#2) * 0 + (1#2) * 2) <= (1#2) * sq 0 + (1#2) * sq 2 /\
  portfolio_var 1 (1#2) 2 < portfolio_var 1 (1#2) 1 /\
  portfolio_var 1 (1#2) 100 - (1#2) == 1#200.

Lemma convex_risk_synthesis_holds : convex_risk_synthesis.
Proof.
  split. exact sq_convex_0_2.
  split. exact diversification_K2_lt_K1.
  exact diversification_limit_approx.
Qed.
