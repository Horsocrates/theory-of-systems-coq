(** * LambdaAntigravityComputation.v — metaphysics-hint ① (computed): "the cosmological constant IS
       antigravity" made NUMERICAL.  The deceleration parameter q = (1+3w)/2 is q = -1 for Lambda (w=-1)
       vs q = +1/2 for matter; and the Friedmann acceleration a''/a (with the repo's G=7/1760, pi=22/7)
       is +1/30 for Lambda (repulsion) vs -1/60 for matter (attraction) — Lambda repels exactly TWICE
       as hard as matter attracts, per unit energy density.

    WHAT THE REPO HAS (surveyed): ProcessFriedmann.v (Friedmann eq 8*pi*rho0/3 = H^2, rho0 = 21H^2/176)
    but with a LINEAR scale factor a(t)=l0(1+Ht) => a'' = 0; no deceleration parameter q, no acceleration
    from Lambda.  This computes them.

    THE NUMBERS (over Q).
      deceleration parameter  q(w) = (1+3w)/2 :  matter (w=0) q=+1/2 (decel),  Lambda (w=-1) q=-1 (accel);
                              q < 0  <->  w < -1/3  <->  rho+3p < 0 (the antigravity condition);
      Friedmann acceleration  a''/a = -(4 pi G /3)(rho+3p),  G=7/1760, pi=22/7, 4piG/3 = 1/60 :
                              matter (p=0)   a''/a = -1/60  (attraction);
                              Lambda (p=-rho) a''/a = +1/30  (REPULSION = antigravity);
                              ratio = 2 : Lambda repels twice as hard as matter attracts.

    ============ E/R/R разбор ============
      Elements : уравнение состояния w; параметр замедления q; конкретные rho, G, pi.
      Roles    : q = знаковая мера притяжения(>0)/отталкивания(<0).
      Rules    : q=(1+3w)/2; q<0 <-> антигравитация; a''/a = -(4 pi G/3)(rho+3p).
      ДИАГНОСТИКА: Lambda (w=-1) -> q=-1 (макс. ускорение для одной жидкости); конкретно a''/a=+1/30 (G=7/1760,
      pi=22/7), вдвое сильнее притяжения материи (-1/60). ЧЕСТНО: q безразмерен (чист); a''/a в решёточных
      единицах (зависит от модельных G, pi, rho) — НЕ предсказание реального значения Lambda. Уровень:
      `новое обрамление известного` (вычисление стандартного q/a''/a в ℚ-единицах каркаса).

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Part A : deceleration parameter q = (1+3w)/2 ; antigravity <-> q < 0    *)
(* ===================================================================== *)

Definition q_param (w : Q) : Q := (1 + 3 * w) * (1#2).

Lemma q_matter    : q_param 0 == 1 # 2.        (* w=0  : q = +1/2  (deceleration = attraction) *)
Proof. unfold q_param. vm_compute. reflexivity. Qed.

Lemma q_radiation : q_param (1#3) == 1.        (* w=1/3: q = +1 *)
Proof. unfold q_param. vm_compute. reflexivity. Qed.

Lemma q_lambda    : q_param (-(1)) == -(1).    (* ★ w=-1 : q = -1  (acceleration = ANTIGRAVITY) *)
Proof. unfold q_param. vm_compute. reflexivity. Qed.

Lemma q_threshold : q_param (-(1#3)) == 0.     (* w=-1/3: q = 0  (boundary) *)
Proof. unfold q_param. vm_compute. reflexivity. Qed.

Lemma q_matter_positive : 0 < q_param 0.
Proof. unfold q_param. lra. Qed.

Lemma q_lambda_negative : q_param (-(1)) < 0.
Proof. unfold q_param. lra. Qed.

(** ★ Antigravity (q < 0) iff the equation of state w < -1/3 (i.e. 3w < -1) = the rho+3p<0 condition. *)
Lemma antigravity_iff_w : forall w, q_param w < 0 <-> 3 * w < -(1).
Proof. intros w. unfold q_param. split; intro H; lra. Qed.

(* ===================================================================== *)
(*  Part B : the Friedmann acceleration a''/a (concrete, repo G and pi)     *)
(* ===================================================================== *)

Definition G_newton : Q := 7 # 1760.     (* repo's Newton constant (QGCompleteSynthesis) *)

(** a''/a = -(4 pi G / 3)(rho + 3p).  With G=7/1760, pi=22/7: the coefficient 4 pi G/3 = 1/60. *)
Definition accel (rho p : Q) : Q := -(4 * (22#7) * G_newton / 3) * (rho + 3 * p).

(** Matter (rho=1, p=0): a''/a = -1/60 < 0 (deceleration = attraction). *)
Lemma accel_matter : accel 1 0 == -(1 # 60).
Proof. unfold accel, G_newton. vm_compute. reflexivity. Qed.

(** ★ Lambda (rho=1, p=-1): a''/a = +1/30 > 0 (ACCELERATION = antigravity). *)
Lemma accel_lambda : accel 1 (-(1)) == 1 # 30.
Proof. unfold accel, G_newton. vm_compute. reflexivity. Qed.

Lemma accel_lambda_positive : 0 < accel 1 (-(1)).
Proof. rewrite accel_lambda. lra. Qed.

(** ★ Lambda repels exactly TWICE as hard as matter attracts (per unit energy density). *)
Lemma accel_ratio : accel 1 (-(1)) == (-(2)) * accel 1 0.
Proof. rewrite accel_lambda, accel_matter. lra. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** "The cosmological constant is antigravity", computed:
      (q matter)  q = +1/2  (matter decelerates = attracts);
      (q Lambda)  q = -1    (Lambda accelerates = antigravity) -- the extreme for a single fluid;
      (signs)     matter q>0, Lambda q<0;
      (a'' matter) a''/a = -1/60 (attraction, in the repo's lattice units G=7/1760, pi=22/7);
      (a'' Lambda) a''/a = +1/30 (REPULSION = antigravity);
      (ratio)     Lambda repels twice as hard as matter attracts.
    Honest: q is dimensionless (clean); a''/a is in lattice units (model G, pi, rho), not a prediction of
    the physical value of Lambda. *)
Theorem lambda_antigravity_computed :
  (q_param 0 == 1 # 2)
  /\ (q_param (-(1)) == -(1))
  /\ (0 < q_param 0 /\ q_param (-(1)) < 0)
  /\ (accel 1 0 == -(1 # 60))
  /\ (accel 1 (-(1)) == 1 # 30)
  /\ (accel 1 (-(1)) == (-(2)) * accel 1 0).
Proof.
  split. exact q_matter.
  split. exact q_lambda.
  split. split; [ exact q_matter_positive | exact q_lambda_negative ].
  split. exact accel_matter.
  split. exact accel_lambda.
  exact accel_ratio.
Qed.
