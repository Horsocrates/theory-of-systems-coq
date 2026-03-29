(** * FubiniProcess.v — Fubini's theorem for 2D step functions
    Elements: Rectangle records, 2D step functions, iterated integrals
    Roles:    Double integral, iterated integral, order exchange
    Rules:    Fubini: integral_xy = integral_yx for step functions
    STATUS:   20 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: March 2026

    Fubini's theorem says: for "nice" functions on R^2,
      integral integral f(x,y) dx dy = integral integral f(x,y) dy dx

    For step functions on rectangles, this is EXACT and TRIVIAL:
    c * (x2-x1) * (y2-y1) = c * (y2-y1) * (x2-x1) by commutativity.

    But the theorem has deep content at the L1 completion level:
    it says the order of taking limits doesn't matter.

    Connection to transfer matrices: Tr(AB) = Tr(BA) is Fubini
    for the discrete counting measure. Our rectangle Fubini
    is the spatial/continuous analog.
*)

From Stdlib Require Import QArith Qabs List Lqa Lia.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  REPLICATED DEFINITIONS                                             *)
(* ================================================================== *)

(* Replicated from StepIntegral.v *)
Record Step := mkStep {
  step_val : Q;
  step_left : Q;
  step_right : Q;
  step_valid : step_left <= step_right
}.

Definition StepFun := list Step.

Definition step_integral (s : Step) : Q :=
  step_val s * (step_right s - step_left s).

Fixpoint step_fun_integral (f : StepFun) : Q :=
  match f with
  | [] => 0
  | s :: rest => step_integral s + step_fun_integral rest
  end.

(* ================================================================== *)
(*  2D RECTANGLE STEP FUNCTIONS                                        *)
(* ================================================================== *)

(** A rectangle in 2D: constant value on [x1,x2] x [y1,y2] *)
Record Rectangle := mkRect {
  rect_val : Q;
  rect_x1 : Q;
  rect_x2 : Q;
  rect_y1 : Q;
  rect_y2 : Q;
  rect_x_valid : rect_x1 <= rect_x2;
  rect_y_valid : rect_y1 <= rect_y2
}.

(** A 2D step function = list of rectangles *)
Definition StepFun2D := list Rectangle.

(* ================================================================== *)
(*  2D INTEGRAL                                                        *)
(* ================================================================== *)

(** Integral over one rectangle: c * (x2-x1) * (y2-y1) *)
Definition rect_integral (r : Rectangle) : Q :=
  rect_val r * (rect_x2 r - rect_x1 r) * (rect_y2 r - rect_y1 r).

(** Double integral of 2D step function *)
Fixpoint integral_2d (f : StepFun2D) : Q :=
  match f with
  | [] => 0
  | r :: rest => rect_integral r + integral_2d rest
  end.

(* ================================================================== *)
(*  ITERATED INTEGRALS                                                 *)
(* ================================================================== *)

(** Iterated integral: integrate x first, then y *)
Definition iterated_xy (r : Rectangle) : Q :=
  rect_val r * (rect_x2 r - rect_x1 r) * (rect_y2 r - rect_y1 r).

(** Iterated integral: integrate y first, then x *)
Definition iterated_yx (r : Rectangle) : Q :=
  rect_val r * (rect_y2 r - rect_y1 r) * (rect_x2 r - rect_x1 r).

(** Iterated integral for list: x first *)
Fixpoint iterated_xy_list (f : StepFun2D) : Q :=
  match f with
  | [] => 0
  | r :: rest => iterated_xy r + iterated_xy_list rest
  end.

(** Iterated integral for list: y first *)
Fixpoint iterated_yx_list (f : StepFun2D) : Q :=
  match f with
  | [] => 0
  | r :: rest => iterated_yx r + iterated_yx_list rest
  end.

(* ================================================================== *)
(*  FUBINI FOR SINGLE RECTANGLE                                        *)
(* ================================================================== *)

(** ★ Fubini for one rectangle: order doesn't matter *)
Lemma fubini_rectangle : forall r : Rectangle,
  iterated_xy r == iterated_yx r.
Proof.
  intros r. unfold iterated_xy, iterated_yx. ring.
Qed.

(** ★ Both iterated integrals equal the double integral for one rectangle *)
Lemma iterated_eq_double : forall r : Rectangle,
  iterated_xy r == rect_integral r.
Proof.
  intros r. unfold iterated_xy, rect_integral. ring.
Qed.

(** ★ yx iterated also equals double integral *)
Lemma iterated_yx_eq_double : forall r : Rectangle,
  iterated_yx r == rect_integral r.
Proof.
  intros r. unfold iterated_yx, rect_integral. ring.
Qed.

(* ================================================================== *)
(*  FUBINI FOR STEP FUNCTIONS (LISTS OF RECTANGLES)                    *)
(* ================================================================== *)

(** ★ Fubini for step functions: integral_xy = integral_yx *)
Theorem fubini_step : forall f : StepFun2D,
  iterated_xy_list f == iterated_yx_list f.
Proof.
  intros f. induction f as [| r rest IH].
  - simpl. ring.
  - simpl. rewrite fubini_rectangle. rewrite IH. ring.
Qed.

(** ★ iterated_xy_list equals integral_2d *)
Lemma iterated_xy_eq_2d : forall f : StepFun2D,
  iterated_xy_list f == integral_2d f.
Proof.
  intros f. induction f as [| r rest IH].
  - simpl. ring.
  - simpl. rewrite iterated_eq_double. rewrite IH. ring.
Qed.

(** ★ iterated_yx_list also equals integral_2d *)
Lemma iterated_yx_eq_2d : forall f : StepFun2D,
  iterated_yx_list f == integral_2d f.
Proof.
  intros f. induction f as [| r rest IH].
  - simpl. ring.
  - simpl. rewrite iterated_yx_eq_double. rewrite IH. ring.
Qed.

(* ================================================================== *)
(*  CONCRETE EXAMPLES                                                  *)
(* ================================================================== *)

Lemma le_0_1 : 0 <= 1. Proof. lra. Qed.
Lemma le_0_2 : 0 <= 2. Proof. lra. Qed.
Lemma le_0_3 : 0 <= 3. Proof. lra. Qed.
Lemma le_1_2 : 1 <= 2. Proof. lra. Qed.

(** ★ Example: f=3 on [0,1] x [0,2], I = 3*1*2 = 6 *)
Lemma example_rect_integral :
  rect_integral (mkRect 3 0 1 0 2 le_0_1 le_0_2) == 6.
Proof.
  unfold rect_integral. simpl. ring.
Qed.

(** ★ Example: Fubini on the concrete rectangle *)
Lemma example_fubini_concrete :
  iterated_xy (mkRect 3 0 1 0 2 le_0_1 le_0_2) ==
  iterated_yx (mkRect 3 0 1 0 2 le_0_1 le_0_2).
Proof.
  apply fubini_rectangle.
Qed.

(** ★ Example: two rectangles, f=2 on [0,1]x[0,1] + f=3 on [1,2]x[0,1] *)
Lemma example_two_rects :
  let r1 := mkRect 2 0 1 0 1 le_0_1 le_0_1 in
  let r2 := mkRect 3 1 2 0 1 le_1_2 le_0_1 in
  integral_2d [r1; r2] == 5.
Proof.
  simpl. unfold rect_integral. simpl. ring.
Qed.

(** ★ Example: Fubini on two rectangles *)
Lemma example_fubini_two :
  let r1 := mkRect 2 0 1 0 1 le_0_1 le_0_1 in
  let r2 := mkRect 3 1 2 0 1 le_1_2 le_0_1 in
  iterated_xy_list [r1; r2] == iterated_yx_list [r1; r2].
Proof.
  simpl. unfold iterated_xy, iterated_yx. simpl. ring.
Qed.

(* ================================================================== *)
(*  PROPERTIES OF 2D INTEGRAL                                          *)
(* ================================================================== *)

(** ★ Empty 2D integral = 0 *)
Lemma integral_2d_nil : integral_2d [] == 0.
Proof. simpl. ring. Qed.

(** ★ 2D integral is additive on concatenation *)
Lemma integral_2d_app : forall f g : StepFun2D,
  integral_2d (f ++ g) == integral_2d f + integral_2d g.
Proof.
  intros f g. induction f as [| r rest IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** ★ Rectangle with zero value has zero integral *)
Lemma rect_integral_zero_val : forall x1 x2 y1 y2
  (Hx : x1 <= x2) (Hy : y1 <= y2),
  rect_integral (mkRect 0 x1 x2 y1 y2 Hx Hy) == 0.
Proof.
  intros. unfold rect_integral. simpl. ring.
Qed.

(** ★ Rectangle with zero width has zero integral *)
Lemma rect_integral_zero_width : forall c y1 y2 x
  (Hx : x <= x) (Hy : y1 <= y2),
  rect_integral (mkRect c x x y1 y2 Hx Hy) == 0.
Proof.
  intros. unfold rect_integral. simpl. ring.
Qed.

(* ================================================================== *)
(*  CONNECTION TO TRANSFER MATRIX TRACE                                *)
(* ================================================================== *)

(** The discrete analog of Fubini is Tr(AB) = Tr(BA).
    For 1x1 "matrices" (scalars), this is just commutativity: a*b = b*a.
    We verify this principle at the scalar level. *)

(** ★ Scalar trace identity: a*b = b*a *)
Lemma trace_commute_scalar : forall a b : Q, a * b == b * a.
Proof. intros. ring. Qed.

(** ★ Grand theorem: Fubini + connection to trace *)
Theorem fubini_and_trace :
  (* Fubini for rectangles *)
  (forall r : Rectangle, iterated_xy r == iterated_yx r) /\
  (* Fubini for step functions *)
  (forall f : StepFun2D, iterated_xy_list f == iterated_yx_list f) /\
  (* Trace identity (discrete Fubini) *)
  (forall a b : Q, a * b == b * a).
Proof.
  split. { exact fubini_rectangle. }
  split. { exact fubini_step. }
  exact trace_commute_scalar.
Qed.

(** * PHILOSOPHICAL NOTE: Fubini and Process Observation

    Fubini's theorem says: the ORDER of observation doesn't matter.
    Whether we scan horizontally then vertically, or vice versa,
    we get the same total.

    In ToS terms: Fubini expresses the COMMUTATIVITY of observation
    processes. The double integral I(f) is a process-independent
    invariant of the function f.

    At the step function level, this is trivially true (ring identity).
    At the L1 completion level, it requires dominated convergence
    to justify exchanging the order of limits.

    The connection to Tr(AB) = Tr(BA) is deep: both are instances
    of "observation order independence" in different settings:
    - Fubini: continuous observation on rectangles
    - Trace: discrete observation on matrices
    - Both: P4 process invariance under re-ordering
*)
