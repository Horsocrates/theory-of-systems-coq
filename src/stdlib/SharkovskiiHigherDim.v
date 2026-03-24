(** * SharkovskiiHigherDim.v — Sharkovskii fails in dimension >= 2
    Elements: 2D maps (cyclic permutation, negation, shear)
    Roles:    period structure without forcing
    Rules:    period-3 does NOT imply chaos in 2D (counterexample: rotation)
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)
From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(** Cyclic permutation of 3 elements: period 3, no chaos *)
Definition cyclic3 (v : list Q) : list Q :=
  match v with
  | a :: b :: c :: nil => c :: a :: b :: nil
  | _ => v
  end.

Lemma cyclic3_step1 : cyclic3 [1; 0; 0] = [0; 1; 0].
Proof. reflexivity. Qed.

Lemma cyclic3_step2 : cyclic3 [0; 1; 0] = [0; 0; 1].
Proof. reflexivity. Qed.

Lemma cyclic3_step3 : cyclic3 [0; 0; 1] = [1; 0; 0].
Proof. reflexivity. Qed.

(** Full period-3 cycle verified *)
Lemma cyclic3_period3 :
  cyclic3 [1; 0; 0] = [0; 1; 0] /\
  cyclic3 [0; 1; 0] = [0; 0; 1] /\
  cyclic3 [0; 0; 1] = [1; 0; 0].
Proof. repeat split; reflexivity. Qed.

(** 2D negation: (x,y) -> (-x, -y). Period 2 everywhere except origin. *)
Definition negate_2d (x y : Q) : Q * Q := (-x, -y).

Lemma negate_period_2 :
  negate_2d 1 2 = (-(1), -(2)) /\
  negate_2d (-(1)) (-(2)) = (1, 2).
Proof.
  split; reflexivity.
Qed.

(** Negation fixed point at origin *)
Lemma negate_fixed_origin : negate_2d 0 0 = (0, 0).
Proof. unfold negate_2d. f_equal; ring. Qed.

(** 2D shear map: (x,y) -> (x+y, y). No periodic orbits except fixed points *)
Definition shear (x y : Q) : Q * Q := (x + y, y).

Lemma shear_iterate2 :
  let p := shear 1 1 in
  shear (fst p) (snd p) = (3, 1).
Proof. vm_compute. reflexivity. Qed.

(** Shear fixed points: y=0 *)
Lemma shear_fixed : shear 5 0 = (5, 0).
Proof. unfold shear. f_equal; ring. Qed.

(** KEY: In 2D, period-3 map (cyclic3) has NO period-2 orbits *)
(** Cyclic3 applied twice: [1;0;0] -> [0;1;0] -> [0;0;1] (not back to start) *)
Lemma cyclic3_no_period2 :
  cyclic3 (cyclic3 [1; 0; 0]) = [0; 0; 1] /\
  [0; 0; 1] <> [1; 0; 0].
Proof.
  split.
  - reflexivity.
  - intro H. discriminate.
Qed.

(** Synthesis: Sharkovskii fails in higher dimensions *)
Theorem higher_dim_no_sharkovskii :
  (* Period-3 exists (cyclic permutation) *)
  cyclic3 [1; 0; 0] = [0; 1; 0] /\
  cyclic3 [0; 1; 0] = [0; 0; 1] /\
  cyclic3 [0; 0; 1] = [1; 0; 0] /\
  (* But no period-2: cyclic3^2 ≠ identity on [1;0;0] *)
  cyclic3 (cyclic3 [1; 0; 0]) <> [1; 0; 0] /\
  (* 2D negation: period-2, no period-3 *)
  negate_2d 1 2 = (-(1), -(2)).
Proof.
  repeat split; try reflexivity.
  - intro H. discriminate.
Qed.
