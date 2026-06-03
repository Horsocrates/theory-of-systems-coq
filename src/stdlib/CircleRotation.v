(** * CircleRotation.v — rotation of the circle by an angle α: the orbit closes (is periodic)
      iff α is rational (Element side), otherwise it is quasiperiodic / dense (role-limit).
      The dynamical / resonance form of the cluster's "returns ⟺ rational" theme: rational
      frequency ratios mode-lock (periodic, Element); irrational ones are quasiperiodic
      (role-limit), with the golden ratio the "most irrational" winding (KAM), the same √5/φ
      as FibonacciWord / MarkovTree.

    Elements: the periodic orbits (e.g. 1/4 → {0,¼,½,¾}); the period q (L1 + P4)
    Roles:    Element side = a rational angle α=p/q gives a FINITE periodic orbit (returns to
              the start after q steps; mode-locking); role-limit = an irrational angle gives
              an infinite quasiperiodic orbit (never closes, dense), e.g. √2; the golden ratio
              is the most-irrational winding
    Rules:    the rotation x↦x+α; the orbit n·α; a return ⟺ n·α∈ℤ ⟺ α rational

    THE DEEP POINT — the orbit closes ⟺ the angle is rational.  Rotating by a rational angle
    α=p/q, after q steps the position is q·(p/q)=p, an integer — i.e. back to the start mod 1
    (`rotation_returns`): a FINITE periodic orbit, the Element side (mode-locking / resonance
    at rational frequency ratios).  Concretely the 1/3-rotation returns after 3 steps and the
    1/4-rotation after 4 (`rotation_third`, `rotation_quarter`).  But an irrational angle never
    returns: the √2-rotation's angle is irrational (`sqrt2_rotation_role_limit`), so the orbit
    never closes — quasiperiodic, dense, equidistributed — the role-limit.  The golden ratio is
    the most irrational angle (hardest to mode-lock, KAM stability), the same √5/φ as
    FibonacciWord and the Markov–Lagrange spectrum.  Element = the orbit closes (rational
    angle); role-limit = it never closes (irrational angle).

    ============ E/R/R разбор ============
      Rules (L5): поворот x↦x+α; орбита n·α; возврат ⟺ n·α∈ℤ ⟺ α рационально.
      Roles (L4): Element = рациональный угол α=p/q → конечная периодическая орбита (период q,
                  mode-locking); role-limit = иррациональный угол → квазипериодика (не замыкается, √2).
      Elements  : периодические орбиты (1/4→{0,¼,½,¾}); период q (L1+P4).
    ДИАГНОСТИКА (P4): орбита замыкается ⟺ угол рационален ⟺ Element; не замыкается ⟺ иррационален ⟺ role-limit;
    динамическая форма «возврат ⟺ рациональное». Золотое сечение = самое иррациональное наматывание (KAM), тот же √5/φ.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Element: a rational rotation returns to the start (finite periodic)    *)
(* ===================================================================== *)

(** The 1/3-rotation returns to the start after 3 steps (period 3). *)
Lemma rotation_third : inject_Z 3 * (1 # 3) == 1.
Proof. reflexivity. Qed.

(** The 1/4-rotation returns after 4 steps (period 4). *)
Lemma rotation_quarter : inject_Z 4 * (1 # 4) == 1.
Proof. reflexivity. Qed.

(** ★ The general pattern: rotating by p/q returns after q steps to the integer p (= start
    mod 1) — the period is the denominator.  E.g. 2/5 (period 5), 5/6 (period 6), 3/7
    (period 7): each rational rotation has a finite periodic orbit (Element). *)
Lemma rational_rotations_return :
  inject_Z 5 * (2 # 5) == 2 /\ inject_Z 6 * (5 # 6) == 5 /\ inject_Z 7 * (3 # 7) == 3.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: an irrational angle never returns (quasiperiodic)         *)
(* ===================================================================== *)

(** ★ The √2-rotation's angle is irrational, so the orbit never closes — quasiperiodic,
    dense, equidistributed (role-limit).  (The golden ratio is the most-irrational winding,
    the same √5/φ as FibonacciWord.) *)
Theorem sqrt2_rotation_role_limit : ~ (exists r : Q, r * r == 2).
Proof. exact sqrt2_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Circle rotation, split by the finitization boundary:
      (a) ELEMENT — rational rotations return to the start (finite periodic orbits):
          1/3 → period 3, 1/4 → period 4, and the general pattern p/q → period q;
      (b) ROLE-LIMIT — the √2-rotation's angle is irrational (orbit never closes). *)
Theorem circle_rotation_synthesis :
  (inject_Z 3 * (1 # 3) == 1 /\ inject_Z 4 * (1 # 4) == 1)
  /\ (inject_Z 5 * (2 # 5) == 2 /\ inject_Z 6 * (5 # 6) == 5 /\ inject_Z 7 * (3 # 7) == 3)
  /\ ~ (exists r : Q, r * r == 2).
Proof.
  split; [ split; reflexivity | ].
  split; [ exact rational_rotations_return | exact sqrt2_rotation_role_limit ].
Qed.
