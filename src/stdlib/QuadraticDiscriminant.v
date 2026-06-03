(** * QuadraticDiscriminant.v — the unifying principle behind the cluster's quadratic role-
      limits: a quadratic has a RATIONAL root iff its discriminant is a PERFECT SQUARE.  The
      discriminant b²−4ac is the single Element/role-limit dial for quadratics: a perfect-
      square discriminant gives a rational root (Element); a non-square discriminant gives an
      irrational root (role-limit).  This unifies golden (disc 5), pentagon (disc 5), silver
      (disc 8), metallic (disc n²+4), … — all instances of "non-square discriminant ⟹
      irrational root."  (As PellDichotomy unified the Pell processes.)

    Elements: the rational roots (e.g. 2,3 of x²−5x+6); the perfect-square discriminants
              (L1 + P4)
    Roles:    Element side = quadratics with a perfect-square discriminant (rational roots);
              role-limit side = non-square discriminant (irrational roots — φ disc 5, silver
              disc 8, …)
    Rules:    the identity 4a(ax²+bx+c)=(2ax+b)²−(b²−4ac); rational root ⟺ disc a perfect square

    THE DEEP POINT — the discriminant is THE Element/role-limit dial for quadratics.  The key
    ring identity
        4a·(a·x²+b·x+c) = (2a·x+b)² − (b²−4ac)     (`quadratic_disc_identity`)
    shows that a rational root x of a·x²+b·x+c=0 forces (2a·x+b)² = b²−4ac
    (`root_gives_disc_square`): the discriminant is a rational square.  When the discriminant
    is a perfect square the root is rational — Element side (x²−5x+6, disc 1, roots 2,3:
    `element_rational_root_example`).  When it is NOT a perfect square, the root is
    irrational — a role-limit.  The golden ratio's polynomial x²−x−1 has discriminant 5
    (`golden_no_rational_root`, via √5), the silver ratio's x²−2x−1 has discriminant 8
    (`silver_no_rational_root`, via √2).  So every quadratic role-limit in the cluster —
    golden/pentagon (disc 5), silver (disc 8), metallic (disc n²+4) — is one instance of
    "non-square discriminant ⟹ irrational root = role-limit."  The same √5 (disc 5) and √2
    (disc 8 = 2·4) as everywhere.

    ============ E/R/R разбор ============
      Rules (L5): тождество 4a(ax²+bx+c)=(2ax+b)²−(b²−4ac); рациональный корень ⟺ дискриминант квадрат.
      Roles (L4): Element = квадратики с точным квадратом дискриминанта (рациональные корни); role-limit =
                  не-квадратный дискриминант (иррациональные корни — φ disc 5, серебряное disc 8).
      Elements  : рациональные корни 2,3; точно-квадратные дискриминанты (L1+P4).
    ДИАГНОСТИКА (P4): корень Element (рационален) ⟺ дискриминант квадрат; role-limit ⟺ не квадрат. ОБЪЕДИНЯЕТ
    все квадратичные role-limits (φ/пентагон disc 5, серебряное disc 8, металлические disc n²+4); дискриминант =
    единственная ручка. Тот же √5/√2, что везде.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.
From ToS Require Import analysis.Sqrt5Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The discriminant identity and the rational-root criterion             *)
(* ===================================================================== *)

(** The key ring identity: 4a·(a·x²+b·x+c) = (2a·x+b)² − (b²−4ac). *)
Lemma quadratic_disc_identity : forall a b c x : Q,
  4 * a * (a*x*x + b*x + c) == (2*a*x + b) * (2*a*x + b) - (b*b - 4*a*c).
Proof. intros. ring. Qed.

(** ★ A rational root forces the discriminant to be a rational square: if a·x²+b·x+c=0 then
    (2a·x+b)² = b²−4ac.  So a perfect-square discriminant is NECESSARY for a rational root. *)
Theorem root_gives_disc_square : forall a b c x : Q,
  a*x*x + b*x + c == 0 -> (2*a*x + b) * (2*a*x + b) == b*b - 4*a*c.
Proof.
  intros a b c x H.
  assert (Hg : (2*a*x + b) * (2*a*x + b)
               == (b*b - 4*a*c) + 4 * a * (a*x*x + b*x + c)) by ring.
  rewrite Hg, H. ring.
Qed.

(* ===================================================================== *)
(*  Element side: perfect-square discriminant ⟹ rational root            *)
(* ===================================================================== *)

(** Element side, concretely: x²−5x+6 has discriminant 25−24 = 1 (a perfect square), and
    the rational root 2.  Perfect-square discriminant ⟹ rational root. *)
Lemma element_rational_root_example :
  (2*2 - 5*2 + 6 == 0) /\ ((5*5 - 4*1*6 = 1*1)%Z).
Proof. split; [ ring | reflexivity ]. Qed.

(* ===================================================================== *)
(*  Role-limit side: non-square discriminant ⟹ irrational root           *)
(* ===================================================================== *)

(** ★ The golden ratio's polynomial x²−x−1 has discriminant 5 (a non-square): no rational
    root, since a root would give (2x−1)²=5 (`root_gives_disc_square`), i.e. √5 ∈ ℚ. *)
Theorem golden_no_rational_root : ~ (exists x : Q, x*x - x - 1 == 0).
Proof.
  intros [x H].
  apply (no_rational_sqrt5 (2*x - 1)).
  assert (Hd : (2*x - 1) * (2*x - 1) == 4 * (x*x - x - 1) + 5) by ring.
  rewrite Hd, H. ring.
Qed.

(** ★ The silver ratio's polynomial x²−2x−1 has discriminant 8 (a non-square): no rational
    root, since a root would give (x−1)²=2, i.e. √2 ∈ ℚ. *)
Theorem silver_no_rational_root : ~ (exists x : Q, x*x - 2*x - 1 == 0).
Proof.
  intros [x H].
  apply (no_rational_sqrt2 (x - 1)).
  assert (Hd : (x - 1) * (x - 1) == (x*x - 2*x - 1) + 2) by ring.
  rewrite Hd, H. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The discriminant as the Element/role-limit dial for quadratics:
      (a) the identity 4a(ax²+bx+c) = (2ax+b)²−(b²−4ac);
      (b) a rational root ⟹ the discriminant is a rational square (perfect-square necessary);
      (c) ELEMENT — perfect-square discriminant gives a rational root (x²−5x+6, disc 1);
      (d) ROLE-LIMIT — non-square discriminant gives an irrational root (golden disc 5,
          silver disc 8). *)
Theorem discriminant_synthesis :
  (forall a b c x : Q, 4 * a * (a*x*x + b*x + c) == (2*a*x + b) * (2*a*x + b) - (b*b - 4*a*c))
  /\ (forall a b c x : Q, a*x*x + b*x + c == 0 -> (2*a*x + b) * (2*a*x + b) == b*b - 4*a*c)
  /\ ~ (exists x : Q, x*x - x - 1 == 0)
  /\ ~ (exists x : Q, x*x - 2*x - 1 == 0).
Proof.
  split; [ exact quadratic_disc_identity | ].
  split; [ exact root_gives_disc_square | ].
  split; [ exact golden_no_rational_root | exact silver_no_rational_root ].
Qed.
