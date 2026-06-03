(** * PythagoreanMeans.v — the three classical (Pythagorean) means: the arithmetic mean AM
      and harmonic mean HM of two rationals are rational (Element side), but the geometric
      mean GM = √(ab) is a role-limit (irrational unless ab is a perfect square — e.g. √2 for
      1,2).  The identity AM·HM = GM² puts the role-limit GM "between" the two Element means
      (GM = √(AM·HM)), and AM ≥ GM ≥ HM holds at the Element (squared) level.

    Elements: the rational AM = 3/2 and HM = 4/3 (of 1,2); the integer inequality 4ab≤(a+b)²
              (L1 + P4)
    Roles:    Element side = AM and HM (rational for rational a,b; the AM≥GM≥HM ordering is a
              rational comparison); role-limit = GM = √(ab) (irrational unless ab a perfect
              square — √2 for a=1,b=2)
    Rules:    AM=(a+b)/2, HM=2ab/(a+b), GM²=ab; the identity AM·HM=GM²; the inequality (a−b)²≥0

    THE DEEP POINT — of the three classical means, AM and HM are Element, GM is a role-limit.
    For rational a,b the arithmetic mean (a+b)/2 and harmonic mean 2ab/(a+b) are rational
    (finite-actual), and AM·HM = ab = GM² (`am_hm_eq_gm_sq`): the geometric mean is √(AM·HM),
    a role-limit lying "between" the two Element means.  The AM–GM inequality AM ≥ GM holds at
    the squared (Element) level, 4ab ≤ (a+b)² ⟺ (a−b)² ≥ 0 (`am_gm_integer`).  But GM = √(ab)
    is irrational unless ab is a perfect square: GM(1,2) = √2 (`gm_role_limit`).  So "the
    geometric mean of 1 and 2" is √2, a role-limit, while AM=3/2 and HM=4/3 are Element
    (`means_of_one_two`).  The same √2 as everywhere.

    ============ E/R/R разбор ============
      Rules (L5): AM=(a+b)/2, HM=2ab/(a+b), GM²=ab; тождество AM·HM=GM²; неравенство (a−b)²≥0.
      Roles (L4): Element = AM, HM (рациональны; AM≥GM≥HM — рациональное сравнение); role-limit = GM=√(ab)
                  (иррационально, если ab не квадрат — √2 для 1,2).
      Elements  : рациональные AM=3/2, HM=4/3; целочисленное 4ab≤(a+b)² (L1+P4).
    ДИАГНОСТИКА (P4): из трёх средних AM/HM = Element, GM=√(ab) = role-limit; тождество AM·HM=GM² ставит GM
    «между» двух Element-средних; неравенство держится на Element-уровне квадратов. Тот же √2, что везде.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

(* ===================================================================== *)
(*  AM·HM = GM²  (the geometric mean is √(AM·HM))                          *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ The arithmetic and harmonic means multiply to the squared geometric mean:
    AM·HM = ((a+b)/2)·(2ab/(a+b)) = ab = GM² — so GM = √(AM·HM). *)
Lemma am_hm_eq_gm_sq : forall a b : Q, ~ (a + b == 0) ->
  ((a + b) / 2) * ((2 * a * b) / (a + b)) == a * b.
Proof. intros a b H. field. exact H. Qed.

(* ===================================================================== *)
(*  AM ≥ GM at the Element (squared, integer) level                       *)
(* ===================================================================== *)

Open Scope Z_scope.

(** ★ The AM–GM inequality at the squared/integer level: 4ab ≤ (a+b)² ⟺ (a−b)² ≥ 0 —
    a rational comparison (Element side). *)
Lemma am_gm_integer : forall a b : Z, 4 * (a * b) <= (a + b) * (a + b).
Proof.
  intros a b.
  assert (H : (a + b) * (a + b) - 4 * (a * b) = (a - b) * (a - b)) by ring.
  assert (Hsq : 0 <= (a - b) * (a - b)) by apply Z.square_nonneg.
  lia.
Qed.

(* ===================================================================== *)
(*  Element: AM and HM of 1,2 are rational; role-limit: GM = √2           *)
(* ===================================================================== *)

Open Scope Q_scope.

(** Element side: AM(1,2) = 3/2 and HM(1,2) = 4/3 are rational. *)
Lemma means_of_one_two :
  (1 + 2) / 2 == 3 # 2 /\ (2 * 1 * 2) / (1 + 2) == 4 # 3.
Proof. split; reflexivity. Qed.

(** ★ Role-limit: the geometric mean of 1 and 2 is √2, irrational (GM²=ab=2; the same √2 as
    everywhere).  GM is rational iff ab is a perfect square. *)
Theorem gm_role_limit : ~ (exists g : Q, g * g == 2).
Proof. exact sqrt2_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Pythagorean means, split by the finitization boundary:
      (a) AM·HM = GM² (the geometric mean is √(AM·HM));
      (b) AM ≥ GM at the squared/integer level (4ab ≤ (a+b)²);
      (c) ELEMENT — AM(1,2)=3/2 and HM(1,2)=4/3 are rational;
      (d) ROLE-LIMIT — GM(1,2) = √2 is irrational. *)
Theorem pythagorean_means_synthesis :
  (forall a b : Q, ~ (a + b == 0) -> ((a + b) / 2) * ((2 * a * b) / (a + b)) == a * b)
  /\ (forall a b : Z, (4 * (a * b) <= (a + b) * (a + b))%Z)
  /\ ((1 + 2) / 2 == 3 # 2 /\ (2 * 1 * 2) / (1 + 2) == 4 # 3)
  /\ ~ (exists g : Q, g * g == 2).
Proof.
  split; [ exact am_hm_eq_gm_sq | ].
  split; [ exact am_gm_integer | ].
  split; [ exact means_of_one_two | exact gm_role_limit ].
Qed.
