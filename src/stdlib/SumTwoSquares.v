(** * SumTwoSquares.v — which circles x²+y²=n have rational points?  The unit
      circle is densely rational (Pythagoras), and x²+y²=2, x²+y²=5 have rational
      points (Elements), but x²+y²=3 has NONE (a role-limit): 3 is not a sum of two
      rational squares (3 ≡ 3 mod 4).

    Elements: the rational points (1,1) on x²+y²=2 and (1,2) on x²+y²=5; the integer
              triple (a,b,c); the numbers n=1,2,5 (L1 + P4)
    Roles:    the rational points of x²+y²=n = the Element side (dense, like the unit
              circle) vs the EMPTY circle x²+y²=3 = a role-limit (no rational point);
              the number n = "good" (a sum of two squares, an Element circle) or "bad"
              (a role-limit circle, n ≡ 3 mod 4)
    Rules:    the equation x²+y²=n; the mod-3 obstruction (squares mod 3 ∈ {0,1}, so
              3 | a²+b² ⟹ 3|a ∧ 3|b); infinite descent on |a|+|b|+|c|; Fermat's
              two-square theorem

    THE DEEP POINT — whether a circle has rational points is an Element/role-limit
    split, and scaling decides it.  The unit circle x²+y²=1 is DENSELY rational
    (Pythagorean triples, `ConicDuality.v`/`PythagoreanTriples.v`) — the Element side.
    The circles x²+y²=2 and x²+y²=5 also have rational points (`circle2_point`,
    `circle5_point`): 2 and 5 are sums of two squares.  But the circle x²+y²=3 has
    NOT A SINGLE rational point (`circle3_no_rational_point`): 3 is not a sum of two
    rational squares.  The proof is mod-3 + infinite descent: any integer solution of
    the homogeneous form a²+b²=3c² has 3|a and 3|b (squares mod 3 are 0 or 1, so a
    sum ≡ 0 forces both ≡ 0), then 3|c, and dividing through descends to (0,0,0) — so
    the only solution is trivial, i.e. no rational point.  A role-limit circle: the
    Element (a rational point) simply does not exist there, even though the unit
    circle next to it teems with them.  Which n admit the Element is Fermat's
    two-square theorem (n ≡ 3 mod 4 with 3 ∤ … is "bad").

    ============ E/R/R разбор ============
      Rules (L5): уравнение x²+y²=n; обструкция mod 3 (квадраты mod 3 ∈{0,1}, 3|a²+b²⟹
                  3|a∧3|b); бесконечный спуск по |a|+|b|+|c|; теорема Ферма о двух квадратах.
      Roles (L4): рациональные точки x²+y²=n = Element (плотны) vs пустая x²+y²=3 = role-limit;
                  n = «хорошее» (сумма двух квадратов) или «плохое» (≡3 mod 4).
      Elements  : точки (1,1) на =2, (1,2) на =5; целая тройка; n=1,2,5 (L1+P4).
    ДИАГНОСТИКА (P4): рациональные точки x²+y²=n Element-сторонни для «хороших» n (2,5,…), но ПУСТЫ
    для «плохих» (3≡3 mod4). Окружность радиуса √3 имеет НОЛЬ рациональных точек; 3 — не сумма двух
    рациональных квадратов (спуск mod 3). Единичная окружность рядом плотно-рациональна.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith Znumtheory Lqa.
From ToS Require Import analysis.Sqrt3Irrational.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Squares mod 3 ∈ {0,1}, hence 3 | a²+b² ⟹ 3|a ∧ 3|b             *)
(* ================================================================= *)

Lemma sq_mod3 : forall n : Z, (n * n) mod 3 = 0 \/ (n * n) mod 3 = 1.
Proof.
  intro n. rewrite (Z.mul_mod n n 3) by lia.
  pose proof (Z.mod_pos_bound n 3 ltac:(lia)) as Hb.
  destruct (Z.eq_dec (n mod 3) 0) as [E | N0].
  - rewrite E. left. reflexivity.
  - destruct (Z.eq_dec (n mod 3) 1) as [E1 | N1].
    + rewrite E1. right. reflexivity.
    + assert (E2 : n mod 3 = 2) by lia. rewrite E2. right. reflexivity.
Qed.

Lemma three_div_sum_sq : forall a b : Z, (3 | a*a + b*b) -> (3 | a) /\ (3 | b).
Proof.
  intros a b H.
  assert (H0 : (a*a + b*b) mod 3 = 0).
  { destruct H as [k Hk]. rewrite Hk. apply Z.mod_mul. lia. }
  rewrite (Z.add_mod (a*a) (b*b) 3) in H0 by lia.
  destruct (sq_mod3 a) as [Ha | Ha]; destruct (sq_mod3 b) as [Hb | Hb];
    rewrite Ha, Hb in H0; try discriminate.
  split.
  - apply three_div_sq. apply Z.mod_divide; [ lia | exact Ha ].
  - apply three_div_sq. apply Z.mod_divide; [ lia | exact Hb ].
Qed.

(* ================================================================= *)
(** ** Descent: every integer solution of a²+b²=3c² is divisible by 3 *)
(* ================================================================= *)

Lemma descent_step : forall a b c : Z,
  a*a + b*b = 3*(c*c) ->
  exists a' b' c', a = 3*a' /\ b = 3*b' /\ c = 3*c' /\ a'*a' + b'*b' = 3*(c'*c').
Proof.
  intros a b c Heq.
  destruct (three_div_sum_sq a b) as [Ha Hb].
  { exists (c*c). lia. }
  destruct Ha as [a' Ha']. destruct Hb as [b' Hb'].   (* a=a'*3, b=b'*3 *)
  assert (HH : (a'*3)*(a'*3) + (b'*3)*(b'*3) = 9*(a'*a' + b'*b')) by ring.
  rewrite Ha', Hb' in Heq. rewrite HH in Heq.          (* Heq: 9X = 3c² *)
  assert (Hc2 : c*c = 3*(a'*a' + b'*b')) by lia.
  assert (Hc : (3 | c)).
  { apply three_div_sq. exists (a'*a' + b'*b'). lia. }
  destruct Hc as [c' Hc'].                              (* c=c'*3 *)
  assert (Hcc : c*c = 9*(c'*c')) by (rewrite Hc'; ring).
  exists a', b', c'.
  split. lia. split. lia. split. lia.
  lia.
Qed.

Lemma descent_to_zero : forall n : nat, forall a b c : Z,
  Z.to_nat (Z.abs a + Z.abs b + Z.abs c) = n ->
  a*a + b*b = 3*(c*c) ->
  a = 0 /\ b = 0 /\ c = 0.
Proof.
  intro n. induction n as [n IH] using lt_wf_ind.
  intros a b c Hn Heq.
  destruct (Z.eq_dec c 0) as [Hc0 | Hcn0].
  - subst c. (* a²+b² = 0 ⟹ a=0 ∧ b=0 *)
    assert (Hsum : a*a + b*b = 0) by lia.
    assert (Haa : a*a = 0).
    { assert (0 <= a*a) by nia. assert (0 <= b*b) by nia. lia. }
    assert (Hbb : b*b = 0) by lia.
    assert (Ha0 : a = 0) by (apply Z.mul_eq_0 in Haa; destruct Haa; assumption).
    assert (Hb0 : b = 0) by (apply Z.mul_eq_0 in Hbb; destruct Hbb; assumption).
    subst. auto.
  - destruct (descent_step a b c Heq) as [a' [b' [c' [Ha [Hb [Hc Heq']]]]]].
    assert (Hlt : (Z.to_nat (Z.abs a' + Z.abs b' + Z.abs c') < n)%nat).
    { subst a b c n.
      rewrite !Z.abs_mul. simpl (Z.abs 3).
      assert (0 <= Z.abs a') by apply Z.abs_nonneg.
      assert (0 <= Z.abs b') by apply Z.abs_nonneg.
      assert (0 <= Z.abs c') by apply Z.abs_nonneg.
      assert (Hcpos : 0 < Z.abs c').
      { apply Z.abs_pos. intro. apply Hcn0. lia. }
      apply Z2Nat.inj_lt; lia. }
    destruct (IH _ Hlt a' b' c' eq_refl Heq') as [Ha'0 [Hb'0 Hc'0]].
    subst. repeat split; lia.
Qed.

(* ================================================================= *)
(** ** x²+y²=3 has no rational point (3 is not a sum of two squares)  *)
(* ================================================================= *)

(** ★ The homogeneous form a²+b²=3c² has only the trivial integer solution — i.e.
    the circle x²+y²=3 has NO rational point.  (A rational point (a/c, b/c) would
    give a non-trivial integer solution with c≠0.) *)
Theorem circle3_no_rational_point : forall a b c : Z,
  a*a + b*b = 3*(c*c) -> a = 0 /\ b = 0 /\ c = 0.
Proof.
  intros a b c Heq.
  apply (descent_to_zero (Z.to_nat (Z.abs a + Z.abs b + Z.abs c)) a b c).
  - reflexivity.
  - exact Heq.
Qed.

(* ================================================================= *)
(** ** The "good" circles x²+y²=2 and x²+y²=5 DO have rational points  *)
(* ================================================================= *)

Open Scope Q_scope.

(** 2 is a sum of two squares: (1,1) is a rational point on x²+y²=2. *)
Theorem circle2_point : (1#1)*(1#1) + (1#1)*(1#1) == 2.
Proof. vm_compute. reflexivity. Qed.

(** 5 is a sum of two squares: (1,2) is a rational point on x²+y²=5. *)
Theorem circle5_point : (1#1)*(1#1) + (2#1)*(2#1) == 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** Synthesis                                                      *)
(* ================================================================= *)

(** Which circles have rational points, split by the finitization boundary:
      (a) x²+y²=2 has the rational point (1,1) — an Element circle;
      (b) x²+y²=5 has the rational point (1,2) — an Element circle;
      (c) x²+y²=3 has NO rational point (only the trivial homogeneous solution) — a
          role-limit circle (3 is not a sum of two rational squares). *)
Theorem sum_two_squares_synthesis :
  ((1#1)*(1#1) + (1#1)*(1#1) == 2)
  /\ ((1#1)*(1#1) + (2#1)*(2#1) == 5)
  /\ (forall a b c : Z, (a*a + b*b = 3*(c*c))%Z -> (a = 0 /\ b = 0 /\ c = 0)%Z).
Proof.
  split; [ exact circle2_point | ].
  split; [ exact circle5_point | exact circle3_no_rational_point ].
Qed.
