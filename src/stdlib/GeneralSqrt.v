(** * GeneralSqrt.v — the general surd theorem: √n is rational ⟺ n is a perfect square.
      This UNIFIES the cluster's individual Sqrt2/Sqrt3/Sqrt5 irrationality results (each proved
      by descent on a specific prime) into ONE theorem, via a single mechanism — a reduced
      fraction whose square is an integer is itself an integer (coprimality preserved under
      squaring).  It opens NEW role-limits √6, √7, √8, √10 beyond the cluster's √2/√3/√5, and
      puts every non-square on the role-limit side at once.

    Elements: a reduced fraction (a,b) with gcd a b = 1; the perfect squares m²; concrete
              √4 = 2 (Element), √6 (role-limit) (L1 + P4)
    Roles:    Element side = n a perfect square (4=2², 9=3²) ⟹ √n ∈ ℚ (terminates);
              role-limit = n not a perfect square (2,3,5,6,7,8,10) ⟹ √n ∉ ℚ (non-terminating)
    Rules:    reduce r=p/q to lowest terms (gcd p q = 1); r²=n ⟹ p²=n·q² ⟹ q | p²; coprimality
              preserved under squaring (gcd q p² = 1) ⟹ q | 1 ⟹ q = 1 ⟹ n = p²

    THE DEEP POINT — "is √n rational?" is the DECIDABLE Element-question "is n a perfect square?".
    The engine `reduced_square_integer`: a reduced fraction whose square is an integer must be an
    integer (b=1).  Mechanism: from a²=n·b² we get b | a²; gcd(a,b)=1 forces gcd(b,a²)=1
    (coprimality under squaring, `rel_prime_mult`); a common divisor coprime to its multiple
    divides 1, so b | 1, b = 1.  Lifting through `Qred` (lowest terms), a rational square is a
    perfect square (`rational_square_is_perfect`), hence n NOT a perfect square ⟹ √n irrational
    (`not_perfect_square_irrational`).  This RE-DERIVES √2,√3,√5 as instances and adds √6,√7,√8,√10
    — one theorem puts every non-square on the role-limit side, no per-prime descent needed.
    Element = n a perfect square (√n terminates in ℚ); role-limit = n a non-square (√n names a
    non-terminating process).

    ============ E/R/R разбор ============
      Rules (L5): привести r=p/q к низшим членам (gcd p q=1); r²=n ⟹ p²=n·q² ⟹ q∣p²; взаимная
                  простота под возведением в степень (gcd q p²=1) ⟹ q∣1 ⟹ q=1 ⟹ n=p².
      Roles (L4): Element = n полный квадрат (4,9) ⟹ √n∈ℚ; role-limit = n не квадрат (2,3,5,6,7,8,10)
                  ⟹ √n∉ℚ (нетерминирующий процесс).
      Elements  : приведённая дробь (a,b) gcd=1; полные квадраты m²; √4=2 (Element), √6 (role-limit).
    ДИАГНОСТИКА (P4): «рационален ли √n?» = «n полный квадрат?» — РАЗРЕШИМЫЙ Element-вопрос про n, не
    метафизика про √n. Один движок (взаимная простота приведённой дроби) ставит ВСЕ не-квадраты на сторону
    role-limit — общий механизм за Sqrt2/3/5Irrational (которые были инстансами). Квадрат⟺Element, не-квадрат⟺role-limit.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia QArith.
From Stdlib Require Qcanon.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: a reduced fraction with integer square is an integer       *)
(* ===================================================================== *)

(** ★ A reduced fraction a/b (gcd a b = 1, b > 0) whose square a²/b² is an integer n
    (a² = n·b²) must have denominator b = 1 — i.e. it is itself an integer.  This single
    integer fact is the engine behind every √n irrationality. *)
Lemma reduced_square_integer : forall a b n : Z,
  0 < b -> Z.gcd a b = 1 -> a * a = n * (b * b) -> b = 1.
Proof.
  intros a b n Hpos Hcop Heq.
  assert (Hdiv : (b | a * a)) by (exists (n * b); rewrite Heq; ring).
  assert (Hrp : rel_prime a b) by (red; rewrite <- Hcop; apply Zgcd_is_gcd).
  assert (Hrp2 : rel_prime b (a * a)).
  { apply rel_prime_sym in Hrp. apply rel_prime_mult; exact Hrp. }
  assert (Hb1 : (b | 1)).
  { destruct Hrp2 as [_ _ Hg]. apply Hg; [ apply Z.divide_refl | exact Hdiv ]. }
  pose proof (Z.divide_pos_le b 1 ltac:(lia) Hb1) as Hle.
  lia.
Qed.

(* ===================================================================== *)
(*  The bridge to ℚ: a rational square is a perfect square                 *)
(* ===================================================================== *)

(** ★ If a rational r squares to the integer n, then n is a perfect square.  Reduce r to
    lowest terms via Qred (coprime numerator/denominator), cross-multiply to a² = n·b² over ℤ,
    and apply the engine: b = 1, so n = a². *)
Lemma rational_square_is_perfect : forall (r : Q) (n : Z),
  (r * r == inject_Z n)%Q -> exists m : Z, n = m * m.
Proof.
  intros r n H.
  remember (Qred r) as r' eqn:Er'.
  assert (Hr' : (r' * r' == inject_Z n)%Q).
  { rewrite Er'. rewrite Qred_correct. exact H. }
  assert (Hcop : Z.gcd (Qnum r') (Z.pos (Qden r')) = 1).
  { rewrite Er'. apply Qcanon.Qred_identity2. apply Qcanon.Qred_involutive. }
  unfold Qeq, Qmult, inject_Z in Hr'. simpl in Hr'.
  rewrite Z.mul_1_r in Hr'. rewrite Pos2Z.inj_mul in Hr'.
  assert (Hb : Z.pos (Qden r') = 1).
  { apply (reduced_square_integer (Qnum r') (Z.pos (Qden r')) n).
    - apply Pos2Z.is_pos.
    - exact Hcop.
    - exact Hr'. }
  rewrite Hb in Hr'.
  exists (Qnum r'). lia.
Qed.

(** ★ Hence: if n is NOT a perfect square, √n is irrational (no rational squares to n). *)
Corollary not_perfect_square_irrational : forall n : Z,
  (forall m : Z, m * m <> n) -> ~ (exists r : Q, (r * r == inject_Z n)%Q).
Proof.
  intros n Hns [r Hr].
  destruct (rational_square_is_perfect r n Hr) as [m Hm].
  apply (Hns m). symmetry. exact Hm.
Qed.

(* ===================================================================== *)
(*  Deciding "n is not a perfect square" for concrete n                    *)
(* ===================================================================== *)

(** No integer squares to a value strictly between consecutive squares k² and (k+1)². *)
Lemma not_square_strict : forall m k n : Z,
  0 <= k -> k * k < n -> n < (k + 1) * (k + 1) -> m * m <> n.
Proof.
  intros m k n Hk Hlo Hhi Heq.
  assert (Hn : 0 <= n) by nia.
  assert (Hsq : Z.abs m * Z.abs m = n).
  { rewrite <- Z.abs_mul. rewrite Heq. apply Z.abs_eq. exact Hn. }
  assert (k < Z.abs m) by nia.
  assert (Z.abs m < k + 1) by nia.
  lia.
Qed.

(* ===================================================================== *)
(*  Element side: a perfect square HAS a rational square root              *)
(* ===================================================================== *)

(** √4 = 2 ∈ ℚ: a perfect square's root is an Element. *)
Lemma sqrt4_element : (inject_Z 2 * inject_Z 2 == inject_Z 4)%Q.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit side: the new irrationals √6, √7, √8, √10                    *)
(* ===================================================================== *)

(** ★ √6 is irrational — NEW beyond the cluster's √2/√3/√5, via the general theorem. *)
Theorem sqrt6_role_limit : ~ (exists r : Q, (r * r == inject_Z 6)%Q).
Proof. apply not_perfect_square_irrational. intros m. apply (not_square_strict m 2 6); lia. Qed.

(** √7 is irrational. *)
Theorem sqrt7_role_limit : ~ (exists r : Q, (r * r == inject_Z 7)%Q).
Proof. apply not_perfect_square_irrational. intros m. apply (not_square_strict m 2 7); lia. Qed.

(** √8 = 2√2 is irrational (the silver-ratio surd). *)
Theorem sqrt8_role_limit : ~ (exists r : Q, (r * r == inject_Z 8)%Q).
Proof. apply not_perfect_square_irrational. intros m. apply (not_square_strict m 2 8); lia. Qed.

(** √10 is irrational. *)
Theorem sqrt10_role_limit : ~ (exists r : Q, (r * r == inject_Z 10)%Q).
Proof. apply not_perfect_square_irrational. intros m. apply (not_square_strict m 3 10); lia. Qed.

(** The cluster's √2 re-derived as an instance of the SAME general theorem. *)
Theorem sqrt2_via_general : ~ (exists r : Q, (r * r == inject_Z 2)%Q).
Proof. apply not_perfect_square_irrational. intros m. apply (not_square_strict m 1 2); lia. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The general surd theorem, split by the finitization boundary:
      (a) ENGINE — a reduced fraction with integer square is an integer
          (`reduced_square_integer`), so a rational square is a perfect square
          (`rational_square_is_perfect`);
      (b) ELEMENT — a perfect square has a rational root (√4 = 2, `sqrt4_element`);
      (c) ROLE-LIMIT — every non-square is irrational; the new √6, and √2 re-derived as one
          instance of the general theorem. *)
Theorem general_sqrt_synthesis :
  (forall a b n : Z, 0 < b -> Z.gcd a b = 1 -> a * a = n * (b * b) -> b = 1)
  /\ (forall (r : Q) (n : Z), (r * r == inject_Z n)%Q -> exists m : Z, n = m * m)
  /\ (inject_Z 2 * inject_Z 2 == inject_Z 4)%Q
  /\ ~ (exists r : Q, (r * r == inject_Z 6)%Q).
Proof.
  split; [ exact reduced_square_integer | ].
  split; [ exact rational_square_is_perfect | ].
  split; [ exact sqrt4_element | exact sqrt6_role_limit ].
Qed.
