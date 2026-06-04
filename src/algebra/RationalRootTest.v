(** * RationalRootTest.v — general Gauss lemma and the rational root test
    Elements: integers, coprimality (rel_prime), divisibility
    Roles:    Gauss's lemma as the rule "coprime divides a power => unit"
    Rules:    rel_prime x y, x | y^n => x = ±1  (any degree n)
    STATUS:   7 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    GENERALIZES the cube-specific `coprime_div_cube_unit` (AngleTrisection.v,
    degree 3) to EVERY degree, via Stdlib Znumtheory (Euclid / rel_prime).
    From it, the rational-root test: the n-th root of an integer is an integer
    or irrational (q = 1 in lowest terms). This subsumes √2,√3,√5 (n=2) and
    ∛2 (n=3) under one general criterion — the "общий критерий неприводимости"
    for the pure-root case.

    HONEST SCOPE: this is the rational-root / pure-power criterion (the heart
    of the rational root theorem). The full RRT for arbitrary integer
    polynomials, and irreducibility-as-nonfactorability, build on this but are
    not yet assembled here.
*)

From Stdlib Require Import ZArith Znumtheory Lia.
Open Scope Z_scope.

(* nat-indexed power over Z (definitional: zpow y (S k) = y * zpow y k) *)
Fixpoint zpow (y : Z) (n : nat) : Z :=
  match n with O => 1 | S k => y * zpow y k end.

(* coprime to 1 *)
Lemma rel_prime_x_1 : forall x, rel_prime x 1.
Proof.
  intro x. apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros c _ Hc1. exact Hc1.
Qed.

(* coprimality is preserved under powers: gcd(x,y)=1 => gcd(x, y^n)=1 *)
Lemma rel_prime_zpow : forall n x y, rel_prime x y -> rel_prime x (zpow y n).
Proof.
  induction n; intros x y H.
  - simpl. apply rel_prime_x_1.
  - simpl. apply rel_prime_mult.
    + exact H.
    + apply IHn. exact H.
Qed.

(* ===================== GENERAL Gauss lemma ===================== *)
(* x | y^n with gcd(x,y)=1  =>  x = ±1   (for ANY power n) *)
Theorem coprime_div_pow_unit : forall (x y : Z) (n : nat),
  rel_prime x y -> (x | zpow y n) -> x = 1 \/ x = -1.
Proof.
  intros x y n Hrp Hdiv.
  assert (Hrpn : rel_prime x (zpow y n)) by (apply rel_prime_zpow; exact Hrp).
  unfold rel_prime in Hrpn. destruct Hrpn as [_ _ Hgcd].
  assert (Hx1 : (x | 1)) by (apply Hgcd; [apply Z.divide_refl | exact Hdiv]).
  apply Zdivide_1. exact Hx1.
Qed.

(* ===================== Rational root test (pure-power form) ============= *)
(* If (p/q)^(S k) is an integer m with p,q coprime and q>0, then q = 1:
   the (S k)-th root of an integer is itself an integer, else irrational. *)
Theorem nth_root_integer_or_irrational :
  forall (p q : Z) (k : nat) (m : Z),
    q > 0 -> rel_prime p q -> zpow p (S k) = m * zpow q (S k) -> q = 1.
Proof.
  intros p q k m Hq Hrp Heq.
  assert (Hqp : rel_prime q p) by (apply rel_prime_sym; exact Hrp).
  assert (Hdvd : (q | zpow p (S k))).
  { exists (m * zpow q k). rewrite Heq. simpl. ring. }
  destruct (coprime_div_pow_unit q p (S k) Hqp Hdvd) as [H1 | Hm1].
  - exact H1.
  - lia.
Qed.

(* ===================== subsumes the repo's degree-specific lemmas ======= *)

Corollary gauss_square : forall x y : Z,
  rel_prime x y -> (x | zpow y 2) -> x = 1 \/ x = -1.
Proof. intros x y. apply coprime_div_pow_unit. Qed.

Corollary gauss_cube : forall x y : Z,
  rel_prime x y -> (x | zpow y 3) -> x = 1 \/ x = -1.
Proof. intros x y. apply coprime_div_pow_unit. Qed.
