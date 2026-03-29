(** * StoneWeierstrass.v -- Uniform Approximation by Bernstein Polynomials

    Theory of Systems -- Analysis (Stone-Weierstrass via Bernstein)

    Wiedijk-style: concrete Bernstein polynomial approximation over Q.
    Every continuous function on [0,1] can be uniformly approximated
    by polynomials — here we build the machinery concretely.

    Elements: polynomials (finite), function values, binomial coefficients
    Roles:    polynomial -> Approximator, function -> Target, error -> Bound
    Rules:    partition of unity (Bernstein basis sums to 1),
              reproduction of constants and linear functions
    Status:   finite_approximation | exact_reproduction | error_bounded

    P4 significance: polynomials are FINITE (Elements),
    continuous functions are PROCESSES (P4).
    Approximation = finite Elements approaching a Process.

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================= *)
(** ** Section 1: Binomial Coefficients *)
(* ================================================================= *)

Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binom n' k' + binom n' (S k'))%nat
  end.

Lemma binom_0_r : forall n, binom n O = 1%nat.
Proof. destruct n; reflexivity. Qed.

Lemma binom_gt : forall n k, (n < k)%nat -> binom n k = 0%nat.
Proof.
  induction n; intros k Hlt.
  - destruct k; [lia | reflexivity].
  - destruct k; [lia | simpl].
    rewrite IHn by lia. rewrite IHn by lia. lia.
Qed.

Lemma binom_n_n : forall n, binom n n = 1%nat.
Proof.
  induction n; [reflexivity | simpl].
  assert (Hgt: (n < S n)%nat) by lia.
  rewrite (binom_gt n (S n) Hgt).
  rewrite IHn. reflexivity.
Qed.

(* ================================================================= *)
(** ** Section 2: Rational Power *)
(* ================================================================= *)

Fixpoint qpower (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S m => x * qpower x m
  end.

Lemma qpower_0 : forall x, qpower x O = 1.
Proof. reflexivity. Qed.

Lemma qpower_1 : forall x, qpower x 1 == x.
Proof. intros. simpl. ring. Qed.

Lemma qpower_S : forall x n, qpower x (S n) == x * qpower x n.
Proof. intros. simpl. ring. Qed.

(* ================================================================= *)
(** ** Section 3: Bernstein Basis Polynomials *)
(* ================================================================= *)

Definition bernstein_basis (n k : nat) (x : Q) : Q :=
  inject_Z (Z.of_nat (binom n k)) * qpower x k * qpower (1 - x) (n - k).

(** Concrete computations for n=1 *)

Lemma bernstein_1_0 : forall x, bernstein_basis 1 O x == 1 - x.
Proof.
  intros. unfold bernstein_basis. simpl.
  ring.
Qed.

Lemma bernstein_1_1 : forall x, bernstein_basis 1 1 x == x.
Proof.
  intros. unfold bernstein_basis. simpl.
  ring.
Qed.

(** Concrete computations for n=2 *)

Lemma bernstein_2_0 : forall x,
  bernstein_basis 2 O x == (1 - x) * (1 - x).
Proof.
  intros. unfold bernstein_basis. simpl.
  ring.
Qed.

Lemma bernstein_2_1 : forall x,
  bernstein_basis 2 1 x == inject_Z 2 * x * (1 - x).
Proof.
  intros. unfold bernstein_basis. simpl.
  ring.
Qed.

Lemma bernstein_2_2 : forall x,
  bernstein_basis 2 2 x == x * x.
Proof.
  intros. unfold bernstein_basis. simpl.
  ring.
Qed.

(* ================================================================= *)
(** ** Section 4: Partition of Unity *)
(* ================================================================= *)

(** Sum of Bernstein basis polynomials *)
Fixpoint bernstein_sum (n : nat) (k : nat) (x : Q) : Q :=
  match k with
  | O => bernstein_basis n O x
  | S k' => bernstein_sum n k' x + bernstein_basis n (S k') x
  end.

(** Partition of unity for n=1: B_{1,0}(x) + B_{1,1}(x) = 1 *)
Lemma partition_of_unity_1 : forall x,
  bernstein_sum 1 1 x == 1.
Proof.
  intros. simpl.
  unfold bernstein_basis. simpl.
  ring.
Qed.

(** Partition of unity for n=2: B_{2,0} + B_{2,1} + B_{2,2} = 1 *)
Lemma partition_of_unity_2 : forall x,
  bernstein_sum 2 2 x == 1.
Proof.
  intros. simpl.
  unfold bernstein_basis. simpl.
  ring.
Qed.

(* ================================================================= *)
(** ** Section 5: Bernstein Polynomial of a Function *)
(* ================================================================= *)

(** Bernstein polynomial: B_n(f,x) = sum_{k=0}^{n} f(k/n) * B_{n,k}(x)
    We define for n >= 1 using a helper that accumulates the sum. *)

Fixpoint bernstein_poly_aux (f : Q -> Q) (n : nat) (k : nat) (x : Q) : Q :=
  match k with
  | O => f 0 * bernstein_basis n O x
  | S k' =>
      bernstein_poly_aux f n k' x +
      f (inject_Z (Z.of_nat (S k')) / inject_Z (Z.of_nat n)) * bernstein_basis n (S k') x
  end.

Definition bernstein_poly (f : Q -> Q) (n : nat) (x : Q) : Q :=
  bernstein_poly_aux f n n x.

(** B_1(f,x) = f(0)(1-x) + f(1)x -- linear interpolation *)
Lemma bernstein_poly_1_linear : forall (f : Q -> Q) x,
  bernstein_poly f 1 x ==
    f 0 * (1 - x) + f (inject_Z 1 / inject_Z 1) * x.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  ring.
Qed.

(* ================================================================= *)
(** ** Section 6: Bernstein Reproduces Constants *)
(* ================================================================= *)

(** For a constant function f(x) = c, B_1(c, x) = c *)
Lemma bernstein_reproduces_const_1 : forall (c x : Q),
  bernstein_poly (fun _ => c) 1 x == c.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  ring.
Qed.

(** For a constant function f(x) = c, B_2(c, x) = c *)
Lemma bernstein_reproduces_const_2 : forall (c x : Q),
  bernstein_poly (fun _ => c) 2 x == c.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  ring.
Qed.

(* ================================================================= *)
(** ** Section 7: Bernstein Reproduces Linear Functions *)
(* ================================================================= *)

(** B_1(id, x) = x *)
Lemma bernstein_reproduces_id_1 : forall x,
  bernstein_poly (fun t => t) 1 x == x.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  field; discriminate.
Qed.

(** B_2(id, x) = x *)
Lemma bernstein_reproduces_id_2 : forall x,
  bernstein_poly (fun t => t) 2 x == x.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  field; discriminate.
Qed.

(* ================================================================= *)
(** ** Section 8: Approximation Error for x^2 *)
(* ================================================================= *)

(** B_2(x^2, x) = x^2 + ... but we need f(k/n) = (k/n)^2.
    For n=2: f(0)=0, f(1/2)=1/4, f(1)=1.
    B_2(x^2,x) = 0*B_{2,0} + (1/4)*B_{2,1} + 1*B_{2,2}
               = (1/4)*2x(1-x) + x^2
               = x(1-x)/2 + x^2
               = x^2 + x(1-x)/2 *)
Lemma bernstein_x2_n2 : forall x,
  bernstein_poly (fun t => t * t) 2 x == x * x + x * (1 - x) / inject_Z 2.
Proof.
  intros. unfold bernstein_poly. simpl.
  unfold bernstein_basis. simpl.
  field; discriminate.
Qed.

(** The error term x(1-x)/2 shows the approximation gap.
    For general n, the error is x(1-x)/n.
    On [0,1], x(1-x) <= 1/4, so error <= 1/(4n) -> 0. *)

(** Error bound: x(1-x) <= 1/4 when 0 <= x <= 1 *)
Lemma Qsquare_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intros q.
  destruct (Qlt_le_dec q 0).
  - assert (H1: 0 < -q) by lra.
    assert (H2: 0 < (-q) * (-q)).
    { apply Qmult_lt_0_compat; lra. }
    assert (H3: (-q) * (-q) == q * q) by ring.
    lra.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma unit_interval_variance_bound : forall x,
  0 <= x -> x <= 1 -> 4 * (x * (1 - x)) <= 1.
Proof.
  intros x Hx0 Hx1.
  assert (Hsq := Qsquare_nonneg (2 * x - 1)).
  lra.
Qed.

(* ================================================================= *)
(** ** Section 9: ToS Interpretation *)
(* ================================================================= *)

(** P4 significance theorem: polynomials are finitely determined.
    A polynomial of degree n is determined by n+1 coefficients.
    This is the FINITE (Element) side of approximation. *)

Definition is_polynomial_approx (p : Q -> Q) (f : Q -> Q) (eps : Q) : Prop :=
  forall x, 0 <= x -> x <= 1 -> Qabs (p x - f x) <= eps.

(** The Bernstein polynomial B_1 exactly reproduces the identity *)
(** Zero error means p(x) = f(x), so |p(x)-f(x)| = 0 <= 0 *)
Lemma qabs_zero_le : forall q, q == 0 -> Qabs q <= 0.
Proof.
  intros q Hq.
  rewrite Hq. simpl. lra.
Qed.

Lemma bernstein_1_exact_on_id : is_polynomial_approx
  (fun x => bernstein_poly (fun t => t) 1 x) (fun t => t) 0.
Proof.
  unfold is_polynomial_approx. intros x Hx0 Hx1.
  apply qabs_zero_le.
  assert (Heq: bernstein_poly (fun t : Q => t) 1 x == x).
  { apply bernstein_reproduces_id_1. }
  lra.
Qed.

(** The Bernstein polynomial B_1 exactly reproduces constants *)
Lemma bernstein_1_exact_on_const : forall c,
  is_polynomial_approx
    (fun x => bernstein_poly (fun _ => c) 1 x) (fun _ => c) 0.
Proof.
  unfold is_polynomial_approx. intros c x Hx0 Hx1.
  apply qabs_zero_le.
  assert (Heq: bernstein_poly (fun _ : Q => c) 1 x == c).
  { apply bernstein_reproduces_const_1. }
  lra.
Qed.

(* ================================================================= *)
(** ** Summary *)
(* ================================================================= *)

(** Stone-Weierstrass via Bernstein polynomials:

    1. Binomial coefficients (binom) - Pascal's triangle
    2. Rational power (qpower) - x^n over Q
    3. Bernstein basis B_{n,k}(x) = C(n,k) x^k (1-x)^{n-k}
    4. Concrete: B_{1,0}=1-x, B_{1,1}=x, B_{2,0}=(1-x)^2, etc.
    5. Partition of unity for n=1 and n=2
    6. Bernstein polynomial B_n(f,x)
    7. Linear interpolation: B_1(f,x) = f(0)(1-x) + f(1)x
    8. Reproduces constants: B_n(c,x) = c (for n=1,2)
    9. Reproduces identity: B_n(id,x) = x (for n=1,2)
   10. Error for x^2: B_2(x^2,x) = x^2 + x(1-x)/2
   11. Variance bound: x(1-x) <= 1/4 on [0,1]
   12. P4: polynomials = FINITE, functions = PROCESS

    24 Qed, 0 Admitted, 0 axioms.
*)
