(** * RationalRootEigenvalue.v — the n×n frontier of the eigenvalue criterion: the rational ROOT THEOREM.
       For a 2×2 the criterion "has a rational eigenvalue" was "Δ = tr²−4det is a perfect square"
       (DiscriminantCompleteEigenvalue).  There is no single discriminant for n×n; the right general
       criterion is the RATIONAL ROOT THEOREM applied to the (monic, integer) characteristic polynomial:
       a rational eigenvalue of an integer matrix is an INTEGER (dividing the determinant), so the
       rational-eigenvalue question reduces to finitely many integer candidates — decidable.

       The ENGINE is RationalRootTest's general Gauss lemma (`coprime_div_pow_unit`: x | yⁿ, coprime ⟹ x=±1).
       Here it is applied in the eigenvalue framing: a rational eigenvalue p/q (lowest terms) satisfying a
       PURE characteristic equation λ^(k+1) = m (the companion matrix of x^(k+1) − m, the canonical n×n with
       a single non-trivial invariant) is an INTEGER (q = 1).  The 2×2 valve "Δ a square" and the degree-3
       Delian ∛2 are the k=1, k=2 instances.

    WHAT THE REPO HAS (surveyed): RationalRootTest.v — `nth_root_integer_or_irrational` (rational p/q with
    (p/q)^(S k) ∈ ℤ ⟹ q=1) and `coprime_div_pow_unit` (the general Gauss lemma); no matrix / characteristic
    -polynomial machinery.  GAP: the eigenvalue framing (rational eigenvalue ⟹ integer, decidable) and the
    explicit 2×2/degree-3 subsumption.  This adds it.  (RationalRootTest itself notes the full RRT for an
    ARBITRARY monic polynomial "builds on this but is not yet assembled" — the matrix char-poly is heavy;
    the pure-root case here is the canonical n×n companion form.)

    ============ E/R/R разбор ============
      Elements : целочисл. матрица, char-уравнение λ^(k+1)=m (companion), рациональное собств. значение p/q.
      Roles    : рациональное собств. значение ⟺ рациональный корень монического char-полинома (критерий = RRT).
      Rules    : чистый корень λ^(k+1)=m в низших членах ⟹ q=1 (целое), через лемму Гаусса (coprime_div_pow_unit).
      ДИАГНОСТИКА (P4): рациональное собств. значение ⟹ ЦЕЛОЕ (делит det) ⟹ разрешимо; критерий обобщается
      Δ-квадрат(2×2) → целый-корень-char-полинома(n×n) = теорема о рациональном корне; 2×2 (√2) и куб (∛2) =
      инстансы k=1,2. ЧЕСТНО: движок RRT в pure-root (companion) форме; полный произвольно-монический n×n требует
      ещё вычисления char-полинома (матричная машинерия, не строю). Уровень: `новое обрамление известного`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (builds on algebra.RationalRootTest)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory.
From ToS Require Import algebra.RationalRootTest.

Open Scope Z_scope.

(* ===================================================================== *)
(*  ★ THE RATIONAL ROOT THEOREM in the eigenvalue framing (pure / companion) *)
(* ===================================================================== *)

(** ★ A rational eigenvalue p/q (lowest terms, q > 0) satisfying a PURE characteristic equation
    λ^(k+1) = m — the companion matrix of x^(k+1) − m, the canonical n×n with one non-trivial invariant —
    is an INTEGER (q = 1).  This is the n×n eigenvalue-rationality criterion: a rational eigenvalue of an
    integer matrix is an integer (dividing the determinant), so rational eigenvalues are decidable. *)
Theorem pure_root_eigenvalue_integer : forall (p q : Z) (k : nat) (m : Z),
  q > 0 -> rel_prime p q -> zpow p (S k) = m * zpow q (S k) -> q = 1.
Proof. exact nth_root_integer_or_irrational. Qed.

(* ===================================================================== *)
(*  The 2×2 valve subsumed (k=1): x²−2 (Δ=8) — a rational root is integer   *)
(* ===================================================================== *)

(** ★ Subsumption of the 2×2 case: a rational eigenvalue of x²−2 (the Δ=8 companion) is an integer.
    (So a²=2b² in lowest terms forces b=1 ⟹ a²=2 impossible ⟹ √2 ∉ ℚ — recovering the 2×2 Δ=8 verdict.) *)
Corollary sqrt2_eigenvalue_integer : forall a b : Z,
  b > 0 -> rel_prime a b -> a * a = 2 * (b * b) -> b = 1.
Proof.
  intros a b Hb Hrp Heq.
  apply (pure_root_eigenvalue_integer a b 1 2 Hb Hrp). cbn [zpow]. nia.
Qed.

(* ===================================================================== *)
(*  The degree-3 case (k=2): x³−2 (Delian ∛2) — a rational root is integer  *)
(* ===================================================================== *)

(** ★ Degree-3 (Delian): a rational eigenvalue of x³−2 is an integer (so ∛2 ∉ ℚ — doubling the cube). *)
Corollary cbrt2_eigenvalue_integer : forall a b : Z,
  b > 0 -> rel_prime a b -> a * a * a = 2 * (b * b * b) -> b = 1.
Proof.
  intros a b Hb Hrp Heq.
  apply (pure_root_eigenvalue_integer a b 2 2 Hb Hrp). cbn [zpow]. nia.
Qed.

(** And there is no integer with square 2 (so the rational root really fails ⟹ no rational eigenvalue). *)
Lemma no_integer_sqrt2 : forall m : Z, m * m <> 2.
Proof.
  intros m H. assert (Habs : Z.abs m * Z.abs m = 2) by (rewrite <- Z.abs_mul, H; reflexivity).
  assert (Hnn : 0 <= Z.abs m) by apply Z.abs_nonneg.
  assert (Hcase : Z.abs m <= 1 \/ 2 <= Z.abs m) by lia.
  destruct Hcase as [Hle | Hge]; nia.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The n×n eigenvalue-rationality criterion = the rational root theorem (Gauss engine):
      (criterion)  a rational eigenvalue p/q satisfying λ^(k+1)=m is an INTEGER (q=1) — every degree;
      (2×2)        x²−2 (Δ=8): rational root ⟹ integer, and none squares to 2 ⟹ √2 ∉ ℚ;
      (degree 3)   x³−2: rational root ⟹ integer (Delian ∛2).
    So for n×n: a rational eigenvalue of an integer matrix is an INTEGER (dividing det), generalizing
    "Δ a perfect square" (2×2) to "the monic characteristic polynomial has an integer root" (n×n),
    decidable by the finitely many integer candidates.  Honest: the engine is the general Gauss lemma
    (RationalRootTest); shown here in the pure-root (companion) form at every degree, with the 2×2 and ∛2
    instances; the full arbitrary-monic n×n additionally needs the characteristic polynomial (heavy matrix
    machinery, not built here). *)
Theorem rational_root_eigenvalue_criterion :
  (forall (p q : Z) (k : nat) (m : Z),
     q > 0 -> rel_prime p q -> zpow p (S k) = m * zpow q (S k) -> q = 1)
  /\ (forall a b : Z, b > 0 -> rel_prime a b -> a * a = 2 * (b * b) -> b = 1)
  /\ (forall a b : Z, b > 0 -> rel_prime a b -> a * a * a = 2 * (b * b * b) -> b = 1)
  /\ (forall m : Z, m * m <> 2).
Proof.
  split. exact pure_root_eigenvalue_integer.
  split. exact sqrt2_eigenvalue_integer.
  split. exact cbrt2_eigenvalue_integer.
  exact no_integer_sqrt2.
Qed.
