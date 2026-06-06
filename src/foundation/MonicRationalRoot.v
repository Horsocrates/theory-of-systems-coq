(** * MonicRationalRoot.v — the GENERAL rational root theorem (fresh formulation): a rational root of an
       ARBITRARY monic integer polynomial is an integer.  This is the n×n eigenvalue-rationality criterion
       in full: a rational eigenvalue of an integer matrix is an INTEGER (the char poly is monic integer).
       It supersedes the pure-root (companion) form of RationalRootEigenvalue.v with the arbitrary-monic case.

       FRESH FORMULATION (avoiding the List.last / length−1 / ring-on-abstract-list pitfalls of the first
       attempt): represent the monic polynomial p(x) = xⁿ + Σ_{i<n} c_i x^i by its LOWER coefficients
       cs = [c_0; …; c_{n−1}] (the leading xⁿ is implicit), n = length cs.  The cleared-denominator value
       is mhom cs a b = bⁿ·p(a/b) = aⁿ + g cs a b, where g cs a b = Σ_{i<n} c_i a^i b^{n−i} is the lower
       homogenized sum.  KEY: b | g (every lower term carries b^{≥1}), so a root mhom = 0 gives
       aⁿ = −g ⟹ b | aⁿ ⟹ (RationalRootTest.coprime_div_pow_unit / Gauss) b = ±1 ⟹ b = 1.  The whole proof
       is divisibility (Z.divide), no ring on abstract lists, no List.last, no length−1.

    WHAT THE REPO HAS (surveyed): RationalRootTest.v — `coprime_div_pow_unit` (Gauss: x | yⁿ, coprime ⟹
    x=±1) and `nth_root_integer_or_irrational` (the PURE-root case).  GAP: the rational root theorem for an
    ARBITRARY monic integer polynomial (RationalRootTest's own note: "the full RRT … is not yet assembled").
    This assembles it.

    ============ E/R/R разбор ============
      Elements : монический полином = младшие коэфф. cs (ведущий xⁿ неявно), n=length cs; mhom=aⁿ+g (очищенное bⁿp(a/b)).
      Roles    : рациональный корень a/b ⟺ mhom=0; критерий = делимость на b.
      Rules    : g (младшая сумма) делится на b (каждый член b^{≥1}) ⟹ aⁿ=−g делится на b ⟹ (Гаусс) b=±1 ⟹ b=1.
      ДИАГНОСТИКА (P4): рациональный корень ПРОИЗВОЛЬНОГО монического ⟹ ЦЕЛЫЙ (без pure-root ограничения) =
      общий n×n критерий рациональности собств. значения. ЧЕСТНО: mhom = очищенное уравнение корня; полное
      матричное n×n ещё требует вычисления char-полинома (не строю). Уровень: `синтез`.

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (builds on algebra.RationalRootTest)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory List.
From ToS Require Import algebra.RationalRootTest.
Import ListNotations.

Open Scope Z_scope.

(** zpow successor (controlled reduction). *)
Lemma zpow_S : forall (y : Z) (k : nat), zpow y (S k) = y * zpow y k.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The lower homogenized sum g, and the cleared monic value mhom           *)
(* ===================================================================== *)

(** cs = [c_0; …; c_{n−1}] are the LOWER coefficients of monic p(x) = xⁿ + Σ_{i<n} c_i x^i.
    g cs a b = Σ_{i<n} c_i a^i b^{n−i} — the lower part of bⁿ·p(a/b). *)
Fixpoint g (cs : list Z) (a b : Z) : Z :=
  match cs with
  | [] => 0
  | c :: cs' => c * zpow b (S (length cs')) + a * g cs' a b
  end.

Lemma g_cons : forall (c : Z) (cs' : list Z) (a b : Z),
  g (c :: cs') a b = c * zpow b (S (length cs')) + a * g cs' a b.
Proof. reflexivity. Qed.

(** ★ The lower sum is divisible by b: every term Σ c_i a^i b^{n−i} carries a factor b^{n−i} with n−i ≥ 1. *)
Lemma g_div_b : forall (cs : list Z) (a b : Z), (b | g cs a b).
Proof.
  intros cs; induction cs as [| c cs' IH]; intros a b.
  - apply Z.divide_0_r.
  - rewrite g_cons. apply Z.divide_add_r.
    + exists (c * zpow b (length cs')). rewrite zpow_S. ring.
    + apply Z.divide_mul_r. apply IH.
Qed.

(** The cleared-denominator value of the monic polynomial at a/b: mhom = bⁿ·p(a/b) = aⁿ + g. *)
Definition mhom (cs : list Z) (a b : Z) : Z := zpow a (length cs) + g cs a b.

(* ===================================================================== *)
(*  ★★ THE GENERAL RATIONAL ROOT THEOREM (arbitrary monic)                 *)
(* ===================================================================== *)

(** ★★ A rational root a/b (lowest terms, b > 0) of an ARBITRARY monic integer polynomial is an INTEGER
    (b = 1): from mhom = 0 we get aⁿ = −g, and b | g, so b | aⁿ ⟹ (Gauss) b = ±1 ⟹ b = 1. *)
Theorem rational_root_monic_is_integer : forall (cs : list Z) (a b : Z),
  rel_prime a b -> b > 0 -> mhom cs a b = 0 -> b = 1.
Proof.
  intros cs a b Hrp Hbpos Hroot.
  assert (Hg : (b | g cs a b)) by apply g_div_b.
  assert (Hdvd : (b | zpow a (length cs))).
  { unfold mhom in Hroot.
    assert (Heq : zpow a (length cs) = - g cs a b) by lia.
    rewrite Heq. apply Z.divide_opp_r. exact Hg. }
  assert (Hrpba : rel_prime b a) by (apply rel_prime_sym; exact Hrp).
  destruct (coprime_div_pow_unit b a (length cs) Hrpba Hdvd) as [H1 | Hm1]; lia.
Qed.

(* ===================================================================== *)
(*  Subsumption: 2×2 (x²−2, Δ=8) and degree-3 (x³−2, Delian ∛2)            *)
(* ===================================================================== *)

(** The cleared x²−2 is a²−2b² (lower coeffs [−2; 0]). *)
Lemma mhom_x2_minus_2 : forall a b, mhom [-2; 0] a b = a * a - 2 * (b * b).
Proof. intros a b. unfold mhom. cbn [zpow length g]. ring. Qed.

(** ★ A rational root of x²−2 is an integer (recovering the 2×2 Δ=8 valve from the general theorem). *)
Corollary sqrt2_root_is_integer : forall a b,
  rel_prime a b -> b > 0 -> a * a - 2 * (b * b) = 0 -> b = 1.
Proof.
  intros a b Hrp Hbpos Heq.
  apply (rational_root_monic_is_integer [-2; 0] a b Hrp Hbpos).
  rewrite mhom_x2_minus_2. exact Heq.
Qed.

(** The cleared x³−2 is a³−2b³ (lower coeffs [−2; 0; 0]). *)
Lemma mhom_x3_minus_2 : forall a b, mhom [-2; 0; 0] a b = a * a * a - 2 * (b * b * b).
Proof. intros a b. unfold mhom. cbn [zpow length g]. ring. Qed.

(** ★ A rational root of x³−2 is an integer (the Delian ∛2, degree 3). *)
Corollary cbrt2_root_is_integer : forall a b,
  rel_prime a b -> b > 0 -> a * a * a - 2 * (b * b * b) = 0 -> b = 1.
Proof.
  intros a b Hrp Hbpos Heq.
  apply (rational_root_monic_is_integer [-2; 0; 0] a b Hrp Hbpos).
  rewrite mhom_x3_minus_2. exact Heq.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The general rational root theorem = the n×n eigenvalue-rationality criterion:
      (lower sum)  b | g (the lower homogenized sum is divisible by b);
      (RRT)        a rational root of an ARBITRARY monic integer polynomial is an integer (b = 1);
      (2×2)        x²−2 (Δ=8) subsumed; (degree 3) x³−2 (Delian ∛2) subsumed.
    So for n×n: a rational eigenvalue of an integer matrix is an INTEGER (dividing det), generalizing
    "Δ a perfect square" (2×2) to "the monic characteristic polynomial has an integer root" (n×n, ANY
    monic — not just pure roots), decidable by the finitely many integer candidates.  Honest: mhom is the
    cleared-denominator monic equation (= bⁿ·p(a/b)); the full matrix decision additionally needs the
    characteristic polynomial itself (heavy matrix machinery, not built here). *)
Theorem monic_rational_root_criterion :
  (forall cs a b, (b | g cs a b))
  /\ (forall cs a b, rel_prime a b -> b > 0 -> mhom cs a b = 0 -> b = 1)
  /\ (forall a b, rel_prime a b -> b > 0 -> a * a - 2 * (b * b) = 0 -> b = 1)
  /\ (forall a b, rel_prime a b -> b > 0 -> a * a * a - 2 * (b * b * b) = 0 -> b = 1).
Proof.
  split. exact g_div_b.
  split. exact rational_root_monic_is_integer.
  split. exact sqrt2_root_is_integer.
  exact cbrt2_root_is_integer.
Qed.
