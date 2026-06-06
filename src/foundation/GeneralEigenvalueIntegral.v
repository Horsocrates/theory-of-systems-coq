(** * GeneralEigenvalueIntegral.v — the eigenvalue-integrality CORE at GENERAL n (any dimension).
       CharPolyEigenvalue3 connected the criterion to an actual matrix at n=3.  The full general n needs the
       characteristic polynomial det(λI−A) of an arbitrary n×n integer matrix — a determinant library
       (Leibniz / cofactor), heavy machinery not built here.  But the LOGICAL CORE of the criterion is
       general-n and 0-axiom: the cleared characteristic value D = det(aI−bA) is MONIC-mod-b (D = aⁿ + b·K,
       since the lower part of any char poly is divisible by b), and D = 0 (a/b an eigenvalue) then forces
       aⁿ = −b·K ⟹ b | aⁿ ⟹ (Gauss) b = ±1 ⟹ b = 1 — at EVERY dimension n.

    -- What is general (here) vs what is the matrix input --
      GENERAL (proved, ∀n): `eigenvalue_integral_general` — D = aⁿ + b·K and D = 0 ⟹ b = 1.  And the cleared
      monic value mhom is ALWAYS of this form (`mhom_monic_mod_b`, via MonicRationalRoot.g_div_b): the
      lower homogenized sum is b-divisible at every degree.  So the rational-root criterion is general-n
      at the polynomial / cleared-characteristic level.
      MATRIX INPUT (proved n≤3, general n = determinant library): D = det(aI−bA) = mhom (char coeffs) — the
      characteristic determinant equals the cleared monic value (DiscriminantCompleteEigenvalue n=2,
      CharPolyEigenvalue3 n=3).  The general-n determinant identity is the only remaining mechanical piece.

    WHAT THE REPO HAS (surveyed): MonicRationalRoot (g_div_b, mhom, the general monic RRT); RationalRootTest
    (coprime_div_pow_unit / Gauss); CharPolyEigenvalue3 (the n=3 matrix bridge).  No determinant library.
    GAP: the general-n statement of the eigenvalue-integrality core, and the honest localization of the
    determinant as the sole matrix-theory input.  This adds it.

    ============ E/R/R разбор ============
      Elements : очищенное char-значение D=det(aI−bA); монично-mod-b: D=aⁿ+b·K.
      Roles    : собств. значение ⟺ D=0; рациональность ⟺ b.
      Rules    : aⁿ+b·K=0 ⟹ aⁿ=−b·K ⟹ b∣aⁿ ⟹ (Гаусс coprime_div_pow_unit) b=1 — на ЛЮБОЙ n.
      ДИАГНОСТИКА (P4): ядро eigenvalue-integrality ОБЩЕЕ по n (0-акс); mhom ВСЕГДА монично-mod-b (g_div_b);
      единственный матричный вход D=mhom доказан n≤3, общий n = det-библиотека. ЧЕСТНО локализую разрыв.
      Уровень: `синтез` (общий-n ядро + честная локализация det-входа).

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (builds on algebra.RationalRootTest + foundation.MonicRationalRoot)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory List.
From ToS Require Import algebra.RationalRootTest.
From ToS Require Import foundation.MonicRationalRoot.

Open Scope Z_scope.

(* ===================================================================== *)
(*  ★★ THE GENERAL-n EIGENVALUE-INTEGRALITY CORE                           *)
(* ===================================================================== *)

(** ★★ At EVERY dimension n: if the cleared characteristic value is monic-mod-b (D = aⁿ + b·K — which holds
    for det(aI−bA) of any integer matrix) and D = 0 (a/b is an eigenvalue, lowest terms, b > 0), then b = 1:
    the rational eigenvalue is an INTEGER.  Pure Gauss (coprime_div_pow_unit) — no determinant needed. *)
Theorem eigenvalue_integral_general : forall (n : nat) (a b K : Z),
  rel_prime a b -> b > 0 -> zpow a n + b * K = 0 -> b = 1.
Proof.
  intros n a b K Hrp Hbpos Heq.
  assert (Hdvd : (b | zpow a n)) by (exists (- K); nia).
  assert (Hrpba : rel_prime b a) by (apply rel_prime_sym; exact Hrp).
  destruct (coprime_div_pow_unit b a n Hrpba Hdvd) as [H1 | Hm1]; lia.
Qed.

(* ===================================================================== *)
(*  The cleared monic value mhom is ALWAYS monic-mod-b (every degree)       *)
(* ===================================================================== *)

(** ★ The cleared monic value mhom cs a b = aⁿ + b·K at every degree n = length cs (the lower homogenized
    sum is b-divisible, MonicRationalRoot.g_div_b).  So mhom always fits the general-n core. *)
Lemma mhom_monic_mod_b : forall (cs : list Z) (a b : Z),
  exists K, mhom cs a b = zpow a (length cs) + b * K.
Proof.
  intros cs a b. destruct (g_div_b cs a b) as [K HK].
  exists K. unfold mhom. rewrite HK. ring.
Qed.

(** ★ Hence the general monic RRT is an instance of the general-n core (mhom = 0 ⟹ b = 1, any degree). *)
Corollary monic_root_via_general : forall (cs : list Z) (a b : Z),
  rel_prime a b -> b > 0 -> mhom cs a b = 0 -> b = 1.
Proof.
  intros cs a b Hrp Hbpos Hroot.
  destruct (mhom_monic_mod_b cs a b) as [K HK].
  apply (eigenvalue_integral_general (length cs) a b K Hrp Hbpos).
  rewrite <- HK. exact Hroot.
Qed.

(* ===================================================================== *)
(*  Concrete: the core fires at any n — degree 4 and degree 7 examples     *)
(* ===================================================================== *)

(** Degree 4: aⁿ + b·K = 0 ⟹ b = 1 (n=4). *)
Example eig_n4 : forall a b K, rel_prime a b -> b > 0 -> zpow a 4 + b * K = 0 -> b = 1.
Proof. intros a b K. apply (eigenvalue_integral_general 4). Qed.

(** Degree 7: the core is genuinely dimension-uniform. *)
Example eig_n7 : forall a b K, rel_prime a b -> b > 0 -> zpow a 7 + b * K = 0 -> b = 1.
Proof. intros a b K. apply (eigenvalue_integral_general 7). Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The eigenvalue-integrality core, general-n:
      (core)       at EVERY n, a monic-mod-b cleared char value (aⁿ + b·K) that vanishes forces b = 1;
      (mhom)       the cleared monic value is always monic-mod-b (every degree, via g_div_b);
      (RRT)        hence the general monic RRT (mhom = 0 ⟹ b = 1) is an instance;
      (any n)      the core fires at n = 4, 7, … — dimension-uniform.
    So a rational eigenvalue of an integer matrix is an INTEGER at EVERY dimension — given the matrix input
    det(aI−bA) = mhom (the char-poly homogenization, proved for n ≤ 3; the general-n determinant is the only
    remaining mechanical piece, a determinant library not built here).  Honest: the LOGICAL core is general
    and 0-axiom; the determinant identity is localized as the matrix-theory input. *)
Theorem general_eigenvalue_integrality :
  (forall n a b K, rel_prime a b -> b > 0 -> zpow a n + b * K = 0 -> b = 1)
  /\ (forall cs a b, exists K, mhom cs a b = zpow a (length cs) + b * K)
  /\ (forall cs a b, rel_prime a b -> b > 0 -> mhom cs a b = 0 -> b = 1).
Proof.
  split. exact eigenvalue_integral_general.
  split. exact mhom_monic_mod_b.
  exact monic_root_via_general.
Qed.
