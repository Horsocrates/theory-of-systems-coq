(** * CharPolyEigenvalue3.v — bringing the n×n eigenvalue criterion to an ACTUAL matrix (n=3).
       MonicRationalRoot proved "a rational root of a monic integer polynomial is an integer".  This connects
       it to a REAL matrix: for a general 3×3 integer matrix A, the characteristic polynomial det(λI−A) is
       the monic cubic λ³ − tr·λ² + m₂·λ − det(A); its homogenized form det(aI−bA) equals mhom of those
       coefficients (a ring identity), so a RATIONAL EIGENVALUE a/b (lowest terms) of A is an INTEGER (b=1).
       This is the n×n criterion realized on a matrix (the n=3 case), beyond the abstract polynomial.

    -- The bridge --
      char poly: det(λI−A) = λ³ − tr·λ² + m₂·λ − det(A), tr = Σaᵢᵢ, m₂ = Σ principal 2×2 minors.
      "a/b is an eigenvalue" ⟺ det((a/b)I−A)=0 ⟺ det(aI−bA)=0 (cleared, b≠0; det scales by b³).
      ★ det(aI−bA) = mhom [−det(A); m₂; −tr] a b   (a Z ring identity — the char-poly homogenization).
      So det(aI−bA)=0 ⟹ mhom=0 ⟹ (MonicRationalRoot) b=1: the rational eigenvalue is an integer.

    WHAT THE REPO HAS (surveyed): MonicRationalRoot.v (the general monic RRT, mhom); no matrix / determinant
    machinery.  GAP: connecting the RRT to an actual matrix's characteristic polynomial.  This does it for
    n=3 (a general symbolic 3×3); the general n needs an inductive determinant (a matrix library, not built).

    ============ E/R/R разбор ============
      Elements : 3×3 целая матрица (9 входов); char-полином = монический кубик; коэфф. tr, m₂, det.
      Roles    : собств. значение = корень char-полинома; рациональное a/b ⟺ det(aI−bA)=0 (очищенное).
      Rules    : det(aI−bA) = mhom(char-коэфф) (ring-тождество гомогенизации) ⟹ (MonicRationalRoot) b=1.
      ДИАГНОСТИКА (P4): рациональное собств. значение РЕАЛЬНОЙ 3×3 ⟹ ЦЕЛОЕ — критерий доведён до матриц (n=3).
      ЧЕСТНО: 3×3 общий символьный; общий n требует индуктивного det (матричная библиотека). Уровень: `синтез`.

    STATUS: 4 Qed, 0 Admitted, 0 axioms  (builds on foundation.MonicRationalRoot)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory List.
From ToS Require Import algebra.RationalRootTest.
From ToS Require Import foundation.MonicRationalRoot.
Import ListNotations.

Open Scope Z_scope.

Section Matrix3.

(** A general 3×3 integer matrix A = (aᵢⱼ). *)
Variables a11 a12 a13 a21 a22 a23 a31 a32 a33 : Z.

(** The characteristic-polynomial coefficients: trace, sum of principal 2×2 minors, determinant. *)
Definition tr3   : Z := a11 + a22 + a33.
Definition m2_3  : Z := (a11*a22 - a12*a21) + (a11*a33 - a13*a31) + (a22*a33 - a23*a32).
Definition det3A : Z := a11*(a22*a33 - a23*a32) - a12*(a21*a33 - a23*a31) + a13*(a21*a32 - a22*a31).

(** The lower coefficients of the monic char poly x³ − tr·x² + m₂·x − det = x³ + c₂x² + c₁x + c₀. *)
Definition charcoeffs : list Z := [ - det3A ; m2_3 ; - tr3 ].

(** The homogenized characteristic value det(aI − bA) of the 3×3 (expanded determinant). *)
Definition charhom (a b : Z) : Z :=
    (a - b*a11) * ((a - b*a22)*(a - b*a33) - (- b*a23)*(- b*a32))
  - (- b*a12)   * ((- b*a21)*(a - b*a33)   - (- b*a23)*(- b*a31))
  + (- b*a13)   * ((- b*a21)*(- b*a32)      - (a - b*a22)*(- b*a31)).

(* ===================================================================== *)
(*  ★ det(aI − bA) = mhom of the char-poly coefficients (the homogenization) *)
(* ===================================================================== *)

(** ★ The characteristic determinant det(aI−bA) IS the cleared monic value mhom [−det; m₂; −tr] a b —
    a pure ℤ ring identity (the homogenized Cayley characteristic polynomial of the 3×3). *)
Lemma charhom_eq_mhom : forall a b, charhom a b = mhom charcoeffs a b.
Proof.
  intros a b. unfold charhom, mhom, charcoeffs, det3A, m2_3, tr3.
  cbn [zpow length g]. ring.
Qed.

(* ===================================================================== *)
(*  ★★ A rational eigenvalue of the 3×3 is an integer                      *)
(* ===================================================================== *)

(** ★★ A rational eigenvalue a/b (lowest terms, b > 0) of the integer 3×3 matrix A — i.e. det(aI−bA) = 0,
    the cleared eigenvalue equation — is an INTEGER (b = 1).  The n×n criterion on an actual matrix (n=3). *)
Theorem rational_eigenvalue_3x3_is_integer : forall a b,
  rel_prime a b -> b > 0 -> charhom a b = 0 -> b = 1.
Proof.
  intros a b Hrp Hbpos Heig.
  apply (rational_root_monic_is_integer charcoeffs a b Hrp Hbpos).
  rewrite <- charhom_eq_mhom. exact Heig.
Qed.

End Matrix3.

(* ===================================================================== *)
(*  Concrete: a 3×3 with eigenvalue 2 (Element) and the upper-triangular det *)
(* ===================================================================== *)

(** diag(2,3,5): charhom at (a,b)=(2,1) is det(2I − diag) with a 0 factor — eigenvalue 2 (integer). *)
Example diag235_eig2 :
  charhom 2 0 0 0 3 0 0 0 5 2 1 = 0.
Proof. vm_compute. reflexivity. Qed.

(** And its rational eigenvalues are forced integer by the theorem (instantiated at diag(2,3,5)). *)
Example diag235_rational_eig_integer : forall a b,
  rel_prime a b -> b > 0 -> charhom 2 0 0 0 3 0 0 0 5 a b = 0 -> b = 1.
Proof. apply rational_eigenvalue_3x3_is_integer. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The n×n eigenvalue criterion on a real matrix (n=3):
      (identity)   det(aI−bA) = mhom [−det; m₂; −tr] a b — the char-poly homogenization (ring identity);
      (integer)    a rational eigenvalue a/b of an integer 3×3 is an integer (b=1) — via MonicRationalRoot;
      (concrete)   diag(2,3,5) has the integer eigenvalue 2.
    So the rational-root criterion is realized on an actual matrix: a rational eigenvalue of an integer 3×3
    is an INTEGER (dividing det), decidable.  Honest: n=3 (general symbolic entries); the general n needs an
    inductive determinant (a matrix library, not built); `charhom` is the cleared det(aI−bA), the homogenized
    characteristic polynomial. *)
Theorem charpoly_eigenvalue_3x3 :
  (forall a11 a12 a13 a21 a22 a23 a31 a32 a33 a b,
     charhom a11 a12 a13 a21 a22 a23 a31 a32 a33 a b
     = mhom (charcoeffs a11 a12 a13 a21 a22 a23 a31 a32 a33) a b)
  /\ (forall a11 a12 a13 a21 a22 a23 a31 a32 a33 a b,
        rel_prime a b -> b > 0 ->
        charhom a11 a12 a13 a21 a22 a23 a31 a32 a33 a b = 0 -> b = 1).
Proof.
  split.
  - intros. apply charhom_eq_mhom.
  - intros until b. apply rational_eigenvalue_3x3_is_integer.
Qed.
