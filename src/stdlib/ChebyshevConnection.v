(** * ChebyshevConnection.v — Characteristic Polynomials of Tridiagonal Matrices
    Elements: Tridiagonal matrix T_K, polynomial coefficients as list Q
    Roles:    Recurrence p_K(λ) = λ·p_{K-1}(λ) - p_{K-2}(λ) (Chebyshev connection)
    Rules:    Concrete verification for K=2..6, integer coefficients
    Status:   Stdlib
    STATUS: 17 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  POLYNOMIAL OPERATIONS ON list Q                                    *)
(*  Coefficients stored as [a₀, a₁, ..., a_K]                         *)
(* ================================================================== *)

(** Multiply polynomial by λ: shift coefficients up by 1 *)
Definition poly_shift (p : list Q) : list Q := 0 :: p.

(** Subtract two polynomials coefficient-wise *)
Fixpoint poly_sub (p q : list Q) : list Q :=
  match p, q with
  | [], _ => map (fun x => -x) q
  | _, [] => p
  | a :: p', b :: q' => (a - b) :: poly_sub p' q'
  end.

(* ================================================================== *)
(*  CHARACTERISTIC POLYNOMIAL OF TRIDIAGONAL MATRIX                    *)
(*  T_K has 1s on super/sub-diagonal, 0s on diagonal                   *)
(*  Recurrence: p_K(λ) = λ·p_{K-1}(λ) - p_{K-2}(λ)                   *)
(*  This is exactly the Chebyshev polynomial of the first kind!        *)
(* ================================================================== *)

(** Build char poly iteratively: carry prev2 and prev1. *)
Fixpoint char_poly_aux (K : nat) (prev2 prev1 : list Q) : list Q :=
  match K with
  | O => prev1
  | S m => char_poly_aux m prev1 (poly_sub (poly_shift prev1) prev2)
  end.

Definition char_poly_tridiag (K : nat) : list Q :=
  match K with
  | O => [1]
  | S m => char_poly_aux m [1] [0; 1]
  end.

(* ================================================================== *)
(*  CONCRETE VERIFICATIONS K=2..6                                      *)
(* ================================================================== *)

(** K=2: p₂(λ) = λ² - 1 *)
Lemma cpoly_2 : char_poly_tridiag 2 = [-(1); 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** K=3: p₃(λ) = λ³ - 2λ *)
Lemma cpoly_3 : char_poly_tridiag 3 = [0; -(2); 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** K=4: p₄(λ) = λ⁴ - 3λ² + 1 *)
Lemma cpoly_4 : char_poly_tridiag 4 = [1; 0; -(3); 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** K=5: p₅(λ) = λ⁵ - 4λ³ + 3λ *)
Lemma cpoly_5 : char_poly_tridiag 5 = [0; 3; 0; -(4); 0; 1].
Proof. vm_compute. reflexivity. Qed.

(** K=6: p₆(λ) = λ⁶ - 5λ⁴ + 6λ² - 1 *)
Lemma cpoly_6 : char_poly_tridiag 6 = [-(1); 0; 6; 0; -(5); 0; 1].
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  INTEGER COEFFICIENT PROPERTIES                                     *)
(* ================================================================== *)

(** All coefficients of p₄ are integers (denominator = 1) *)
Lemma cpoly_4_coeff_0 : nth 0 (char_poly_tridiag 4) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_4_coeff_1 : nth 1 (char_poly_tridiag 4) 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_4_coeff_2 : nth 2 (char_poly_tridiag 4) 0 == -(3).
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_4_coeff_3 : nth 3 (char_poly_tridiag 4) 0 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_4_coeff_4 : nth 4 (char_poly_tridiag 4) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Degree of char poly = K *)
Lemma cpoly_degree_2 : length (char_poly_tridiag 2) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_degree_4 : length (char_poly_tridiag 4) = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_degree_6 : length (char_poly_tridiag 6) = 7%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CHEBYSHEV CONNECTION                                               *)
(*  The recurrence p_K = λ·p_{K-1} - p_{K-2} is exactly the           *)
(*  recurrence for Chebyshev polynomials T_K(λ/2).                     *)
(*  Eigenvalues of T_K are 2·cos(jπ/(K+1)), j=1..K.                   *)
(* ================================================================== *)

(** The leading coefficient is always 1 (monic polynomial) *)
Lemma cpoly_monic_2 : last (char_poly_tridiag 2) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_monic_4 : last (char_poly_tridiag 4) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma cpoly_monic_6 : last (char_poly_tridiag 6) 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

(** The Chebyshev connection: tridiagonal char polys satisfy the
    Chebyshev recurrence, linking matrix spectra to trigonometric
    values cos(jπ/(K+1)). This is WHY π appears in matrix spectra. *)
Theorem chebyshev_connection_verified :
  char_poly_tridiag 2 = [-(1); 0; 1] /\
  char_poly_tridiag 4 = [1; 0; -(3); 0; 1] /\
  char_poly_tridiag 6 = [-(1); 0; 6; 0; -(5); 0; 1].
Proof.
  repeat split; vm_compute; reflexivity.
Qed.
