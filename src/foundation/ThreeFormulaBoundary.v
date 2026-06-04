(** * ThreeFormulaBoundary.v — the R-formula (spectrum) sits on the FINITIZATION BOUNDARY.

    Companion to ThreeFormulaMethod.v.  There the method was reified (Rules->Roles->Elements,
    strict; scale free).  HERE we locate precisely WHERE the method can leave Q: in its
    R-formula, the SPECTRUM.  For a 2x2 rule M over Q the eigenvalues are (tr +- sqrt(disc))/2
    with disc = tr^2 - 4*det.  So:

      the spectrum is ELEMENT (rational, terminates in Q)  <->  disc M is a perfect square,
      the spectrum is ROLE-LIMIT (irrational sqrt(disc), a non-terminating process)  otherwise.

    This is EXACTLY the discriminant criterion of the reduction atlas (QuadraticDiscriminant.v /
    ReductionAtlasSynthesis.v: a rational eigenvalue forces a square discriminant) — the
    method's R-formula IS the finitization boundary, the bridge from Part A to Tom II's H1.

    TWO FACES of the boundary (the two atlas engines surface here):
      * real / hyperbolic (disc >= 0): Element iff disc a perfect square — the SURD engine
        (atlas I).  Examples: diag(2,3) -> Element (disc 1); Fibonacci -> role-limit sqrt 5
        (disc 5); Pell -> role-limit sqrt 2 (disc 32).
      * elliptic / oscillation (disc < 0): NO real eigenvalue (disc_neg_no_eigenvalue); finite
        order is governed by the TRACE in {-2..2} — the NIVEN engine (atlas IV), NOT the
        discriminant.  The SHO companion lives here.

    WHAT IS PROVED:
      complete_square                4*char_poly = (2x - tr)^2 - disc            (the bridge)
      eigenvalue_forces_square       rational eigenvalue  -> disc a perfect square (surd, fwd)
      square_disc_eigenvalue         disc = s^2  -> (tr+s)/2 is an eigenvalue     (back)
    * spectrum_element_iff_square_disc   (exists rational eigenvalue) <-> is_square (disc M)
      spectrum_role_limit_iff_nonsquare  the role-limit side (contrapositive)
      diag23_*                       a fully rational (Element) spectrum
      fib_eigenvalue_iff_square5     Fibonacci spectrum is Element <-> is_square 5  (= sqrt5 in Q)
      pell_eigenvalue_iff_square32   Pell spectrum is Element <-> is_square 32      (= sqrt2 in Q)
      disc_neg_no_eigenvalue         disc < 0 -> no rational eigenvalue (elliptic = role-limit)
      companion_*                    the SHO rule's disc = (2-k)^2 - 4 (trace face)
    The role-limit verdicts for Fibonacci (sqrt5) and Pell (sqrt2) are completed by the CITED
    surd facts 5, 32 not perfect squares (Sqrt5Irrational.v / GeneralSqrt.v, atlas page I) —
    not re-proved here; the boundary file supplies the criterion and the exact disc values.

    Elements: concrete spectra (diag, Fibonacci, Pell, SHO companion) on each side of the boundary
    Roles:    the "spectrum status" slot — Element vs role-limit — set by the discriminant verdict
    Rules:    a spectrum is Element iff disc is a perfect square (real face); the elliptic face is
              ruled by the trace (Niven) — the R-formula IS the finitization boundary

    ============ E/R/R разбор ============
      Rules (L5): спектр Element ⟺ disc полный квадрат (вещественная грань, сурд-движок); эллиптика
                  (disc<0) — нет веществ. собств. значения, конечный порядок по СЛЕДУ (Niven).
      Roles (L4): слот «статус спектра» назначается вердиктом дискриминанта/следа; R-формула на границе.
      Elements  : diag(2,3) Element; Фибоначчи √5, Пелля √2 role-limit; SHO-компаньон эллиптический.
    ДИАГНОСТИКА (P4): спектр — место, где метод покидает ℚ; role-limit = (tr±√disc)/2 как Коши-процесс,
    именуется не строится; ТЕ ЖЕ движки disc/след, что в атласе (мост Часть A → H1).

    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ThreeFormulaMethod.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The bridge: completing the square                                      *)
(* ===================================================================== *)

(** ★ 4 * char_poly M x = (2x - tr M)^2 - disc M.  The single identity behind the boundary. *)
Lemma complete_square (M : Mat2) (x : Q) :
  4 * char_poly M x == (2*x - tr M) * (2*x - tr M) - disc M.
Proof. unfold char_poly, disc; ring. Qed.

(* ===================================================================== *)
(*  Real face: Element  <->  disc a perfect square (the SURD engine)       *)
(* ===================================================================== *)

(** A rational eigenvalue forces the discriminant to be a perfect square (forward). *)
Lemma eigenvalue_forces_square (M : Mat2) (x : Q) :
  char_poly M x == 0 -> is_square (disc M).
Proof.
  intro H. exists (2*x - tr M).
  pose proof (complete_square M x) as Hc. rewrite H in Hc. lra.
Qed.

(** A square discriminant yields an explicit rational eigenvalue (tr + s)/2 (backward). *)
Lemma square_disc_eigenvalue (M : Mat2) (s : Q) :
  disc M == s * s -> char_poly M ((tr M + s) / 2) == 0.
Proof.
  intro Hs.
  pose proof (complete_square M ((tr M + s) / 2)) as Hc.
  assert (Hhalf : 2 * ((tr M + s) / 2) == tr M + s) by field.
  rewrite Hhalf in Hc.
  rewrite Hs in Hc.
  assert (Hrhs : (tr M + s - tr M) * (tr M + s - tr M) - s * s == 0) by ring.
  rewrite Hrhs in Hc.
  lra.
Qed.

(** ★ THE BOUNDARY: a system's spectrum is Element (has a rational eigenvalue) iff its
    discriminant is a perfect square. *)
Theorem spectrum_element_iff_square_disc (M : Mat2) :
  (exists x, char_poly M x == 0) <-> is_square (disc M).
Proof.
  split.
  - intros [x Hx]. exact (eigenvalue_forces_square M x Hx).
  - intros [s Hs]. exists ((tr M + s) / 2). exact (square_disc_eigenvalue M s Hs).
Qed.

(** The role-limit side: no rational eigenvalue iff disc is not a perfect square. *)
Corollary spectrum_role_limit_iff_nonsquare (M : Mat2) :
  ~ is_square (disc M) <-> ~ (exists x, char_poly M x == 0).
Proof.
  split; intros H Hc; apply H.
  - apply (proj1 (spectrum_element_iff_square_disc M)); exact Hc.
  - apply (proj2 (spectrum_element_iff_square_disc M)); exact Hc.
Qed.

(* ===================================================================== *)
(*  Element example: a fully rational spectrum                             *)
(* ===================================================================== *)

Definition diag23 : Mat2 := mk2 2 0 0 3.

Lemma diag23_disc : disc diag23 == 1.
Proof. unfold disc, tr, det, diag23; simpl; ring. Qed.

Lemma diag23_element : is_square (disc diag23).
Proof. exists 1. rewrite diag23_disc; ring. Qed.

Lemma diag23_eigenvalue_2 : char_poly diag23 2 == 0.
Proof. unfold char_poly, tr, det, diag23; simpl; ring. Qed.

(* ===================================================================== *)
(*  Boundary instances: the method's spectrum meets the atlas surds        *)
(* ===================================================================== *)

(** Fibonacci rule: spectrum is Element iff is_square 5.  Since sqrt 5 is irrational
    (Sqrt5Irrational.v / atlas I), the Fibonacci spectrum is role-limit (golden ratio). *)
Definition fib : Mat2 := mk2 1 1 1 0.

Lemma fib_disc : disc fib == 5.
Proof. unfold disc, tr, det, fib; simpl; ring. Qed.

Lemma fib_eigenvalue_iff_square5 :
  (exists x, char_poly fib x == 0) <-> is_square 5.
Proof.
  rewrite (spectrum_element_iff_square_disc fib).
  unfold is_square. split; intros [r Hr]; exists r.
  - rewrite <- fib_disc. exact Hr.
  - rewrite fib_disc. exact Hr.
Qed.

(** Pell rule: spectrum is Element iff is_square 32 (= 16*2).  Since sqrt 2 is irrational
    (atlas I), the Pell spectrum is role-limit. *)
Definition pell : Mat2 := mk2 3 4 2 3.

Lemma pell_disc : disc pell == 32.
Proof. unfold disc, tr, det, pell; simpl; ring. Qed.

Lemma pell_eigenvalue_iff_square32 :
  (exists x, char_poly pell x == 0) <-> is_square 32.
Proof.
  rewrite (spectrum_element_iff_square_disc pell).
  unfold is_square. split; intros [r Hr]; exists r.
  - rewrite <- pell_disc. exact Hr.
  - rewrite pell_disc. exact Hr.
Qed.

(* ===================================================================== *)
(*  Elliptic face: disc < 0 -> no real eigenvalue (the SHO oscillation)     *)
(* ===================================================================== *)

(** A negative discriminant gives NO rational eigenvalue: the spectrum is role-limit
    (oscillation).  Here finite order is ruled by the TRACE (Niven), not the discriminant. *)
Lemma disc_neg_no_eigenvalue (M : Mat2) :
  disc M < 0 -> ~ (exists x, char_poly M x == 0).
Proof.
  intros Hneg [x Hx].
  pose proof (complete_square M x) as Hc. rewrite Hx in Hc.
  assert (Hsq : 0 <= (2*x - tr M) * (2*x - tr M)).
  { destruct (Qlt_le_dec (2*x - tr M) 0) as [Hy|Hy].
    - assert (Hyy : (2*x - tr M) * (2*x - tr M)
                    == (-(2*x - tr M)) * (-(2*x - tr M))) by ring.
      rewrite Hyy. apply Qmult_le_0_compat; lra.
    - apply Qmult_le_0_compat; lra. }
  lra.
Qed.

(** The SHO evolution rule x(t+1) = (2-k)x(t) - x(t-1): companion disc = (2-k)^2 - 4. *)
Lemma companion_disc (k : Q) : disc (companion k) == (2 - k) * (2 - k) - 4.
Proof. unfold disc, tr, det, companion; simpl; ring. Qed.

(** k = 4: disc = 0, a repeated rational eigenvalue (parabolic, Element). *)
Lemma companion4_disc_zero : disc (companion 4) == 0.
Proof. rewrite companion_disc; ring. Qed.

Lemma companion4_element : is_square (disc (companion 4)).
Proof. exists 0. rewrite companion4_disc_zero; ring. Qed.

(** k = 1: disc = -3 < 0, elliptic — the order-6 oscillation, role-limit on the real side
    (its finite order is a TRACE/Niven fact, atlas IV). *)
Lemma companion1_disc_neg : disc (companion 1) == - (3).
Proof. rewrite companion_disc; ring. Qed.

Lemma companion1_role_limit : ~ (exists x, char_poly (companion 1) x == 0).
Proof. apply disc_neg_no_eigenvalue. rewrite companion1_disc_neg. lra. Qed.

(* ===================================================================== *)
(*  Capstone: the R-formula on the finitization boundary                   *)
(* ===================================================================== *)

(** The boundary:
      (criterion) the spectrum is Element iff disc is a perfect square (spectrum_element_iff...);
      (Element)   diag(2,3) has a rational spectrum (diag23_element);
      (real face) Fibonacci is Element iff is_square 5 — role-limit sqrt 5 (atlas I);
      (elliptic)  the SHO companion (k=1) has no real eigenvalue — oscillation (trace/Niven). *)
Theorem three_formula_boundary :
  (forall M, (exists x, char_poly M x == 0) <-> is_square (disc M))
  /\ is_square (disc diag23)
  /\ ((exists x, char_poly fib x == 0) <-> is_square 5)
  /\ ~ (exists x, char_poly (companion 1) x == 0).
Proof.
  split; [ exact spectrum_element_iff_square_disc | ].
  split; [ exact diag23_element | ].
  split; [ exact fib_eigenvalue_iff_square5 | exact companion1_role_limit ].
Qed.
