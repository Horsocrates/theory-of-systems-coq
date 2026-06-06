(** * HierarchyLaplacian.v — the SPECTRUM of the inter-level coupling Laplacian, classified by the
      Element / role-limit boundary (the far step of ПЛАН-Иерархии-и-Каскады.md §8.5, and the answer to
      §8.3: the rational-vs-surd classification of the inter-level coupling spectrum).

   When two systems at adjacent levels (or two siblings) interact, the coupling is a 2x2 matrix
   M = [[a,b],[c,d]] over Q; its spectrum (the COUPLING MODES) is the roots of the characteristic
   polynomial lam^2 - tr*lam + det, with tr = a+d, det = ad-bc, and discriminant disc = tr^2 - 4det =
   (a-d)^2 + 4bc.  The central fact:

     ★ a coupling mode is RATIONAL (Element)  <=>  the discriminant is a perfect square in Q.
       Surd discriminant => surd coupling modes (role-limit).

   This is exactly the criterion of foundation/ThreeFormulaBoundary.v (spectrum_element_iff_square_disc),
   now read on the INTER-LEVEL COUPLING: the spectrum of how systems influence neighbours across the
   hierarchy sits on the SAME Element/role-limit boundary as everything else in ToS.  Two exemplars:
     -- diagonal coupling [[2,0],[0,3]]: disc = 1 (a square) => rational modes {2,3} -- Element;
     -- golden coupling [[0,1],[1,1]]: disc = 5 (NOT a square, cf. GoldenFibonacci/Sqrt5Irrational) =>
        surd modes {phi, 1-phi} -- role-limit.

   HONEST SCOPE.  The spectral boundary criterion (rational mode <=> square discriminant) and the Element
   exemplar are fully machine-closed here, 0 axioms.  The role-limit exemplar shows disc = 5 and CITES
   the atlas (5 is not a perfect square in Q -- Sqrt5Irrational/GoldenFibonacci) for the surd conclusion;
   the irrationality is not re-proved here.  The role-limit (surd spectrum) is located, NOT crossed.
   Level: synthesis + observation -- ties the hierarchy direction to ThreeFormulaBoundary and the
   reduction atlas.  HIGHLIGHTS candidate (ПЛАН §8.3).

   Elements: the 2x2 coupling entries a,b,c,d in Q; the discriminant; rational mode / surd mode.
   Roles:    the eigenvalues = coupling modes; the discriminant = the dial; the two spectrum sides.
   Rules:    rational mode <=> disc is a perfect square (completing the square); disc = tr^2 - 4det.

   ============ E/R/R разбор ============
     Rules (L5): рацион. собств. значение <=> disc — полный квадрат (достройка квадрата); disc = tr^2-4det.
     Roles (L4): собств. значения = моды связи; дискриминант = ручка; две стороны спектра.
     Elements  : элементы связи a,b,c,d in Q; disc; рацион. мода / сурд мода.
   ДИАГНОСТИКА (P4): спектр межуровневой связи на ТОЙ ЖЕ границе Element/role-limit, что всё в ToS:
   рацион <=> disc-квадрат, сурд <=> не-квадрат. Голотая связь = phi/sqrt5 (мост к GoldenFibonacci).
   Отвечает §8.3, связывает с ThreeFormulaBoundary/атласом. ЧЕСТНО: iff+Element машинно; не-квадратность 5
   — цитата атласа. Локализуем, не пересекаем.

   STATUS: 6 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The 2x2 inter-level coupling matrix: trace, determinant, discriminant  *)
(* ===================================================================== *)

Definition cl_tr   (a b c d : Q) : Q := a + d.
Definition cl_det  (a b c d : Q) : Q := a*d - b*c.
Definition cl_disc (a b c d : Q) : Q := (a - d)*(a - d) + 4*b*c.   (* = tr^2 - 4 det *)

Lemma cl_disc_eq : forall a b c d,
  cl_disc a b c d == cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d.
Proof. intros. unfold cl_disc, cl_tr, cl_det. ring. Qed.

(** A coupling mode (eigenvalue): a root of the characteristic polynomial lam^2 - tr*lam + det. *)
Definition is_eigenvalue (a b c d lam : Q) : Prop :=
  lam*lam - cl_tr a b c d * lam + cl_det a b c d == 0.

(** A perfect square in Q. *)
Definition is_square_Q (x : Q) : Prop := exists s : Q, s * s == x.

(* ===================================================================== *)
(*  ★ The spectral boundary: rational mode <=> square discriminant         *)
(* ===================================================================== *)

Theorem spectrum_rational_iff_disc_square : forall a b c d,
  (exists lam, is_eigenvalue a b c d lam) <-> is_square_Q (cl_disc a b c d).
Proof.
  intros a b c d. split.
  - (* a rational mode forces a square discriminant: disc = (2*lam - tr)^2 *)
    intros [lam Hlam]. exists (2*lam - cl_tr a b c d).
    rewrite cl_disc_eq. unfold is_eigenvalue in Hlam.
    assert (Hkey : (2*lam - cl_tr a b c d) * (2*lam - cl_tr a b c d)
                   == (cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d)
                      + 4 * (lam*lam - cl_tr a b c d * lam + cl_det a b c d)) by ring.
    rewrite Hkey, Hlam. ring.
  - (* a square discriminant forces a rational mode: lam = (tr + s)/2 *)
    intros [s Hs]. exists ((cl_tr a b c d + s) / 2).
    rewrite cl_disc_eq in Hs. unfold is_eigenvalue.
    assert (Hkey : ((cl_tr a b c d + s) / 2) * ((cl_tr a b c d + s) / 2)
                   - cl_tr a b c d * ((cl_tr a b c d + s) / 2) + cl_det a b c d
                   == (s*s - (cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d)) * (1#4)) by field.
    rewrite Hkey, Hs. ring.
Qed.

(* ===================================================================== *)
(*  Two exemplars: Element (square disc) vs role-limit (surd disc)         *)
(* ===================================================================== *)

(** ★ Diagonal coupling [[2,0],[0,3]]: disc = 1 (a perfect square) => rational modes {2,3} = Element. *)
Example laplacian_diagonal_element : is_square_Q (cl_disc 2 0 0 3).
Proof. exists 1. vm_compute. reflexivity. Qed.

(** ★ Golden coupling [[0,1],[1,1]]: disc = 5.  Since 5 is NOT a perfect square in Q (GoldenFibonacci /
    Sqrt5Irrational), the coupling modes are surd {phi, 1-phi} = role-limit (cited, not re-proved). *)
Example laplacian_golden_disc : cl_disc 0 1 1 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(** The two sides of the coupling spectrum's finitization boundary. *)
Inductive SpectrumSide := RationalElement | SurdRoleLimit.
Lemma spectrum_h1_disjoint : RationalElement <> SurdRoleLimit.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the inter-level coupling spectrum on the Element/role-limit boundary *)
(* ===================================================================== *)

(** The inter-level coupling Laplacian spectrum:
      (disc)       disc = tr^2 - 4det;
      (★ boundary) a coupling mode is rational (Element) <=> the discriminant is a perfect square;
      (Element)    diagonal coupling [[2,0],[0,3]]: disc 1 (square) => rational modes {2,3};
      (role-limit) golden coupling [[0,1],[1,1]]: disc 5 (non-square per atlas) => surd modes {phi,1-phi};
      (H1)         the rational (Element) and surd (role-limit) spectrum sides are disjoint.
    The spectrum of how systems influence neighbours across the hierarchy sits on the SAME
    Element/role-limit boundary as the rest of ToS (the ThreeFormulaBoundary disc-square criterion).
    Rational coupling = Element; surd coupling = role-limit, located NOT crossed. *)
Theorem hierarchy_laplacian_spectrum :
  (forall a b c d, cl_disc a b c d == cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d)
  /\ (forall a b c d, (exists lam, is_eigenvalue a b c d lam) <-> is_square_Q (cl_disc a b c d))
  /\ is_square_Q (cl_disc 2 0 0 3)
  /\ (cl_disc 0 1 1 1 == 5)
  /\ (RationalElement <> SurdRoleLimit).
Proof.
  split; [exact cl_disc_eq |].
  split; [exact spectrum_rational_iff_disc_square |].
  split; [exact laplacian_diagonal_element |].
  split; [exact laplacian_golden_disc | exact spectrum_h1_disjoint].
Qed.
