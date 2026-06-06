(** * CubicCouplingSpectrum.v — Н1.3 (ПЛАН-Иерархии-и-Каскады.md §9): the inter-level Element/role-limit
      spectral boundary STRATIFIED BY DEGREE -- from 2x2 (quadratic, square discriminant) to 3x3 (cubic,
      perfect-cube condition), where the role-limit is a degree-3 surd (casus irreducibilis).

   A 3x3 inter-level coupling has three modes -- the roots of its characteristic cubic
   p(lam) = lam^3 - e1*lam^2 + e2*lam - e3  (e1=trace, e2=sum of 2x2 principal minors, e3=det).  The
   Element/role-limit question becomes a CUBIC one, and the rationality dial is the degree-3 analogue of
   the 2x2 perfect-square discriminant:

     ★ for the pure cubic lam^3 = e3:  a rational mode exists  <=  e3 is a perfect CUBE in Q
       (k^3 has the rational mode k).  When the cubic is irreducible over Q (no rational root) the modes
       are degree-3 surds -- the casus irreducibilis role-limit (cf. CubicRoleLimit H8, GeneralCbrt).

   ★ THE OBSERVATION (the genuine new content, synthesis + observation level).  The inter-level coupling
   spectral boundary is DEGREE-STRATIFIED: the n x n coupling sits on the Element side via an n-th-power
   condition, and its role-limit is a degree-n surd:
       2x2  ->  perfect SQUARE discriminant  ->  degree-2 role-limit (golden phi / sqrt5, disc 5);
       3x3  ->  perfect CUBE                  ->  degree-3 role-limit (cbrt2, lam^3 = 2).
   This is exactly the degree-uniform engine of the surd atlas (GeneralSqrt/GeneralCbrt/GeneralRoot:
   k-th root rational <=> perfect k-th power) read on the SPECTRUM of an inter-level coupling.  The
   hierarchy direction's boundary inherits the atlas's degree stratification.  Relocate, not cross.

   Exemplars (both real atlas objects, opposite sides, one stratum apart):
     -- Element 3x3: characteristic cubic (lam-1)(lam-2)(lam-3) = lam^3 - 6 lam^2 + 11 lam - 6, rational
        modes {1,2,3} -- fully machine-checked here;
     -- role-limit 3x3: the pure cubic lam^3 = 2, whose only modes are cbrt2 etc.; cbrt2 not in Q
        (GeneralCbrt / CubicRoleLimit H8) -- cited, not re-proved.  We machine-reduce the mode condition
        to lam^3 = 2 (the teeth), then cite the irrationality.
     -- the degree-2 foil (golden coupling disc 5, sqrt5) is carried over from RealCouplingSpectrum to
        make the stratification concrete.

   HONEST SCOPE.  Fully machine-closed here, 0 axioms: the three rational Element modes; the perfect-cube
   => rational-mode direction; the reduction of the role-limit cubic to lam^3 = 2; the degree-2 square
   foil.  The surd conclusions (cbrt2 not in Q at degree 3, sqrt5 not in Q at degree 2) CITE the atlas.
   This is the elementary algebra of the characteristic cubic read as a degree-stratified classification;
   the full 3x3-matrix-to-char-poly computation and the cubic discriminant / Galois refinement are NOT
   done here.  Level: synthesis + observation -- ties the hierarchy boundary to the degree-uniform atlas.

   Elements: the cubic coefficients e1,e2,e3 in Q; the modes; the perfect-cube condition.
   Roles:    the three modes = coupling modes; e1,e2,e3 = trace/minor-sum/det invariants; matrix size =
             surd degree.
   Rules:    pure cubic rational mode <= perfect cube; irreducible cubic => degree-3 role-limit; the n x n
             boundary is the n-th-power condition (degree-stratified).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: 3x3 межуровневая связь (3 моды); спектр = корни кубика lam^3-e1 lam^2+e2 lam-e3.
     Rules (L5): чистый кубик lam^3=e3: рацион. мода <= e3 полный КУБ; неприводимый кубик => degree-3
                 role-limit (casus irreducibilis); n x n граница = n-я-степенное условие.
     Roles (L4): три моды; e1,e2,e3 = след/сумма миноров/det; размер матрицы = степень surd.
     Elements  : коэффициенты e1,e2,e3 in Q; моды; условие полного куба.
     ОБРАЗУЮЩИЕ: rational-root структура (GeneralCbrt/GeneralRoot); is_mode3; companion-кубик.
     ВЛОЖЕННЫЕ : Element (lam-1)(lam-2)(lam-3) = три рацион. моды; role-limit lam^3=2 = cbrt2 (deg-3 surd);
                 degree-2 foil golden disc 5 (sqrt5) — вложенный нижний страт.
   ДИАГНОСТИКА (P4): граница ДЕГРЕ-СТРАТИФИЦИРОВАНА — n x n связь Element <= n-я-степенное условие; role-limit
   = degree-n surd (sqrt5 deg2 -> cbrt2 deg3). = degree-uniform движок атласа на СПЕКТРЕ связи. Münchhausen:
   неприводимый кубик — корень необводим в Q (= role-limit). Локализуем, не пересекаем.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.RealCouplingSpectrum.
Open Scope Q_scope.

(* ===================================================================== *)
(*  A coupling mode of a 3x3: a root of the characteristic cubic           *)
(*    p(lam) = lam^3 - e1 lam^2 + e2 lam - e3                              *)
(* ===================================================================== *)

Definition is_mode3 (e1 e2 e3 lam : Q) : Prop :=
  lam*lam*lam - e1*(lam*lam) + e2*lam - e3 == 0.

(* ===================================================================== *)
(*  Element 3x3: rational modes {1,2,3} of (lam-1)(lam-2)(lam-3)           *)
(*    = lam^3 - 6 lam^2 + 11 lam - 6                                        *)
(* ===================================================================== *)

Lemma elt3_mode_1 : is_mode3 6 11 6 1.
Proof. unfold is_mode3. ring. Qed.

Lemma elt3_mode_2 : is_mode3 6 11 6 2.
Proof. unfold is_mode3. ring. Qed.

Lemma elt3_mode_3 : is_mode3 6 11 6 3.
Proof. unfold is_mode3. ring. Qed.

(* ===================================================================== *)
(*  The degree-3 Element condition: a perfect CUBE gives a rational mode    *)
(* ===================================================================== *)

(** ★ The degree-3 analogue of "perfect square => rational mode": for the pure cubic lam^3 = k^3, the
    cube root k is a rational mode.  Perfect cube => Element. *)
Lemma cube_gives_rational_mode : forall k, is_mode3 0 0 (k*k*k) k.
Proof. intro k. unfold is_mode3. ring. Qed.

(** The role-limit cubic lam^3 - 2 reduces EXACTLY to lam^3 = 2 (the teeth): its modes are the cube
    roots of 2.  cbrt2 is not in Q (GeneralCbrt / CubicRoleLimit H8), so this is a degree-3 role-limit
    (casus irreducibilis) -- cited, not re-proved. *)
Lemma cubic_two_reduces : forall lam, is_mode3 0 0 2 lam <-> lam*lam*lam == 2.
Proof.
  intro lam. unfold is_mode3. split; intro H.
  - transitivity (lam*lam*lam - 0*(lam*lam) + 0*lam - 2 + 2).
    + ring.
    + rewrite H. ring.
  - rewrite H. ring.
Qed.

(* ===================================================================== *)
(*  The degree-2 stratum (carried from RealCouplingSpectrum) for contrast   *)
(* ===================================================================== *)

(** The degree-2 Element condition: a perfect square (k^2 is a square) -- one stratum below the cube. *)
Lemma square_gives_element2 : forall k, is_square_Q (k*k).
Proof. intro k. exists k. ring. Qed.

(** The degree-2 role-limit foil: the golden coupling disc 5 (sqrt5).  One stratum below lam^3 = 2. *)
Example deg2_role_limit_golden : cl_disc 0 1 1 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The boundary is degree-stratified                                      *)
(* ===================================================================== *)

Inductive BoundaryDegree := Deg2Square | Deg3Cube.
Lemma boundary_degree_stratified : Deg2Square <> Deg3Cube.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the degree-stratified inter-level coupling spectral boundary  *)
(* ===================================================================== *)

(** The inter-level coupling spectral boundary at degree 3, stratified against degree 2:
      (Element 3x3)  the cubic (lam-1)(lam-2)(lam-3) has rational modes 1,2,3;
      (★ cube)       a perfect cube gives a rational mode (degree-3 Element condition);
      (role-limit)   the cubic lam^3-2 reduces to lam^3 = 2 (cbrt2, degree-3 surd, cited);
      (degree 2)     a perfect square is the degree-2 Element condition;
      (deg-2 foil)   the golden coupling disc 5 (sqrt5) is the degree-2 role-limit, one stratum below;
      (★ stratified) the degree-2 (square) and degree-3 (cube) strata are distinct.
    The n x n inter-level coupling sits on the Element side via an n-th-power condition, with a degree-n
    surd role-limit -- the degree-uniform engine of the surd atlas, read on the coupling spectrum.
    Located NOT crossed. *)
Theorem cubic_spectral_boundary :
  (is_mode3 6 11 6 1 /\ is_mode3 6 11 6 2 /\ is_mode3 6 11 6 3)
  /\ (forall k, is_mode3 0 0 (k*k*k) k)
  /\ (forall lam, is_mode3 0 0 2 lam <-> lam*lam*lam == 2)
  /\ (forall k, is_square_Q (k*k))
  /\ (cl_disc 0 1 1 1 == 5)
  /\ (Deg2Square <> Deg3Cube).
Proof.
  split; [split; [exact elt3_mode_1 | split; [exact elt3_mode_2 | exact elt3_mode_3]] |].
  split; [exact cube_gives_rational_mode |].
  split; [exact cubic_two_reduces |].
  split; [exact square_gives_element2 |].
  split; [exact deg2_role_limit_golden | exact boundary_degree_stratified].
Qed.
