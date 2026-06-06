(** * RealCouplingSpectrum.v — НАПРАВЛЕНИЕ Н1 (ПЛАН-Иерархии-и-Каскады.md §9): the Element/role-limit
      spectral boundary (HierarchyLaplacian's disc-criterion) applied to a REAL ToS coupling matrix
      from the repo -- the Yang-Mills mass-gap transfer matrix -- NOT a toy.

   The repo's gauge layer (src/gauge/TransferMatrix.v, line 64) builds the 1+1D U(1), K=2 transfer
   matrix  T(beta) = [[1, 1-beta/8],[1-beta/8, 1]],  whose eigenvalues are the ground state
   lam0 = 2-beta/8 (eigenvector (1,1)) and the excited state lam1 = beta/8 (eigenvector (1,-1)); the
   MASS GAP is lam0 - lam1 = 2 - beta/4.  We classify THIS matrix on the inter-level Element/role-limit
   boundary:

     ★ disc(T(beta)) = (a-d)^2 + 4 b c = 0 + 4(1-beta/8)^2 = (2 - beta/4)^2  -- a PERFECT SQUARE for
       EVERY beta.  Hence the coupling spectrum of the Yang-Mills transfer matrix is RATIONAL (Element)
       identically in beta -- the two modes lam0, lam1 are exact rationals at every rational coupling.

   THE OBSERVATION (the genuine new content, synthesis + observation level).  The spectral boundary
   SEPARATES two walls that are easily conflated:
     -- the SPECTRAL wall (a surd eigenvalue) -- which the YM transfer matrix does NOT have: disc is a
        square for all beta, so no finite-beta transfer matrix produces an irrational gap;
     -- the CONTINUUM wall (the closure beta -> beta_c, lattice spacing -> 0) -- which is where the mass
        gap's role-limit actually lives.
   So the mass-gap wall is NOT in the algebra of any finite-coupling transfer matrix; it is the
   continuum/closure role-limit -- exactly the N->infinity boundary the cascade direction localizes.
   This LOCATES the wall, it does not cross it (relocate, not cross).

   Contrast (a real role-limit coupling): the golden coupling [[0,1],[1,1]] has disc = 5, NOT a perfect
   square in Q (GoldenFibonacci / Sqrt5Irrational), so ITS modes {phi, 1-phi} are surd -- role-limit IN
   the spectrum.  Two real repo couplings, opposite sides of one boundary.

   HONEST SCOPE.  Fully machine-closed here, 0 axioms: disc(T(beta)) is a perfect square for all beta;
   the two explicit rational modes; the gap value; the golden contrast's disc = 5.  The surd conclusion
   for the golden contrast CITES the atlas (5 not a square); the continuum-wall claim is recorded as a
   classification TAG (justified by "spectrum Element for all beta"), NOT a continuum-limit theorem.
   The disc-criterion is replicated from foundation/HierarchyLaplacian.v to keep this file single-file
   compilable (stale .vo is the norm on this machine).  Level: synthesis + observation -- ties the
   hierarchy direction to a real physics matrix and clarifies WHERE the mass-gap wall sits.

   Elements: the entries 1, 1-beta/8 in Q of the real transfer matrix; the discriminant; the two modes.
   Roles:    the eigenvectors (1,1)/(1,-1) = the two coupling modes; the gap = role-separation; beta =
             the coupling strength; the disc = the Element/role-limit dial.
   Rules:    rational mode <=> disc a perfect square; disc(T(beta)) = (2-beta/4)^2 (square, all beta) =>
             Element spectrum; the wall is the continuum closure, not the spectrum.

   ============ E/R/R разбор (осн. система + образующие + вложенные) ============
     ОСН. СИСТЕМА: оператор межуровневой связи реального под-ToS = transfer-матрица T(beta).
     Rules (L5): рацион. мода <=> disc — полный квадрат; disc(T(beta))=(2-beta/4)^2 — квадрат ВСЕГДА =>
                 спектр Element при любом beta; стена = континуум-замыкание (beta->beta_c), НЕ спектр.
     Roles (L4): собств. векторы (1,1)/(1,-1) = две моды связи; щель lam0-lam1 = разделение ролей;
                 beta = сила связи; disc = ручка Element/role-limit.
     Elements  : элементы 1, 1-beta/8 in Q настоящей transfer-матрицы; disc; две моды.
     ОБРАЗУЮЩИЕ: disc-критерий (HierarchyLaplacian); матрица transfer_2x2 (gauge/TransferMatrix.v);
                 достройка квадрата (ThreeFormulaBoundary/QuadraticDiscriminant).
     ВЛОЖЕННЫЕ : каждая мода (1,+-1) = вложенная 1-D связь (E=амплитуда, R=мода, R=собств.-масштаб);
                 щель = вложенная производная (Element); golden [[0,1],[1,1]] = вложенный контраст (role-limit).
   ДИАГНОСТИКА (P4): спектр настоящей gauge-матрицы Element при ЛЮБОМ рацион. beta (конечно, точно);
   role-limit НЕ в спектре, а в континуум-замыкании. РАЗДЕЛЯЕТ спектральную стену (сурд собств. знач. —
   которой НЕТ) от континуумной (beta->beta_c — где щель реально становится role-limit). Локализует стену
   щели масс: не в алгебре конечно-beta матрицы, а в N->infinity замыкании. Münchhausen: континуум-предел
   необводим в конечно-beta базе (= то самое замыкание). Relocate, not cross.

   STATUS: 10 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The disc-criterion (replicated from foundation/HierarchyLaplacian.v   *)
(*  to keep this file single-file compilable; stale .vo is the norm here) *)
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

(** rational coupling mode <=> square discriminant (the inter-level boundary criterion). *)
Theorem spectrum_rational_iff_disc_square : forall a b c d,
  (exists lam, is_eigenvalue a b c d lam) <-> is_square_Q (cl_disc a b c d).
Proof.
  intros a b c d. split.
  - intros [lam Hlam]. exists (2*lam - cl_tr a b c d).
    rewrite cl_disc_eq. unfold is_eigenvalue in Hlam.
    assert (Hkey : (2*lam - cl_tr a b c d) * (2*lam - cl_tr a b c d)
                   == (cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d)
                      + 4 * (lam*lam - cl_tr a b c d * lam + cl_det a b c d)) by ring.
    rewrite Hkey, Hlam. ring.
  - intros [s Hs]. exists ((cl_tr a b c d + s) / 2).
    rewrite cl_disc_eq in Hs. unfold is_eigenvalue.
    assert (Hkey : ((cl_tr a b c d + s) / 2) * ((cl_tr a b c d + s) / 2)
                   - cl_tr a b c d * ((cl_tr a b c d + s) / 2) + cl_det a b c d
                   == (s*s - (cl_tr a b c d * cl_tr a b c d - 4 * cl_det a b c d)) * (1#4)) by field.
    rewrite Hkey, Hs. ring.
Qed.

(* ===================================================================== *)
(*  The REAL repo matrix: the Yang-Mills mass-gap transfer matrix T(beta)  *)
(*  entries from src/gauge/TransferMatrix.v line 64:                       *)
(*    transfer_2x2 beta = qmat2x2 1 (1-beta*(1#8)) (1-beta*(1#8)) 1        *)
(* ===================================================================== *)

Definition tm_a (beta : Q) : Q := 1.
Definition tm_b (beta : Q) : Q := 1 - beta * (1#8).
Definition tm_c (beta : Q) : Q := 1 - beta * (1#8).
Definition tm_d (beta : Q) : Q := 1.

(** ★ disc(T(beta)) = (2 - beta/4)^2 -- a PERFECT SQUARE for every beta. *)
Theorem transfer_disc_is_square : forall beta,
  is_square_Q (cl_disc (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta)).
Proof.
  intro beta. exists (2 - beta * (1#4)).
  unfold cl_disc, tm_a, tm_b, tm_c, tm_d. ring.
Qed.

(** ★ Hence the coupling spectrum is RATIONAL (Element) for every beta -- via the disc-criterion. *)
Theorem transfer_spectrum_element : forall beta,
  exists lam, is_eigenvalue (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta) lam.
Proof.
  intro beta.
  apply (proj2 (spectrum_rational_iff_disc_square
                  (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta))).
  apply transfer_disc_is_square.
Qed.

(** The two explicit rational modes -- matching gauge/TransferMatrix.v's eigenvalues exactly:
    lam0 = 2 - beta/8 (ground, eigenvector (1,1)),  lam1 = beta/8 (excited, eigenvector (1,-1)). *)
Lemma transfer_mode_ground : forall beta,
  is_eigenvalue (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta) (2 - beta * (1#8)).
Proof.
  intro beta. unfold is_eigenvalue, cl_tr, cl_det, tm_a, tm_b, tm_c, tm_d. ring.
Qed.

Lemma transfer_mode_excited : forall beta,
  is_eigenvalue (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta) (beta * (1#8)).
Proof.
  intro beta. unfold is_eigenvalue, cl_tr, cl_det, tm_a, tm_b, tm_c, tm_d. ring.
Qed.

(** The mass gap lam0 - lam1 = 2 - beta/4 is itself rational (Element): the role-separation is exact. *)
Definition tm_mass_gap (beta : Q) : Q := (2 - beta * (1#8)) - beta * (1#8).
Lemma tm_mass_gap_value : forall beta, tm_mass_gap beta == 2 - beta * (1#4).
Proof. intro beta. unfold tm_mass_gap. ring. Qed.

(* ===================================================================== *)
(*  Contrast: a real role-limit coupling -- the golden [[0,1],[1,1]]       *)
(* ===================================================================== *)

(** disc([[0,1],[1,1]]) = 5, NOT a perfect square in Q (GoldenFibonacci / Sqrt5Irrational) =>
    surd modes {phi, 1-phi} = role-limit IN the spectrum (cited, not re-proved). *)
Example golden_coupling_disc : cl_disc 0 1 1 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The OBSERVATION: the mass-gap wall is the continuum closure, NOT spectral *)
(* ===================================================================== *)

(** Where a mass-gap wall could sit. *)
Inductive WallLocation := SpectralSurd | ContinuumClosure.

(** ★ Since disc(T(beta)) is a perfect square for ALL beta (transfer_disc_is_square), no finite-coupling
    transfer matrix yields a surd gap -- the spectrum is Element-side identically.  So the YM mass-gap
    wall is NOT spectral; it is the continuum closure beta->beta_c (the N->infinity role-limit).  This
    TAG records that classification (justified by transfer_disc_is_square); it is NOT a continuum-limit
    theorem.  Relocate, not cross. *)
Definition ym_wall_location : WallLocation := ContinuumClosure.
Lemma wall_not_spectral : ym_wall_location <> SpectralSurd.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: a real repo coupling matrix classified on the boundary       *)
(* ===================================================================== *)

(** The Yang-Mills mass-gap transfer matrix on the inter-level Element/role-limit boundary:
      (★ Element) disc(T(beta)) is a perfect square for every beta -- rational spectrum identically;
      (modes)     the two exact rational modes 2-beta/8 and beta/8;
      (gap)       the mass gap 2-beta/4 is itself rational (exact role-separation);
      (contrast)  the golden coupling [[0,1],[1,1]] has disc 5 (surd) -- role-limit in the spectrum;
      (wall)      the YM mass-gap wall is the continuum closure, NOT a spectral surd.
    A REAL repo physics matrix classified on the SAME Element/role-limit boundary as the rest of ToS,
    separating the (absent) spectral wall from the (actual) continuum-closure wall.  Element identically;
    the wall located NOT crossed. *)
Theorem real_coupling_spectrum :
  (forall beta, is_square_Q (cl_disc (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta)))
  /\ (forall beta, exists lam, is_eigenvalue (tm_a beta) (tm_b beta) (tm_c beta) (tm_d beta) lam)
  /\ (forall beta, tm_mass_gap beta == 2 - beta * (1#4))
  /\ (cl_disc 0 1 1 1 == 5)
  /\ (ym_wall_location <> SpectralSurd).
Proof.
  split; [exact transfer_disc_is_square |].
  split; [exact transfer_spectrum_element |].
  split; [exact tm_mass_gap_value |].
  split; [exact golden_coupling_disc | exact wall_not_spectral].
Qed.
