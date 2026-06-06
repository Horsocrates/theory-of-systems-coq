(** * CouplingElementForcing.v — Н1 deepening (ПЛАН-Иерархии-и-Каскады.md §9): from ONE Element example
      to the STRUCTURAL CRITERION -- which inter-level couplings are FORCED onto the Element side, and
      what opens the role-limit (surd) wall.

   RealCouplingSpectrum.v showed the YM transfer matrix T(beta)=[[1,1-beta/8],[1-beta/8,1]] is Element
   (rational spectrum) for every beta.  WHY?  Not luck -- structure:

     ★ EQUAL DIAGONAL collapses the discriminant: disc([[a,b],[c,a]]) = (a-a)^2 + 4bc = 4bc.
     ★ SYMMETRIC + EQUAL DIAGONAL is Element ALWAYS: disc([[a,b],[b,a]]) = 4b^2 = (2b)^2 -- a perfect
       square for every a,b.  The YM transfer matrix is exactly this shape (a=1, b=1-beta/8), so its
       Element spectrum is FORCED by the lattice translation symmetry (equal on-site action a=d), not a
       numerical accident.

   ★ THE LEVER (what opens the role-limit wall).  With the SAME off-diagonal coupling b=c=1:
     -- equal diagonal a=d=0:    disc([[0,1],[1,0]]) = 4 = 2^2  -> Element;
     -- broken diagonal a=0,d=1:  disc([[0,1],[1,1]]) = 5       -> role-limit (golden, surd).
   The surd wall in the spectrum is opened by the SELF-ENERGY ASYMMETRY (the diagonal gap a-d), NOT by
   the coupling strength.  Indeed disc([[a,b],[c,d]]) - disc([[a,b],[c,a]]) = (a-d)^2: the entire excess
   over the equal-diagonal value 4bc is exactly the diagonal-gap square.

   THE OBSERVATION (synthesis + observation level).  ToS's lattice/transfer couplings are Element BY
   STRUCTURE: translation symmetry => equal diagonal => (with symmetric coupling) square discriminant.
   The role-limit needs broken self-energy symmetry.  So "why is ToS physics mostly rational-spectrum"
   has a structural answer: the symmetry that defines the lattice is the same symmetry that forces the
   Element side.  HONEST: this is the elementary algebra of the 2x2 discriminant read as a
   classification; the surd conclusion for the golden case cites the atlas (5 not a square in Q,
   GoldenFibonacci/Sqrt5Irrational).  A full survey of mixing/CP matrices (ProcessPMGMarkov,
   ProcessCPViolation) is a further step.  Relocate, not cross.

   Elements: the 2x2 entries a,b,c,d in Q; the diagonal gap a-d; the off-diagonal product bc.
   Roles:    equal diagonal = on-site symmetry; symmetric = reciprocal coupling; the gap = the lever.
   Rules:    equal diagonal => disc=4bc; symmetric+equal diagonal => disc=(2b)^2 (Element always);
             excess disc = (a-d)^2 => the self-energy asymmetry is what opens the role-limit wall.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: класс межуровневых связей, параметризованный диагональной симметрией.
     Rules (L5): равная диагональ => disc=4bc; симметрия+равная диагональ => disc=(2b)^2 (Element всегда);
                 избыток disc = (a-d)^2 => асимметрия само-энергий открывает role-limit.
     Roles (L4): равная диагональ = on-site симметрия (трансляц.); симметрия = взаимная связь; gap=рычаг.
     Elements  : элементы a,b,c,d in Q; диагональный зазор a-d; произведение bc.
     ОБРАЗУЮЩИЕ: disc-критерий; YM-инстанс (RealCouplingSpectrum); достройка квадрата.
     ВЛОЖЕННЫЕ : YM-семейство [[a,b],[b,a]] (Element); golden [[0,1],[1,1]] (broken diag, role-limit);
                 равно-диаг. golden [[0,1],[1,0]] (disc 4, Element) — вложенный контроль рычага.
   ДИАГНОСТИКА (P4): рацион. спектр ToS-решётки = СЛЕДСТВИЕ трансляц. симметрии (равная диагональ), не
   совпадение; role-limit требует слома само-энерг. симметрии. Münchhausen: тот же симметрийный выбор,
   что определяет решётку, форсирует Element-сторону. Relocate, not cross.

   STATUS: 8 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.RealCouplingSpectrum.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Equal diagonal collapses the discriminant to the off-diagonal product *)
(* ===================================================================== *)

(** ★ Equal self-energies (a = d) collapse disc to 4bc: the diagonal gap is gone. *)
Lemma equal_diag_disc : forall a b c, cl_disc a b c a == 4 * b * c.
Proof. intros a b c. unfold cl_disc. ring. Qed.

(* ===================================================================== *)
(*  Symmetric + equal diagonal => Element ALWAYS (the YM family)           *)
(* ===================================================================== *)

(** ★ A symmetric coupling with equal self-energies [[a,b],[b,a]] has disc = (2b)^2 -- a perfect square
    for EVERY a,b.  So this entire family is on the Element side unconditionally. *)
Lemma symmetric_equal_diag_square : forall a b, is_square_Q (cl_disc a b b a).
Proof. intros a b. exists (2 * b). unfold cl_disc. ring. Qed.

(** Hence the symmetric-equal-diagonal family has a rational coupling mode (Element spectrum). *)
Lemma symmetric_equal_diag_element : forall a b,
  exists lam, is_eigenvalue a b b a lam.
Proof.
  intros a b. apply (proj2 (spectrum_rational_iff_disc_square a b b a)).
  apply symmetric_equal_diag_square.
Qed.

(** ★ The YM transfer matrix is exactly this shape (a=1, b=1-beta/8): its Element spectrum is FORCED by
    the lattice translation symmetry (equal on-site action), not a numerical accident. *)
Lemma ym_is_symmetric_equal_diag : forall beta,
  is_square_Q (cl_disc 1 (1 - beta * (1#8)) (1 - beta * (1#8)) 1).
Proof. intro beta. apply symmetric_equal_diag_square. Qed.

(* ===================================================================== *)
(*  The lever: the self-energy asymmetry (a-d) is what opens role-limit    *)
(* ===================================================================== *)

(** ★ The excess of the full discriminant over its equal-diagonal value is exactly the diagonal-gap
    square: disc([[a,b],[c,d]]) - disc([[a,b],[c,a]]) = (a-d)^2.  The off-diagonal coupling contributes
    the SAME 4bc either way; only the self-energy gap can add structure. *)
Lemma disc_excess_is_gap_square : forall a b c d,
  cl_disc a b c d - cl_disc a b c a == (a - d) * (a - d).
Proof. intros a b c d. unfold cl_disc. ring. Qed.

(** ★ The lever in action -- SAME off-diagonal b=c=1, only the diagonal changes:
    equal diagonal [[0,1],[1,0]] => disc 4 (a perfect square) => Element. *)
Example lever_equal_diag_element : cl_disc 0 1 1 0 == 4.
Proof. vm_compute. reflexivity. Qed.

(** broken diagonal [[0,1],[1,1]] => disc 5 (non-square in Q, golden) => role-limit.  The surd wall was
    opened by the self-energy asymmetry, not by the coupling. *)
Example lever_broken_diag_role_limit : cl_disc 0 1 1 1 == 5.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the structural forcing criterion                             *)
(* ===================================================================== *)

(** Which inter-level couplings are FORCED Element, and what opens the role-limit wall:
      (collapse)  equal self-energies (a=d) collapse disc to 4bc;
      (★ forcing) symmetric + equal diagonal [[a,b],[b,a]] has disc (2b)^2 -- Element ALWAYS;
      (modes)     hence a rational coupling mode exists for the whole family;
      (YM)        the YM transfer matrix is of this shape -- Element FORCED by lattice symmetry;
      (★ lever)   the excess disc over the equal-diagonal value is exactly the gap square (a-d)^2;
      (Element)   same coupling, equal diagonal [[0,1],[1,0]] => disc 4 (Element);
      (role-limit) same coupling, broken diagonal [[0,1],[1,1]] => disc 5 (role-limit).
    ToS's lattice/transfer spectra are Element BY STRUCTURE (translation symmetry => equal diagonal =>
    square discriminant); the role-limit needs broken self-energy symmetry.  The symmetry that defines
    the lattice is the same one that forces the Element side.  Located NOT crossed. *)
Theorem coupling_element_forcing :
  (forall a b c, cl_disc a b c a == 4 * b * c)
  /\ (forall a b, is_square_Q (cl_disc a b b a))
  /\ (forall a b, exists lam, is_eigenvalue a b b a lam)
  /\ (forall beta, is_square_Q (cl_disc 1 (1 - beta * (1#8)) (1 - beta * (1#8)) 1))
  /\ (forall a b c d, cl_disc a b c d - cl_disc a b c a == (a - d) * (a - d))
  /\ (cl_disc 0 1 1 0 == 4)
  /\ (cl_disc 0 1 1 1 == 5).
Proof.
  split; [exact equal_diag_disc |].
  split; [exact symmetric_equal_diag_square |].
  split; [exact symmetric_equal_diag_element |].
  split; [exact ym_is_symmetric_equal_diag |].
  split; [exact disc_excess_is_gap_square |].
  split; [exact lever_equal_diag_element | exact lever_broken_diag_role_limit].
Qed.
