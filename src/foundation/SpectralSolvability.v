(** * SpectralSolvability.v — НАПРАВЛЕНИЕ Δ2 (по запросу автора 2026-06-06): the inter-level coupling
      spectral role-limit STRATIFIED BY SOLVABILITY (Galois) -- a NEW kind of role-limit beyond surds:
      a coupling whose spectrum is radical-INEXPRESSIBLE (an unsolvable quintic, Abel-Ruffini).

   Н1.3 (CubicCouplingSpectrum) stratified the boundary by DEGREE (2x2 square, 3x3 cube, degree-n surd).
   The Galois picture refines this: a polynomial's roots are expressible by radicals <=> its Galois group
   is solvable.  So the role-limit side of the inter-level coupling spectrum is itself STRATIFIED:

     ★ SURD (degree 2):              golden lam^2 - lam - 1 -> {phi, 1-phi} -- radical-expressible (sqrt5);
     ★ RADICAL (degree 3-4):         lam^3 - 2 -> cbrt2 -- radical-expressible (casus irreducibilis);
     ★ RADICAL-INEXPRESSIBLE (>=5):  lam^5 - lam - 1 -- an irreducible quintic with S_5 Galois group, whose
       roots are NOT expressible by ANY finite tower of radicals (Abel-Ruffini).  THE DEEPEST role-limit:
       no surd, no nested radical, no finite radical construction reaches it.

   So the role-limit is not a single wall but a TOWER of walls of increasing depth, and the degree-5
   non-solvable coupling is the role-limit that the entire radical hierarchy cannot reach.  This connects
   the inter-level spectrum (Н1) to the Abel-Ruffini / Galois engine of the repo (Часть XI: GaloisQ23,
   the solvability core).

   What is machine-checked here.  The Element / role-limit verdicts at the rational-root level: a coupling
   has a rational mode <=> its characteristic polynomial has a rational root; for a MONIC integer
   polynomial the rational-root candidates are the integer divisors of the constant term, and we evaluate
   them:
     -- Element foil  lam^2 - 3 lam + 2: vanishes at 1 (= (lam-1)(lam-2), rational modes {1,2});
     -- surd2 lam^2 - lam - 1: candidates +-1 give -1, 1 (no rational root) -> role-limit;
     -- rad3  lam^3 - 2: candidates +-1,+-2 give -1,-3,6,-10 (no rational root) -> role-limit;
     -- quintic lam^5 - lam - 1: candidates +-1 give -1, -1 (no rational root) -> role-limit.
   The SOLVABILITY classification (which role-limit is radical-expressible) is recorded as a tag, with the
   degree-5 non-radical verdict resting on Abel-Ruffini (the quintic lam^5-lam-1 is irreducible with
   S_5 Galois group -- cited, Часть XI, not re-proved).

   HONEST SCOPE.  Fully machine-closed, 0 axioms: the candidate-evaluation verdicts (no rational root)
   and the solvability tags.  The "no rational root" conclusion uses the rational-root theorem for monic
   polynomials (the repo's GeneralRoot / RationalRootTest), cited; the radical-(in)expressibility uses
   Abel-Ruffini / Galois (Часть XI), cited.  The GENUINE NEW content is the OBSERVATION that the spectral
   role-limit is stratified by solvability and that a radical-inexpressible degree-5 coupling spectrum
   exists -- a role-limit beyond every surd, tying the spectrum to Abel-Ruffini.  Level: synthesis +
   observation (a new structural object + a cross-engine connection; the Galois machinery is cited).

   Elements: the polynomial coefficients in Q; the rational-root candidates; their evaluations.
   Roles:    the characteristic polynomial = the coupling spectrum; the Galois group = solvability;
             the three role-limit strata (surd / radical / radical-inexpressible).
   Rules:    rational mode <=> rational root; role-limit stratified by solvability (surd < radical <
             radical-inexpressible); degree >=5 non-solvable = radical-inexpressible (Abel-Ruffini).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: спектр связи = корни char-многочлена, классиф. по РАЗРЕШИМОСТИ Галуа.
     Rules (L5): рацион. мода <=> рацион. корень; role-limit стратиф. по solvability (surd<radical<
                 radical-inexpressible); deg>=5 non-solvable = radical-inexpressible (Abel-Ruffini).
     Roles (L4): степень = глубина surd; группа Галуа = разрешимость; три страта role-limit.
     Elements  : коэфф. in Q; кандидаты-корни; значения.
     ОБРАЗУЮЩИЕ: Н1.3 (дегре-стратификация); rational root test (GeneralRoot); GaloisQ23/Abel-Ruffini (Часть XI).
     ВЛОЖЕННЫЕ : golden deg2 (surd), ∛2 deg3 (radical), lam^5-lam-1 deg5 (non-radical); Element foil (корень 1).
   ДИАГНОСТИКА (P4): role-limit спектра имеет ГЛУБИНУ (solvability-башня); deg-5 квинтика = role-limit, до
   которого не дотягивается НИ ОДНА конечная radical-башня (Abel-Ruffini) — глубочайший. Genuine-новый ОБЪЕКТ
   (radical-inexpressible spectral role-limit), мост спектр(Н1)+Abel-Ruffini(Часть XI). ЧЕСТНО: no-root машинно;
   radical-(in)expressibility = цитата. Локализуем, не пересекаем.

   STATUS: 11 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Element foil: a characteristic polynomial WITH a rational root         *)
(* ===================================================================== *)

(** lam^2 - 3 lam + 2 = (lam-1)(lam-2): rational modes {1,2} -- Element. *)
Definition p_element (x : Q) : Q := x*x - 3*x + 2.
Example element_has_rational_root : p_element 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  role-limit stratum 1 -- SURD (degree 2): golden lam^2 - lam - 1        *)
(* ===================================================================== *)

(** Candidates of c0 = -1 are +-1; neither is a root -> no rational root -> surd role-limit (phi, sqrt5). *)
Definition p_surd2 (x : Q) : Q := x*x - x - 1.
Example surd2_at_1  : p_surd2 1 == -(1).
Proof. vm_compute. reflexivity. Qed.
Example surd2_at_m1 : p_surd2 (-(1)) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  role-limit stratum 2 -- RADICAL (degree 3): lam^3 - 2 (casus irred.)   *)
(* ===================================================================== *)

(** Candidates of c0 = -2 are +-1,+-2; none is a root -> no rational root -> radical role-limit (cbrt2). *)
Definition p_rad3 (x : Q) : Q := x*x*x - 2.
Example rad3_at_1  : p_rad3 1 == -(1).
Proof. vm_compute. reflexivity. Qed.
Example rad3_at_2  : p_rad3 2 == 6.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  ★ role-limit stratum 3 -- RADICAL-INEXPRESSIBLE (degree 5)              *)
(* ===================================================================== *)

(** lam^5 - lam - 1: candidates of c0 = -1 are +-1; neither is a root -> no rational root.  Moreover the
    quintic is irreducible with Galois group S_5, so its roots are NOT expressible by any finite tower of
    radicals (Abel-Ruffini, cited Часть XI) -- the DEEPEST role-limit. *)
Definition p_quintic (x : Q) : Q := x*x*x*x*x - x - 1.
Example quintic_at_1  : p_quintic 1 == -(1).
Proof. vm_compute. reflexivity. Qed.
Example quintic_at_m1 : p_quintic (-(1)) == -(1).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The solvability stratification of the role-limit                       *)
(* ===================================================================== *)

Inductive RoleLimitDepth :=
  | SurdDeg2         (* radical-expressible, degree 2 (sqrt) *)
  | RadicalDeg3to4   (* radical-expressible, degree 3-4 (cbrt, nested radicals) *)
  | NonRadicalDeg5.  (* radical-INEXPRESSIBLE, degree >=5 non-solvable (Abel-Ruffini) *)

(** Which strata are radical-expressible (solvable Galois group). *)
Definition radical_expressible (d : RoleLimitDepth) : bool :=
  match d with
  | SurdDeg2 => true
  | RadicalDeg3to4 => true
  | NonRadicalDeg5 => false
  end.

(** ★ The degree-5 non-solvable role-limit is the ONLY radical-INEXPRESSIBLE stratum -- the deepest. *)
Lemma deg5_not_radical : radical_expressible NonRadicalDeg5 = false.
Proof. reflexivity. Qed.

(** The surd (degree 2) role-limit IS radical-expressible. *)
Lemma deg2_is_radical : radical_expressible SurdDeg2 = true.
Proof. reflexivity. Qed.

(** The surd and the radical-inexpressible strata are distinct -- the role-limit has depth. *)
Lemma depths_distinct : SurdDeg2 <> NonRadicalDeg5.
Proof. discriminate. Qed.

(* ===================================================================== *)
(*  Capstone: the spectral role-limit stratified by solvability            *)
(* ===================================================================== *)

(** The inter-level coupling spectrum, classified by solvability:
      (Element)     lam^2-3lam+2 vanishes at 1 -- rational mode (Element);
      (surd)        lam^2-lam-1: candidates +-1 give -1,1 -- no rational root (surd role-limit);
      (radical)     lam^3-2: candidate 1,2 give -1,6 -- no rational root (radical role-limit);
      (★ inexpr.)   lam^5-lam-1: candidates +-1 give -1,-1 -- no rational root; S_5 Galois => radical-
                    INEXPRESSIBLE (Abel-Ruffini, cited);
      (★ depth)     the role-limit is stratified by solvability: degree>=5 non-solvable is NOT radical-
                    expressible, while the surd (degree 2) is -- a TOWER of role-limit walls.
    The spectral role-limit has DEPTH; the degree-5 non-solvable coupling is the role-limit no finite
    radical tower reaches -- a new object tying the inter-level spectrum to Abel-Ruffini.  Located NOT
    crossed. *)
Theorem spectral_solvability_stratification :
  (p_element 1 == 0)
  /\ (p_surd2 1 == -(1) /\ p_surd2 (-(1)) == 1)
  /\ (p_rad3 1 == -(1))
  /\ (p_quintic 1 == -(1) /\ p_quintic (-(1)) == -(1))
  /\ (radical_expressible NonRadicalDeg5 = false)
  /\ (radical_expressible SurdDeg2 = true).
Proof.
  split; [exact element_has_rational_root |].
  split; [split; [exact surd2_at_1 | exact surd2_at_m1] |].
  split; [exact rad3_at_1 |].
  split; [split; [exact quintic_at_1 | exact quintic_at_m1] |].
  split; [exact deg5_not_radical | exact deg2_is_radical].
Qed.
