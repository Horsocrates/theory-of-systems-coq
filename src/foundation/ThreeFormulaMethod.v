(** * ThreeFormulaMethod.v — the three-formula (E/R/R) method, reified as a THEOREM.

    Until now the "three-formula method" (every physical system = E-formula [ground, L1]
    + R-formula [spectrum / roles, L4] + R-formula [evolution / rule, L5]) was a PILE OF
    EXAMPLES (SHO, qubit, photon, acoustic, atoms).  It was called a method but never
    proved to BE one.  This file reifies it for finite (2x2 over Q) linear systems and
    proves the GENERATIVE ORDER as a determination theorem, honestly.

    The system IS its evolution operator M (the R-rule, L5).  Read off:
      rule    = M                                  (L5, R-formula: the evolution)
      roles   = char. polynomial of M = (tr M, det M)   (L4, R-formula: the spectrum)
      element = an extremal root of the char. poly       (L1, E-formula: the ground)

    WHAT IS PROVED (the honest core — reconciles the EXISTING "the three formulas are
    INDEPENDENT" result of SHOThreeFormulas.v with the generative order):
      * Rules -> Roles  (cayley_hamilton): the rule obeys its own roles, M^2 = tr*M - det*I
        — the char. polynomial is intrinsic to M; the roles are a FUNCTION of the rule.
      * Roles <-> Elements (vieta_from_roots): the eigenvalues' sum / product ARE (tr, det)
        — the roles are exactly the symmetric functions of the elements.
      * Roles -/-> Rules (generation_strict): the SAME roles (char. poly) come from
        DIFFERENT rules with different dynamics (identity vs shear, both char poly (x-1)^2)
        — so the generation Rules->Roles->Elements is STRICT (one-way), NOT invertible.
      * SCALE is FREE (scale_preserves_square via disc_scale): multiplying the rule by a
        scalar rescales the spectrum (disc by c^2) but PRESERVES STRUCTURE (the Element /
        role-limit status = whether disc is a perfect square).  Structure is generated;
        SCALE is the free input — exactly the "independence" SHOThreeFormulas saw, now
        located precisely as the scale.

    So: STRUCTURE flows Rules->Roles->Elements (generated, strict); SCALE is free input.
    The R-formula (spectrum) sits on the FINITIZATION BOUNDARY: Element iff disc a perfect
    square — cross-link to ReductionAtlasSynthesis / H1, developed in ThreeFormulaBoundary.v.
    (sho_companion_* foreshadows it: the SHO evolution rule is unimodular, det = 1.)

    Elements: concrete systems (identity, shear, SHO companion) instantiating (rule,roles,element)
    Roles:    the three formula-slots; STRUCTURE (generated) vs SCALE (free input)
    Rules:    a system's roles are the roots of its char. poly; the rule determines the
              roles (cayley_hamilton), the roles do NOT determine the rule (generation_strict)

    ============ E/R/R разбор ============
      Rules (L5): дано правило M — роли суть корни char-poly, элемент = экстремальный корень;
                  отображение детерминации M -> спектр -> основа НЕОБРАТИМО.
      Roles (L4): три формульных слота + статус спектра (Element/role-limit); структура
                  детерминирована, масштаб — свободный вход.
      Elements  : конкретные системы (тождество, сдвиг, SHO-компаньон) с реальными ℚ-данными.
    ДИАГНОСТИКА (P4): мета-система конечно-актуальна (оператор над ℚ, спектр конечен,
    детерминация — конечное вычисление); role-limit-сторона = спектр как незавершающийся
    процесс (иррациональное собств. значение), метод его ИМЕНУЕТ, не строит. Münchhausen:
    метод терминирует во ВХОДЕ (масштаб) как в постулате.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  A system = a 2x2 evolution operator over Q (the R-rule, L5)            *)
(* ===================================================================== *)

Record Mat2 := mk2 { a11 : Q; a12 : Q; a21 : Q; a22 : Q }.

Definition I2 : Mat2 := mk2 1 0 0 1.

Definition mmul (M N : Mat2) : Mat2 :=
  mk2 (a11 M * a11 N + a12 M * a21 N) (a11 M * a12 N + a12 M * a22 N)
      (a21 M * a11 N + a22 M * a21 N) (a21 M * a12 N + a22 M * a22 N).

Definition madd (M N : Mat2) : Mat2 :=
  mk2 (a11 M + a11 N) (a12 M + a12 N) (a21 M + a21 N) (a22 M + a22 N).

Definition smul (c : Q) (M : Mat2) : Mat2 :=
  mk2 (c * a11 M) (c * a12 M) (c * a21 M) (c * a22 M).

Definition meq (M N : Mat2) : Prop :=
  a11 M == a11 N /\ a12 M == a12 N /\ a21 M == a21 N /\ a22 M == a22 N.

(* The two R-formulas read off the rule: roles = (trace, determinant) = the char. poly. *)
Definition tr   (M : Mat2) : Q := a11 M + a22 M.
Definition det  (M : Mat2) : Q := a11 M * a22 M - a12 M * a21 M.
Definition disc (M : Mat2) : Q := tr M * tr M - 4 * det M.
Definition roles (M : Mat2) : Q * Q := (tr M, det M).

(* The E-formula: a ground / element is an extremal solution of the role-equation. *)
Definition char_poly (M : Mat2) (x : Q) : Q := x * x - tr M * x + det M.

(* ===================================================================== *)
(*  Rules -> Roles : the rule obeys its own roles (Cayley-Hamilton, 2x2)   *)
(* ===================================================================== *)

(** ★ M^2 = (tr M)*M - (det M)*I.  The characteristic polynomial is intrinsic to the
    rule M; the roles are a function of the rule. *)
Lemma cayley_hamilton (M : Mat2) :
  meq (mmul M M) (madd (smul (tr M) M) (smul (- det M) I2)).
Proof.
  unfold meq, mmul, madd, smul, I2, tr, det; simpl; repeat split; ring.
Qed.

(** The roles are literally a function of the rule (well-defined on Qeq-equal rules). *)
Lemma roles_respect (M N : Mat2) :
  meq M N -> tr M == tr N /\ det M == det N.
Proof.
  intros [H1 [H2 [H3 H4]]]; unfold tr, det; split.
  - lra.
  - rewrite H1, H2, H3, H4; ring.
Qed.

(* ===================================================================== *)
(*  Roles <-> Elements : the eigenvalues' sum / product ARE (tr, det)      *)
(* ===================================================================== *)

(** ★ If l, m are two DISTINCT roots of the char. poly (the elements / eigenvalues), then
    l + m = tr M and l*m = det M: the roles are exactly the symmetric functions of the
    elements (Roles <-> Elements). *)
Lemma vieta_from_roots (M : Mat2) (l m : Q) :
  char_poly M l == 0 -> char_poly M m == 0 -> ~ (l == m) ->
  l + m == tr M /\ l * m == det M.
Proof.
  unfold char_poly; intros Hl Hm Hne.
  assert (Hfac : (l - m) * (l + m - tr M)
                 == (l*l - tr M * l + det M) - (m*m - tr M * m + det M)) by ring.
  rewrite Hl, Hm in Hfac.
  assert (Hfac0 : (l - m) * (l + m - tr M) == 0) by (rewrite Hfac; ring).
  apply Qmult_integral in Hfac0.
  destruct Hfac0 as [Hlm | Htr].
  - exfalso; apply Hne; lra.
  - assert (Htr' : l + m == tr M) by lra.
    split; [ exact Htr' | ].
    assert (Hdet : det M == tr M * l - l * l) by lra.
    rewrite Hdet, <- Htr'; ring.
Qed.

(* ===================================================================== *)
(*  Roles -/-> Rules : the generation is STRICT (one-way)                  *)
(* ===================================================================== *)

Definition shear : Mat2 := mk2 1 1 0 1.
Definition ident : Mat2 := mk2 1 0 0 1.

(* First component of the rule's action on a vector (x,y): exposes the dynamics. *)
Definition vfst (M : Mat2) (x y : Q) : Q := a11 M * x + a12 M * y.

(** ★ Identity and shear have the SAME roles (tr = 2, det = 1; char poly (x-1)^2) yet
    DIFFERENT dynamics — so the spectrum does NOT determine the rule. *)
Lemma generation_strict :
  (tr shear == tr ident /\ det shear == det ident)
  /\ ~ (vfst shear 0 1 == vfst ident 0 1).
Proof.
  split.
  - unfold tr, det, shear, ident; simpl; split; ring.
  - unfold vfst, shear, ident; simpl; lra.
Qed.

(* ===================================================================== *)
(*  SCALE is FREE : structure (Element/role-limit status) is scale-invariant *)
(* ===================================================================== *)

(** Scaling the rule by c rescales the discriminant by exactly c^2. *)
Lemma disc_scale (c : Q) (M : Mat2) :
  disc (smul c M) == (c * c) * disc M.
Proof.
  unfold disc, tr, det, smul; simpl; ring.
Qed.

Definition is_square (q : Q) : Prop := exists r : Q, q == r * r.

(** ★ A rational (Element) spectrum stays Element under scaling: the structure is
    generated, the SCALE is the free input. *)
Lemma scale_preserves_square (c : Q) (M : Mat2) :
  is_square (disc M) -> is_square (disc (smul c M)).
Proof.
  intros [r Hr]. exists (c * r).
  rewrite disc_scale, Hr; ring.
Qed.

(* ===================================================================== *)
(*  Concrete anchors                                                       *)
(* ===================================================================== *)

(** The identity's role-equation is (x-1)^2 = 0 (degenerate ground at x = 1). *)
Lemma char_poly_ident (x : Q) : char_poly ident x == (x - 1) * (x - 1).
Proof. unfold char_poly, tr, det, ident; simpl; ring. Qed.

(** The SHO evolution rule x(t+1) = (2-k)x(t) - x(t-1) has companion [[2-k,-1],[1,0]];
    its rule is UNIMODULAR (det = 1, a rotation) — foreshadows the boundary (Niven). *)
Definition companion (k : Q) : Mat2 := mk2 (2 - k) (- (1)) 1 0.

Lemma sho_companion_unimodular (k : Q) : det (companion k) == 1.
Proof. unfold det, companion; simpl; ring. Qed.

Lemma sho_companion_trace (k : Q) : tr (companion k) == 2 - k.
Proof. unfold tr, companion; simpl; ring. Qed.

(* ===================================================================== *)
(*  Capstone: the three-formula method as one theorem                      *)
(* ===================================================================== *)

(** The method:
      (Rules->Roles)   the rule obeys its own roles (cayley_hamilton);
      (Roles<->Elements) the roles are the symmetric functions of the elements (vieta);
      (Roles-/->Rules) the same roles arise from different rules (generation_strict);
      (scale free)     a rational spectrum stays rational under scaling (scale_preserves_square).
    Structure is generated Rules->Roles->Elements (strict); the SCALE is the free input. *)
Theorem three_formula_method :
  (forall M, meq (mmul M M) (madd (smul (tr M) M) (smul (- det M) I2)))
  /\ (forall M l m, char_poly M l == 0 -> char_poly M m == 0 -> ~ (l == m) ->
        l + m == tr M /\ l * m == det M)
  /\ ((tr shear == tr ident /\ det shear == det ident)
        /\ ~ (vfst shear 0 1 == vfst ident 0 1))
  /\ (forall c M, is_square (disc M) -> is_square (disc (smul c M))).
Proof.
  split; [ exact cayley_hamilton | ].
  split; [ exact vieta_from_roots | ].
  split; [ exact generation_strict | exact scale_preserves_square ].
Qed.
