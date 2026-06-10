(** * BoundaryDichotomy.v — WHY the three faces split: criterion-from-below vs self-reflection
      Capstone (Phase 2) over cs/BoundaryDecidability.one_boundary_three_faces.

      THESIS (synthesis+observation, NOT a new theorem):
      The asymmetry of the three faces (#97: NUMBER decidable, PROGRAM/SET not) has a
      structural cause, here made a THEOREM.  Two SHAPES of a boundary-criterion:

        SHAPE 1 — criterion-FROM-BELOW (P2-conform): the boundary is drawn by a terminating
          invariant computed at a level BELOW the domain (matrix -> Z-discriminant ->
          decidable predicate); the criterion never quantifies over its own domain's deciders.
        SHAPE 2 — SELF-REFLECTION (the Russell shape): the domain can internalise ANY
          candidate decider and negate it on itself — for every dec there is d with
          Side d <-> dec d = false.  This is the shape Core_ERR blocks at the type level
          (russell_paradox_blocked) and Roles.v §XII calls circular status s = f(s).

      The two shapes are INCOMPATIBLE (element_drawn_excludes_self_reflective, via the one
      negb seed).  Consequences:
        NUMBER  : integer_eigenvalue on M2(Z) is Element-drawn — and now the face is the
                  REAL object (does this matrix have an integer eigenvalue?), not a bare nat:
                  integer_eigenvalue_iff_disc_square_Z, decider is_squareZ ∘ m_disc.
        PROGRAM : SelfProgrammable (HaltingRoleLimit) literally GIVES SelfReflective —
                  the halting boundary is role-limit-drawn BECAUSE it is Shape 2.
        SET     : Cantor RE-DERIVED as the COLLISION of the shapes: the diagonal boundary
                  of a self-enumerating domain would be BOTH Element-drawn (negb ∘ diag is
                  a decider) AND self-reflective (from surjectivity) — so no surjection.

    Reuses (genuine unification, not restatement):
      - cs/HaltingRoleLimit.v     : negb_no_fixpoint, SelfProgrammable.
      - cs/BoundaryDecidability.v : ElementDrawn / RoleLimitDrawn, diagonal_defeats_decider,
                                    is_square / is_square_iff.
      - cs/LawvereFixedPoint.v    : point_surjective (the Lawvere-root vocabulary).
    Cites (not imported):
      - TheoryOfSystems_Core_ERR.v: P2 (criterion from a lower level) — Shape 1 is P2-conform,
        Shape 2 is the P2-violating Russell pattern blocked there by level_lt_irrefl.
      - foundation/DiscriminantCompleteEigenvalue.v : the Q-version of the eigenvalue iff
        (rational_eigenvalue_iff_disc_square); ours is the INTEGER version on real matrices,
        complementary and cs-local.  foundation/MonicRationalRoot.v : char poly is monic,
        so rational eigenvalue = integer eigenvalue — the integer form is not weaker.

    Elements: 2×2 integer matrices (golden Δ=5, boost345 Δ=64, Hadamard-like Δ=8);
              programs (Prog) at the halting face; boolean predicates A->bool
    Roles:    ElementDrawn / RoleLimitDrawn = boundary STATUS (from #97);
              SelfReflective = the NEW role-shape of a criterion living at its OWN level;
              the decider = role-oracle; the diagonal witness d = the self-application role
    Rules:    element_drawn_excludes_self_reflective — the negb-seed incompatibility;
              is_squareZ ∘ m_disc — the terminating criterion-from-below;
              the parity step (s ≡ t mod 2 ⟹ λ=(t+s)/2 ∈ Z) — descent from square disc
              to an integer eigenvalue

    ============ E/R/R разбор ============
      Rules (L5): правило-обструкция — ОДНО negb-семя: Форма-1 (критерий-снизу) ∧ Форма-2
                  (само-отражение) рождает b = negb b — теорема несовместимости.
                  Правило-построение — is_squareZ ∘ m_disc: композиция инварианта (M2(Z)→Z)
                  и разрешимого предиката НИЖНЕГО уровня (P2 в действии).  Чётностный шаг
                  (s и t одной чётности ⟹ λ=(t+s)/2 ∈ Z) — спуск от квадрата к собственному
                  значению.
      Roles (L4): ElementDrawn / RoleLimitDrawn — СТАТУСЫ границы (из #97).  SelfReflective —
                  НОВАЯ роль-форма критерия: «домен отражает своих решателей» — критерий,
                  живущий на СВОЁМ уровне (расселовская форма, circular status s=f(s),
                  Roles.v §XII).  Решатель — роль-оракул; свидетель d — роль само-применения.
      Elements  : конкретные матрицы (золотая [[1,1],[1,0]] Δ=5 → role-limit φ; буст
                  [[5,4],[4,5]] Δ=64 → Element, собственные 9 и 1 — ось 3-4-5; адамарова
                  [[1,1],[1,−1]] Δ=8 → role-limit √2); программы; булевы предикаты.
    ДИАГНОСТИКА (P4): асимметрия трёх граней — теперь ТЕОРЕМА, не наблюдение: разрешимость =
      критерий-снизу (терминирующий процесс, без квантификации по решателям своего домена);
      неразрешимость = критерий-на-своём-уровне (само-отражение); несовместимость форм —
      водораздел.  Кантор — СЛЕДСТВИЕ водораздела: диагональная граница само-перечисляющего
      домена сидела бы по обе стороны.  Невынужденность проверена: ∃-форма SelfReflective
      (не code-функция) ВЫНУЖДЕНА дисциплиной вены B (функция-кодировщик требовала бы выбора);
      целые собственные значения не слабее рациональных (моничность, MonicRationalRoot.v);
      полярность dec d = false несёт negb — обструкция живёт ровно в отрицании.
      Честно: классика — Кантор 1891/Ловер 1969, чётность квадратичной формулы, Тьюринг;
      ново — наименование общей формы, теорема несовместимости как корень, Кантор-как-коллизия,
      числовая грань на настоящем объекте.  НЕ мета-теорема о всех границах.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Bool Lia.
From ToS Require Import cs.HaltingRoleLimit.
From ToS Require Import cs.BoundaryDecidability.
From ToS Require Import cs.LawvereFixedPoint.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  PART A — SHAPE 1 ON A REAL OBJECT: the integer-eigenvalue boundary    *)
(*                                                                         *)
(*  The NUMBER face of #97 used a bare nat discriminant.  Here the face   *)
(*  is the genuine vein-A object: a 2×2 INTEGER MATRIX and the question   *)
(*  "does it have an integer eigenvalue?".  The criterion factors through  *)
(*  a LOWER-level invariant (the discriminant in Z) plus a terminating     *)
(*  decider — the P2-conform shape.                                        *)
(* ===================================================================== *)

Record M2 : Type := mkM2 { a11 : Z; a12 : Z; a21 : Z; a22 : Z }.

Definition m_tr   (M : M2) : Z := a11 M + a22 M.
Definition m_det  (M : M2) : Z := a11 M * a22 M - a12 M * a21 M.
Definition m_disc (M : M2) : Z := m_tr M * m_tr M - 4 * m_det M.

(** The boundary: does M have an INTEGER eigenvalue (root of its char polynomial)?
    By monicity this coincides with rational eigenvalue (MonicRationalRoot.v). *)
Definition integer_eigenvalue (M : M2) : Prop :=
  exists lam : Z, lam * lam - m_tr M * lam + m_det M = 0.

Definition is_Zsquare (d : Z) : Prop := exists s : Z, s * s = d.

(** Forward: an eigenvalue λ exhibits the square — s := 2λ − tr. *)
Lemma eigenvalue_gives_square : forall M,
  integer_eigenvalue M -> is_Zsquare (m_disc M).
Proof.
  intros M [lam Hlam]. exists (2 * lam - m_tr M).
  unfold m_disc.
  replace ((2 * lam - m_tr M) * (2 * lam - m_tr M))
    with (4 * (lam * lam - m_tr M * lam + m_det M)
          + (m_tr M * m_tr M - 4 * m_det M)) by ring.
  rewrite Hlam. ring.
Qed.

(** Backward: the PARITY step.  s² = t²−4d forces s ≡ t (mod 2), so λ=(t+s)/2 ∈ Z. *)
Lemma square_gives_eigenvalue : forall M,
  is_Zsquare (m_disc M) -> integer_eigenvalue M.
Proof.
  intros M [s Hs]. unfold m_disc in Hs.
  set (t := m_tr M) in *. set (d := m_det M) in *.
  destruct (Z.Even_or_Odd (t + s)) as [[k Hk] | [k Hk]].
  - (* t+s even: λ := (t+s)/2 = k *)
    exists k.
    assert (Hsk : s = 2 * k - t) by lia.
    rewrite Hsk in Hs.
    assert (H4 : 4 * (k * k - t * k + d) = 0).
    { replace (4 * (k * k - t * k + d))
        with ((2 * k - t) * (2 * k - t) - (t * t - 4 * d)) by ring.
      rewrite Hs. ring. }
    lia.
  - (* t+s odd: then t−s odd too, and (t+s)(t−s)=4d gives odd = even *)
    exfalso.
    assert (Hts : (t + s) * (t - s) = 4 * d).
    { replace ((t + s) * (t - s)) with (t * t - s * s) by ring.
      rewrite Hs. ring. }
    rewrite Hk in Hts.
    assert (Hodd : t - s = 2 * (k - s) + 1) by lia.
    rewrite Hodd in Hts.
    assert (HX : (2 * k + 1) * (2 * (k - s) + 1)
                 = 2 * (2 * (k * (k - s)) + k + (k - s)) + 1) by ring.
    rewrite HX in Hts. lia.
Qed.

Theorem integer_eigenvalue_iff_disc_square_Z : forall M,
  integer_eigenvalue M <-> is_Zsquare (m_disc M).
Proof.
  intro M. split; [apply eigenvalue_gives_square | apply square_gives_eigenvalue].
Qed.

(** The terminating decider: perfect-square test on Z (negatives are never squares;
    nonnegatives reduce to the nat decider is_square of BoundaryDecidability). *)
Definition is_squareZ (d : Z) : bool :=
  match d with
  | Zneg _ => false
  | _ => is_square (Z.to_nat d)
  end.

Lemma is_squareZ_iff : forall d : Z, is_squareZ d = true <-> is_Zsquare d.
Proof.
  intro d. unfold is_squareZ, is_Zsquare.
  destruct d as [| p | p].
  - split.
    + intros _. exists 0. reflexivity.
    + intros _. reflexivity.
  - rewrite is_square_iff. split.
    + intros [r Hr]. exists (Z.of_nat r).
      rewrite <- Nat2Z.inj_mul. rewrite Hr.
      apply Z2Nat.id. lia.
    + intros [s Hsq]. exists (Z.to_nat (Z.abs s)).
      rewrite <- Z2Nat.inj_mul; [| apply Z.abs_nonneg | apply Z.abs_nonneg].
      f_equal. rewrite <- Z.abs_mul. rewrite Hsq. reflexivity.
  - split.
    + intro H. discriminate.
    + intros [s Hsq]. exfalso.
      assert (Hnn : 0 <= s * s) by nia.
      rewrite Hsq in Hnn. lia.
Qed.

Definition eigen_dec (M : M2) : bool := is_squareZ (m_disc M).

(** ★ THE NUMBER FACE ON THE REAL OBJECT: the integer-eigenvalue boundary of 2×2
    integer matrices is Element-drawn — Shape 1, criterion-from-below. *)
Theorem matrix_boundary_element_drawn : ElementDrawn integer_eigenvalue.
Proof.
  exists eigen_dec. intro M. unfold eigen_dec.
  rewrite is_squareZ_iff. symmetry.
  apply integer_eigenvalue_iff_disc_square_Z.
Qed.

(* --- Concrete atlas instances ------------------------------------------ *)

Definition golden_matrix  : M2 := mkM2 1 1 1 0.      (* Δ=5  : eigenvalue φ, role-limit *)
Definition boost345       : M2 := mkM2 5 4 4 5.      (* Δ=64 : eigenvalues 9 and 1      *)
Definition hadamard_like  : M2 := mkM2 1 1 1 (-1).   (* Δ=8  : eigenvalue √2, role-limit *)

Example golden_role_limit : eigen_dec golden_matrix = false.
Proof. reflexivity. Qed.

Example boost345_element : eigen_dec boost345 = true.
Proof. reflexivity. Qed.

(** The 3-4-5 axis again: the boost [[5,4],[4,5]] has INTEGER eigenvalue 9. *)
Example boost345_eigenvalue_nine :
  9 * 9 - m_tr boost345 * 9 + m_det boost345 = 0.
Proof. reflexivity. Qed.

Example hadamard_role_limit : eigen_dec hadamard_like = false.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — SHAPE 2 AND THE DICHOTOMY                                     *)
(* ===================================================================== *)

(** SHAPE 2 — SELF-REFLECTION: the domain internalises and negates every candidate
    decider on itself.  This is the COMMON form of the PROGRAM and SET faces, and
    the Russell pattern (criterion at its own level — what P2 forbids and Core_ERR
    blocks by level_lt_irrefl).  Stated with ∃ per decider, NOT a coding function:
    the functional form would smuggle choice (vein-B discipline). *)
Definition SelfReflective {Dom : Type} (Side : Dom -> Prop) : Prop :=
  forall dec : Dom -> bool, exists d, Side d <-> dec d = false.

(** Shape 2 forces role-limit (this is diagonal_defeats_decider, renamed through
    the shape — the naming is the point: the hypothesis IS self-reflection). *)
Theorem self_reflective_role_limit :
  forall (Dom : Type) (Side : Dom -> Prop),
    SelfReflective Side -> RoleLimitDrawn Side.
Proof.
  intros Dom Side H. apply diagonal_defeats_decider. exact H.
Qed.

(** ★ THE DICHOTOMY: the two shapes are INCOMPATIBLE — one negb seed.
    A boundary cannot be both drawn-from-below and self-reflective. *)
Theorem element_drawn_excludes_self_reflective :
  forall (Dom : Type) (Side : Dom -> Prop),
    ElementDrawn Side -> SelfReflective Side -> False.
Proof.
  intros Dom Side [dec Hdec] Hrefl.
  destruct (Hrefl dec) as [d Hd].
  apply (negb_no_fixpoint (dec d)).
  destruct (dec d) eqn:E; simpl.
  - (* E : dec d = true; Hd became Side d <-> true = false; goal: true = false *)
    apply (proj1 Hd). apply (proj1 (Hdec d)). exact E.
  - (* E : dec d = false; Hd became Side d <-> false = false; goal: false = true *)
    assert (Ht : dec d = true).
    { apply (proj2 (Hdec d)). apply (proj2 Hd). reflexivity. }
    rewrite E in Ht. exact Ht.
Qed.

(* ===================================================================== *)
(*  PART C — THE SET FACE AS A COLLISION: Cantor via the dichotomy        *)
(* ===================================================================== *)

(** The diagonal boundary of an enumeration g : "g's own diagonal says no". *)
Definition diagonal_side {A : Type} (g : A -> (A -> bool)) (a : A) : Prop :=
  g a a = false.

(** The diagonal boundary is ALWAYS Element-drawn: negb ∘ diag is a decider. *)
Lemma diagonal_boundary_element_drawn :
  forall (A : Type) (g : A -> (A -> bool)), ElementDrawn (diagonal_side g).
Proof.
  intros A g. exists (fun a => negb (g a a)). intro a.
  unfold diagonal_side.
  destruct (g a a); simpl; split; intro H; congruence.
Qed.

(** If g were point-surjective, the SAME boundary would be self-reflective. *)
Lemma surjective_diagonal_self_reflective :
  forall (A : Type) (g : A -> (A -> bool)),
    point_surjective g -> SelfReflective (diagonal_side g).
Proof.
  intros A g Hsurj dec.
  destruct (Hsurj dec) as [a Ha].
  exists a. unfold diagonal_side. rewrite Ha. tauto.
Qed.

(** ★ CANTOR AS THE COLLISION OF THE TWO SHAPES.  The diagonal boundary would sit on
    BOTH sides of the dichotomy — so the enumeration cannot exist.  (Third route to
    Cantor in this branch: direct negb (HaltingRoleLimit), Lawvere (LawvereFixedPoint),
    and now the dichotomy — the route that EXPLAINS the asymmetry.) *)
Theorem cantor_via_dichotomy :
  forall (A : Type) (g : A -> (A -> bool)), ~ point_surjective g.
Proof.
  intros A g Hsurj.
  exact (element_drawn_excludes_self_reflective A (diagonal_side g)
           (diagonal_boundary_element_drawn A g)
           (surjective_diagonal_self_reflective A g Hsurj)).
Qed.

(* ===================================================================== *)
(*  PART D — THE PROGRAM FACE IS LITERALLY SHAPE 2                        *)
(* ===================================================================== *)

(** SelfProgrammable (HaltingRoleLimit) GIVES self-reflection of the self-halting
    boundary: instantiate the diagonal program of D := (fun p _ => dec p) at itself. *)
Theorem self_programmable_gives_self_reflective :
  forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
    (forall D : Prog -> Prog -> bool, SelfProgrammable Prog Halts D) ->
    SelfReflective (fun q => Halts q q).
Proof.
  intros Prog Halts Hsp dec.
  destruct (Hsp (fun p _ => dec p)) as [diag Hdiag].
  exists diag. exact (Hdiag diag).
Qed.

Corollary halting_role_limit_via_dichotomy :
  forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
    (forall D : Prog -> Prog -> bool, SelfProgrammable Prog Halts D) ->
    RoleLimitDrawn (fun q : Prog => Halts q q).
Proof.
  intros Prog Halts Hsp.
  apply self_reflective_role_limit.
  apply self_programmable_gives_self_reflective. exact Hsp.
Qed.

(* ===================================================================== *)
(*  SYNTHESIS — the dichotomy BEHIND the three faces                       *)
(* ===================================================================== *)

(** ★ CAPSTONE.  one_boundary_three_faces (#97) juxtaposed the faces; here the
    asymmetry is a THEOREM: Shape 1 (criterion-from-below, P2-conform) draws the
    NUMBER face on the real matrix object; Shape 2 (self-reflection, the Russell
    shape) makes the PROGRAM face role-limit; and the SET face is the COLLISION
    of the two shapes.  One negb seed; two shapes; three faces. *)
Theorem boundary_dichotomy_three_faces :
  (* ROOT — the two shapes exclude each other *)
  (forall (Dom : Type) (Side : Dom -> Prop),
      ElementDrawn Side -> SelfReflective Side -> False)
  (* NUMBER — Shape 1 on the real object: integer-eigenvalue boundary of M2(Z) *)
  /\ ElementDrawn integer_eigenvalue
  (* PROGRAM — Shape 2: self-programmability = self-reflection => role-limit *)
  /\ (forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
        (forall D : Prog -> Prog -> bool, SelfProgrammable Prog Halts D) ->
        RoleLimitDrawn (fun q : Prog => Halts q q))
  (* SET — Cantor = the collision of the two shapes on the diagonal boundary *)
  /\ (forall (A : Type) (g : A -> (A -> bool)), ~ point_surjective g).
Proof.
  repeat split.
  - exact element_drawn_excludes_self_reflective.
  - exact matrix_boundary_element_drawn.
  - exact halting_role_limit_via_dichotomy.
  - exact cantor_via_dichotomy.
Qed.

Print Assumptions element_drawn_excludes_self_reflective.
Print Assumptions cantor_via_dichotomy.
Print Assumptions boundary_dichotomy_three_faces.
