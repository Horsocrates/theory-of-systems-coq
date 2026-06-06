(** * LawvereFixedPoint.v — the categorical ROOT: Lawvere's fixed-point theorem
      The mathematical bottom of EVERY diagonal in this project.  Cantor, halting, Rice, Russell,
      the Liar, Tarski's undefinability — all are ONE instance of Lawvere (1969): a point-surjective
      φ : A → (A ⇒ B) forces every endo f : B → B to have a fixed point; contrapositively, if B has a
      fixpoint-free endo (bool's negb), no such surjection exists.

      Our whole CS branch rests on `negb_no_fixpoint` (bool has a fixpoint-free endo) — that IS the
      seed of Lawvere.  BoundaryDecidability.one_boundary_three_faces (number/program/set) are three
      dresses of this one seed; diagonal_defeats_decider is its decider-shaped sibling.  Here we
      formalise the root and re-derive Cantor as a literal Lawvere instance.

    The full categorical statement (any cartesian closed category) generalises this Set/Type-level
    version; its home in this repo is SetoidCat (the predicative topos of Part XIV, src/category/).
    Conceptual neighbours sharing the seed: Roles.v §XII (circular_dep_is_paradox = Russell/Liar),
    settheory/ProcessDiagonal.v (uncountability), cs/HaltingRoleLimit.v + cs/RiceRoleLimit.v.

    Honest level: Lawvere 1969 is classical; the contribution is formalising the root + exhibiting
    our branch's diagonals as its instances (synthesis+framing).  0 axioms.

    Elements: types A, B; the morphism φ : A → (A → B); an endomorphism f : B → B
    Roles:    "point-surjective" (φ enumerates all A→B) = an overview-role; a fixed point of f = a goal-role
    Rules:    the diagonal `fun a => f (φ a a)` (self-application + f) — one rule producing the fixed point

    ============ E/R/R разбор ============
      Rules (L5): диагональ `fun a => f (φ a a)` (само-применение + f) — одно правило, рождающее
                  неподвижную точку; контрапозиция = семя всех диагоналей.
      Roles (L4): «точечная сюръекция» (φ перечисляет все A→B); неподвижная точка f — роль-цель.
      Elements  : типы A, B; морфизм φ : A→(A→B); эндо f : B→B.
    ДИАГНОСТИКА (P4): КОРЕНЬ всех наших диагоналей.  Кантор/halting/Райс/Рассел/Тарский — один
      экземпляр Ловера (B=bool, f=negb без неподвижной точки ⟹ нет сюръекции).  negb_no_fixpoint =
      семя; one_boundary_three_faces (Ф1) = три обличья; diagonal_defeats_decider = решательный
      собрат.  Категориальное обобщение (CCC) — SetoidCat, Часть XIV.  Честно: классика 1969; вклад —
      формализация корня + демонстрация, что наши диагонали суть его экземпляры.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Bool Lia.
From ToS Require Import cs.HaltingRoleLimit.

(** φ is point-surjective: it hits every function A → B. *)
Definition point_surjective {A B : Type} (φ : A -> (A -> B)) : Prop :=
  forall g : A -> B, exists a, φ a = g.

(** ★ LAWVERE'S FIXED-POINT THEOREM.  If some φ : A → (A → B) is point-surjective, then EVERY
    endomorphism f : B → B has a fixed point.  The witness is the diagonal `fun a => f (φ a a)`. *)
Theorem lawvere_fixed_point :
  forall (A B : Type) (φ : A -> (A -> B)),
    point_surjective φ -> forall f : B -> B, exists b, f b = b.
Proof.
  intros A B φ Hsurj f.
  destruct (Hsurj (fun a => f (φ a a))) as [a0 Ha0].
  exists (φ a0 a0).
  pose proof (f_equal (fun h : A -> B => h a0) Ha0) as E. simpl in E.
  (* E : φ a0 a0 = f (φ a0 a0) *)
  symmetry. exact E.
Qed.

(** ★ Contrapositive: a fixpoint-free endo on B blocks every point-surjection onto A → B.
    THIS is the engine of every diagonal argument. *)
Corollary lawvere_no_point_surjection :
  forall (A B : Type) (f : B -> B),
    (forall b, f b <> b) ->
    forall φ : A -> (A -> B), ~ point_surjective φ.
Proof.
  intros A B f Hnofix φ Hsurj.
  destruct (lawvere_fixed_point A B φ Hsurj f) as [b Hb].
  exact (Hnofix b Hb).
Qed.

(** Cantor IS Lawvere at B := bool, f := negb — re-deriving cs/HaltingRoleLimit.cantor_no_surjection. *)
Corollary cantor_via_lawvere :
  forall (A : Type) (g : A -> (A -> bool)),
    ~ (forall f : A -> bool, exists a, g a = f).
Proof.
  intros A g. apply (lawvere_no_point_surjection A bool negb).
  intro b. intro H. apply (negb_no_fixpoint b). symmetry. exact H.
Qed.

(** And at B := nat, f := S (successor, fixpoint-free): nat does not enumerate nat → nat. *)
Corollary nat_fun_not_enumerable :
  forall φ : nat -> (nat -> nat), ~ point_surjective φ.
Proof.
  intro φ. apply (lawvere_no_point_surjection nat nat S). intro n. lia.
Qed.

(** ★ ONE ROOT: our CS diagonals are Lawvere.  (1) Lawvere forces a fixed point from a point-
    surjection; (2) the seed is bool's fixpoint-free negb; (3) hence Cantor (the SET face of
    one_boundary_three_faces).  The PROGRAM face (no_halting_decider) and the SEMANTICS face
    (rice_role_limit) share the identical seed via diagonal_defeats_decider; Russell/Liar
    (Roles.v §XII) and the repo's uncountability (settheory/ProcessDiagonal.v) too. *)
Theorem cs_diagonals_are_lawvere :
  (forall (A B : Type) (φ : A -> (A -> B)),
     point_surjective φ -> forall f : B -> B, exists b, f b = b)
  /\ (forall b : bool, b <> negb b)
  /\ (forall (A : Type) (g : A -> (A -> bool)), ~ (forall f, exists a, g a = f)).
Proof.
  split; [exact lawvere_fixed_point |].
  split; [exact negb_no_fixpoint | exact cantor_via_lawvere].
Qed.

Print Assumptions lawvere_fixed_point.
Print Assumptions cs_diagonals_are_lawvere.
