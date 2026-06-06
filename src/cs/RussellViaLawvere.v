(** * RussellViaLawvere.v — Russell, the Liar, Grelling, Cantor-for-Prop as ONE Lawvere diagonal
      Breadth: the Prop-level face of the one diagonal.  At B := Prop with f := not (negation, which
      is fixpoint-free: ¬P ≠ P), Lawvere's contrapositive gives Cantor for the powerset (no point-
      surjection A → (A → Prop)), and the same negation-diagonal IS Russell's paradox, the Liar, and
      Grelling.  Together with the bool face (Cantor/halting/Rice, cs/BoundaryDecidability.v) and
      truth (Tarski, cs/TarskiUndefinability.v), every classical self-reference limit is one root.

    ★ Gödel is DELIBERATELY excluded — the project's stance is undefinability / the diagonal lemma
    (a clean diagonal), NOT a metamathematical incompleteness theorem.  Russell, Liar, Grelling are
    diagonal/limit facts; they are exactly Roles.v §XII's circular status s = negb s, here on Prop.

    Reuses cs/LawvereFixedPoint.v (point_surjective, lawvere_no_point_surjection) and
    cs/TarskiUndefinability.v (iff_not_self_absurd).  Honest level: classical; the contribution is
    the unification under the one root, 0 axioms.

    Elements: types A; a membership relation mem : A → A → Prop; propositions P : Prop
    Roles:    "the set of all non-self-members" R / the Liar p = a witness-role of the limit;
              ¬ as a fixpoint-free endo on Prop
    Rules:    the diagonal `fun x => ~ mem x x` / `~ p`; negation has no fixed point on Prop

    ============ E/R/R разбор ============
      Rules (L5): диагональ `fun x => ~ mem x x` / `~p`; отрицание без неподвижной точки на Prop.
      Roles (L4): «множество всех не-само-членов» R / Лжец p — роль-свидетель предела; ¬ = fixpoint-free эндо.
      Elements  : типы A; членство mem : A→A→Prop; предложения P : Prop.
    ДИАГНОСТИКА (P4): ВШИРЬ — Рассел/Лжец/Греллинг/Кантор-Prop = ОДИН негационный диагональ Ловера
      (B=Prop, f=not).  Те же, что Кантор-bool/halting/Райс/Тарский.  not_no_fixpoint (¬P≠P) = Prop-семя;
      Roles §XII (bool s=negb s) и эти (Prop) — bool/Prop-грани одного.  Гёдель НЕ включён (позиция
      проекта: undefinability/диагональ, не неполнота).  Честно: классика; вклад — унификация под корнем.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import cs.LawvereFixedPoint.
From ToS Require Import cs.TarskiUndefinability.

(** Negation is fixpoint-free on Prop: ¬P ≠ P (else P ↔ ¬P, absurd). The Prop seed of Lawvere. *)
Lemma not_no_fixpoint : forall P : Prop, ~ P <> P.
Proof.
  intros P H. apply (iff_not_self_absurd P). rewrite H. tauto.
Qed.

(** Cantor for the powerset: no point-surjection A → (A → Prop) — Lawvere at B := Prop, f := not. *)
Corollary cantor_prop :
  forall (A : Type) (phi : A -> (A -> Prop)), ~ point_surjective phi.
Proof.
  intros A phi. apply (lawvere_no_point_surjection A Prop not). exact not_no_fixpoint.
Qed.

(** ★ RUSSELL'S PARADOX: no "set" R whose members are exactly the non-self-members — the negation
    diagonal at the would-be witness R. *)
Theorem russell_no_universal_set :
  forall (A : Type) (mem : A -> A -> Prop),
    ~ exists R : A, forall x, mem R x <-> ~ mem x x.
Proof.
  intros A mem [R HR]. exact (iff_not_self_absurd (mem R R) (HR R)).
Qed.

(** The LIAR: no proposition equivalent to its own negation. *)
Corollary liar : ~ exists p : Prop, p <-> ~ p.
Proof. intros [p Hp]. exact (iff_not_self_absurd p Hp). Qed.

(** GRELLING (heterological): no "applies-to-itself" witness h with app_self h ↔ ¬ app_self h. *)
Corollary grelling :
  forall (W : Type) (app_self : W -> Prop),
    ~ exists h : W, app_self h <-> ~ app_self h.
Proof. intros W app_self [h Hh]. exact (iff_not_self_absurd (app_self h) Hh). Qed.

(** ★ ONE DIAGONAL on Prop: the seed (¬ fixpoint-free), Cantor-for-Prop, Russell, the Liar. *)
Theorem paradoxes_one_diagonal :
  (forall P : Prop, ~ P <> P)
  /\ (forall (A : Type) (phi : A -> (A -> Prop)), ~ point_surjective phi)
  /\ (forall (A : Type) (mem : A -> A -> Prop), ~ exists R, forall x, mem R x <-> ~ mem x x)
  /\ (~ exists p : Prop, p <-> ~ p).
Proof.
  split; [exact not_no_fixpoint |].
  split; [exact cantor_prop |].
  split; [exact russell_no_universal_set | exact liar].
Qed.

(** So the bool face (Cantor/halting/Rice — cs/BoundaryDecidability.one_boundary_three_faces) and the
    Prop face (Russell/Liar/Grelling/Cantor-Prop here, and Tarski) are ONE root: Lawvere's diagonal
    with a fixpoint-free endo (negb on bool, not on Prop).  Roles.v §XII's circular status s = negb s
    is this seed.  Gödel's incompleteness is the only sibling deliberately left out (project stance). *)

Print Assumptions paradoxes_one_diagonal.
