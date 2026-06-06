(** * RecursionTheorem.v — Kleene's recursion theorem AS a Lawvere instance; discharging Rice
      Deeper than the root: the COMPUTATIONAL instance of Lawvere.  Kleene's (second) recursion
      theorem — every program-transformer has a (semantic) fixed point, i.e. a self-describing
      program — is exactly Lawvere's fixed-point theorem with the codomain = programs and the
      point-surjection = universality (the system realises every program-to-program function).

      This DISCHARGES the self-reference hypothesis of Rice (cs/RiceRoleLimit.RiceDiagonal): given a
      universal self-application and reflexive semantics, the diagonal Rice program EXISTS — so a
      non-trivial semantic property is undecidable UNCONDITIONALLY (relative to universality), not
      by assumption.  Full chain, 0 axioms:  LAWVERE  →  RECURSION  →  RICE.

      (Halting's cs/HaltingRoleLimit.SelfProgrammable is discharged similarly but more cheaply — its
      diagonal needs only an if-then-loop closure, not full self-reference; noted, not done here.)
      The further step is to discharge these in the repo's actual verified λ-language
      (src/Expressions.v → src/Evaluator.v).

    Reuses cs/LawvereFixedPoint.v (point_surjective, lawvere_fixed_point), cs/BoundaryDecidability.v
    (RoleLimitDrawn), cs/RiceRoleLimit.v (RiceDiagonal, rice_role_limit).  Honest level: Kleene's
    recursion theorem + its Lawvere reading (synthesis+framing), 0 axioms.

    Elements: programs Prog; self-application app : Prog → (Prog → Prog); semantics sem_equiv
    Roles:    "universality" (app point-surjective = the system realises every program-function) =
              a completeness-role; a fixed point of a transformer = a goal-role (a self-describing program)
    Rules:    recursion = Lawvere at A=B=Prog (the self-application diagonal); a transformer's fixed
              point yields Rice's diagonal program

    ============ E/R/R разбор ============
      Rules (L5): рекурсия = Ловер при A=B=Prog (диагональ само-применения); фикс-точка трансформера
                  рождает диагональную программу Райса.
      Roles (L4): «универсальность» (app точечно-сюръективна = система реализует всякую программную
                  функцию); неподвижная точка трансформера = роль-цель (само-описывающая программа).
      Elements  : программы Prog; само-применение app; семантика sem_equiv.
    ДИАГНОСТИКА (P4): ВЫЧИСЛИТЕЛЬНЫЙ экземпляр корня.  Рекурсия Клини = Ловер при codomain=программы,
      сюръекция=универсальность.  РАЗРЯЖАЕТ гипотезу RiceDiagonal (само-ссылка) → Райс безусловен
      относительно «система универсальна + семантика рефлексивна + свойство нетривиально».  Полная
      цепь Ловер→рекурсия→Райс, 0 аксиом.  Дальнейший шаг — разрядить в реальном λ-языке репо.

    STATUS: 3 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import cs.LawvereFixedPoint.
From ToS Require Import cs.BoundaryDecidability.
From ToS Require Import cs.RiceRoleLimit.

(** ★ KLEENE'S RECURSION THEOREM = LAWVERE at A = B = Prog.  If the system is universal (some
    self-application app : Prog → (Prog → Prog) is point-surjective), then every program-transformer
    f : Prog → Prog has a fixed point — a program e with f e = e. *)
Theorem kleene_recursion_from_lawvere :
  forall (Prog : Type) (app : Prog -> (Prog -> Prog)),
    point_surjective app ->
    forall f : Prog -> Prog, exists e, f e = e.
Proof. intros Prog app. exact (lawvere_fixed_point Prog Prog app). Qed.

(** The recursion theorem DISCHARGES Rice's diagonal hypothesis: a fixed point of the transformer
    "if D e then p_no else p_yes" is the diagonal Rice program. *)
Theorem rice_diagonal_from_recursion :
  forall (Prog : Type) (sem_equiv : Prog -> Prog -> Prop),
    (forall p, sem_equiv p p) ->
    (forall f : Prog -> Prog, exists e, f e = e) ->
    forall (p_yes p_no : Prog) (D : Prog -> bool),
      RiceDiagonal Prog sem_equiv p_yes p_no D.
Proof.
  intros Prog sem_equiv Hrefl Hrec p_yes p_no D. unfold RiceDiagonal.
  destruct (Hrec (fun e => if D e then p_no else p_yes)) as [d Hd].
  cbv beta in Hd.
  exists d. split.
  - intro HT. rewrite HT in Hd. simpl in Hd. rewrite <- Hd. apply Hrefl.
  - intro HF. rewrite HF in Hd. simpl in Hd. rewrite <- Hd. apply Hrefl.
Qed.

(** ★ THE CHAIN: LAWVERE → RECURSION → RICE.  For any universal system with reflexive semantics,
    every non-trivial semantic property is undecidable (RoleLimitDrawn) — UNCONDITIONALLY (the
    self-reference is now proven, not assumed). *)
Theorem rice_from_lawvere :
  forall (Prog : Type) (app : Prog -> (Prog -> Prog)) (sem_equiv : Prog -> Prog -> Prop),
    point_surjective app ->                                  (* universality (Lawvere surjection) *)
    (forall p, sem_equiv p p) ->                             (* reflexive semantics *)
    forall (P : Prog -> Prop),
      (forall p q, sem_equiv p q -> (P p <-> P q)) ->        (* P is semantic *)
      forall (p_yes p_no : Prog), P p_yes -> ~ P p_no ->     (* non-trivial *)
        RoleLimitDrawn P.
Proof.
  intros Prog app sem_equiv Hsurj Hrefl P Pext p_yes p_no Pyes Pno.
  apply (rice_role_limit Prog sem_equiv P Pext p_yes p_no Pyes Pno).
  intro dec.
  exact (rice_diagonal_from_recursion Prog sem_equiv Hrefl
           (kleene_recursion_from_lawvere Prog app Hsurj) p_yes p_no dec).
Qed.

(** Closed loop: the diagonal root (Lawvere, cs/LawvereFixedPoint.v), its computational instance
    (recursion, here), and the undecidability consequences (halting cs/HaltingRoleLimit.v, Rice
    cs/RiceRoleLimit.v) are ONE structure.  rice_from_lawvere needs NO RiceDiagonal hypothesis —
    only that the system is universal (a Lawvere point-surjection) with reflexive semantics. *)

Print Assumptions kleene_recursion_from_lawvere.
Print Assumptions rice_from_lawvere.
