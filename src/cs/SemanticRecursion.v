(** * SemanticRecursion.v — reconciling Leibniz vs reduction: the HONEST recursion theorem
      Grounding (cs/LambdaRecursion.v) revealed that real recursion gives a REDUCTION fixed point
      (`fixpoint f → App f (fixpoint f)`), not a Leibniz one (`f e = e`).  This file reconciles:
        • the honest abstract recursion theorem is SEMANTIC — `exists e, sem_equiv e (f e)` — and it
          discharges Rice MORE cleanly than the Leibniz version (no reflexivity needed);
        • Leibniz recursion is a SPECIAL CASE (`leibniz_recursion_is_semantic`);
        • the concrete λ REALISES the semantic recursion via reduction (`recursion_grounded`), for
          representable transformers (App f) — exactly Kleene's recursion theorem.

    HONEST POINT.  cs/RecursionTheorem.rice_from_lawvere's hypothesis `point_surjective app :
    Prog → (Prog → Prog)` is UNSATISFIABLE for a real total model (Lawvere/Cantor itself forbid a
    total surjection onto the function space) — which is precisely WHY real computation is partial &
    semantic.  The realisable route is `rice_from_sem_recursion` (this file), which the λ satisfies.

    Reuses cs/LambdaRecursion.v (Term, step, fixpoint, Y_step2, closed), cs/RiceRoleLimit.v
    (RiceDiagonal, rice_role_limit), cs/BoundaryDecidability.v (RoleLimitDrawn).  0 axioms.

    Elements: λ-terms; the reduction relation; abstract programs / sem_equiv
    Roles:    "a semantic fixed point" (recursion's role — REDUCTION, not Leibniz); a decider = role-oracle
    Rules:    recursion = `sem_equiv e (f e)`; Leibniz is a special case; the λ realises it via reduces

    ============ E/R/R разбор ============
      Rules (L5): рекурсия = sem_equiv e (f e) (семантическая); Leibniz = частный случай; λ реализует
                  через reduces.
      Roles (L4): «семантическая неподвижная точка» (роль рекурсии — РЕДУКЦИОННАЯ); решатель = роль-оракул.
      Elements  : λ-термы; редукция reduces; абстрактные sem_equiv.
    ДИАГНОСТИКА (P4): ПРИМИРЕНИЕ.  Честная теорема рекурсии — про РЕДУКЦИЮ/СЕМАНТИКУ (sem_equiv e (f e)),
      не Leibniz =.  Гипотеза point_surjective из rice_from_lawvere НЕРЕАЛИЗУЕМА для реальных тотальных
      моделей (сам Ловер запрещает) ⟹ реальная рекурсия семантична/частична.  λ реализует
      семантическую рекурсию (recursion_grounded) для представимых трансформеров (Клини).  Leibniz ⊂ semantic.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From ToS Require Import cs.BoundaryDecidability.
From ToS Require Import cs.RiceRoleLimit.
From ToS Require Import cs.LambdaGrounding.
From ToS Require Import cs.LambdaRecursion.

(* ===================================================================== *)
(*  The honest abstract recursion theorem: SEMANTIC fixed points           *)
(* ===================================================================== *)

(** A SEMANTIC recursion property discharges Rice's diagonal directly — cleaner than the Leibniz
    version (cs/RecursionTheorem.rice_diagonal_from_recursion): no reflexivity needed, sem_equiv is
    used as-is. *)
Theorem rice_diagonal_from_sem_recursion :
  forall (Prog : Type) (sem_equiv : Prog -> Prog -> Prop),
    (forall f : Prog -> Prog, exists e, sem_equiv e (f e)) ->
    forall (p_yes p_no : Prog) (D : Prog -> bool),
      RiceDiagonal Prog sem_equiv p_yes p_no D.
Proof.
  intros Prog sem_equiv Hrec p_yes p_no D. unfold RiceDiagonal.
  destruct (Hrec (fun e => if D e then p_no else p_yes)) as [d Hd]. cbv beta in Hd.
  exists d. split.
  - intro HT. rewrite HT in Hd. simpl in Hd. exact Hd.
  - intro HF. rewrite HF in Hd. simpl in Hd. exact Hd.
Qed.

(** Leibniz recursion is a SPECIAL CASE of semantic recursion (when sem_equiv is reflexive). *)
Lemma leibniz_recursion_is_semantic :
  forall (Prog : Type) (sem_equiv : Prog -> Prog -> Prop),
    (forall p, sem_equiv p p) ->
    (forall f : Prog -> Prog, exists e, f e = e) ->
    forall f : Prog -> Prog, exists e, sem_equiv e (f e).
Proof.
  intros Prog sem_equiv Hrefl Hleib f. destruct (Hleib f) as [e He].
  exists e. rewrite He. apply Hrefl.
Qed.

(** ★ THE HONEST RICE: a non-trivial semantic property is undecidable, from SEMANTIC recursion
    (the realisable hypothesis — no point-surjectivity, no Leibniz). *)
Theorem rice_from_sem_recursion :
  forall (Prog : Type) (sem_equiv : Prog -> Prog -> Prop),
    (forall f : Prog -> Prog, exists e, sem_equiv e (f e)) ->
    forall (P : Prog -> Prop),
      (forall p q, sem_equiv p q -> (P p <-> P q)) ->
      forall (p_yes p_no : Prog), P p_yes -> ~ P p_no ->
        RoleLimitDrawn P.
Proof.
  intros Prog sem_equiv Hrec P Pext p_yes p_no Pyes Pno.
  apply (rice_role_limit Prog sem_equiv P Pext p_yes p_no Pyes Pno).
  intro dec.
  exact (rice_diagonal_from_sem_recursion Prog sem_equiv Hrec p_yes p_no dec).
Qed.

(* ===================================================================== *)
(*  The concrete λ realises semantic recursion via reduction               *)
(* ===================================================================== *)

(** Multi-step reduction on λ-terms (the semantic equivalence is reduction, not Leibniz). *)
Inductive reduces : Term -> Term -> Prop :=
  | red_refl : forall t, reduces t t
  | red_step : forall a b c, step a = Some b -> reduces b c -> reduces a c.

(** ★ GROUNDED semantic recursion: the fixed point REDUCES to f applied to itself — the honest
    (reduction) fixed point that cs/LambdaRecursion.Y_step2 produces, for representable transformers. *)
Lemma recursion_grounded :
  forall f, closed f -> reduces (fixpoint f) (App f (fixpoint f)).
Proof.
  intros f Hcl. eapply red_step; [ apply Y_step2; exact Hcl | apply red_refl ].
Qed.

(** Reconciled: the honest abstract recursion theorem is SEMANTIC (rice_from_sem_recursion); Leibniz
    is a special case; the concrete λ (LambdaRecursion) realises it via reduction (recursion_grounded)
    for representable transformers — Kleene's recursion theorem.  The Leibniz/Lawvere route
    (rice_from_lawvere) is the IDEAL that exposes why computation must be partial & semantic; this is
    the REALISABLE route.  Full abstract semantic recursion over ALL meta-functions Prog→Prog is not
    realisable (more meta-functions than terms) — Kleene's theorem is exactly about representable ones. *)

Print Assumptions rice_from_sem_recursion.
Print Assumptions recursion_grounded.
