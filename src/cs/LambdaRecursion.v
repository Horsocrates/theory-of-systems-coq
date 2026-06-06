(** * LambdaRecursion.v — the Y-combinator: grounding Kleene's recursion theorem in the λ-machine
      Deeper grounding: discharges the abstractness of cs/RecursionTheorem.v IN the concrete
      self-applicable λ of cs/LambdaGrounding.v.  For any CLOSED program f, the fixed point
      `fixpoint f` steps in ONE β-step to `App f (fixpoint f)` — self-reference realised by a real
      program, machine-verified.  This is Kleene's (second) recursion theorem made concrete.

    Needs a correct treatment of de Bruijn scope: `wf k t` (free vars < k), with the standard
    `lift`/`subst` are identities on closed terms (lift_closed/subst_closed) — exactly what makes the
    Curry Y-combinator unfold to a fixed point.

    Reuses cs/LambdaGrounding.v (Term, lift, subst, step).  Honest level: the Y-combinator and its
    fixed-point property are classical; the contribution is grounding the abstract recursion theorem
    in this concrete λ (synthesis).  0 axioms.  (Full tie to the repo's typed Expr = next step.)

    Elements: λ-terms; the Curry combinator Yc; the fixed point `fixpoint f`
    Roles:    `fixpoint f` = a self-describing program (recursion's goal-role); closedness = a
              well-scoping condition-role
    Rules:    β + self-application; subst/lift are identities on closed terms

    ============ E/R/R разбор ============
      Rules (L5): β + само-применение; subst/lift тождественны на замкнутых термах.
      Roles (L4): fixpoint f = само-описывающая программа (роль-цель рекурсии); замкнутость = роль-условие.
      Elements  : λ-термы; Y-комбинатор Yc; неподвижная точка fixpoint f.
    ДИАГНОСТИКА (P4): заземляет АБСТРАКТНУЮ теорему рекурсии (RecursionTheorem.v) в КОНКРЕТНОЙ λ: для
      всякого замкнутого f, step (fixpoint f) = Some (App f (fixpoint f)) — само-ссылка реализована
      настоящей программой, машинно.  Разряжает абстрактную гипотезу point_surjective/recursion на
      уровне модели.  Полная связь с typed Expr репо — следующий шаг.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Lia.
From ToS Require Import cs.LambdaGrounding.

(* ===================================================================== *)
(*  Scope: wf k t = all free variables of t are < k                       *)
(* ===================================================================== *)

Fixpoint wf (k : nat) (t : Term) : Prop :=
  match t with
  | Var n   => n < k
  | Lam b   => wf (S k) b
  | App a b => wf k a /\ wf k b
  end.

Definition closed (t : Term) : Prop := wf 0 t.

Lemma wf_mono : forall t k k', wf k t -> k <= k' -> wf k' t.
Proof.
  intros t. induction t as [n | b IHb | a IHa b IHb]; intros k k' H Hle; simpl in *.
  - lia.
  - apply (IHb (S k) (S k') H). lia.
  - destruct H as [H1 H2]. split; [exact (IHa k k' H1 Hle) | exact (IHb k k' H2 Hle)].
Qed.

Lemma lift_wf : forall t c, wf c t -> lift c t = t.
Proof.
  intros t. induction t as [n | b IHb | a IHa b IHb]; intros c H; simpl in *.
  - destruct (Nat.ltb_spec n c); [reflexivity | lia].
  - f_equal. apply IHb. exact H.
  - destruct H as [H1 H2]. f_equal; [apply IHa | apply IHb]; assumption.
Qed.

Lemma subst_wf : forall t j s, wf j t -> subst j s t = t.
Proof.
  intros t. induction t as [n | b IHb | a IHa b IHb]; intros j s H; simpl in *.
  - destruct (Nat.eqb_spec n j); [lia | reflexivity].
  - f_equal. apply IHb. exact H.
  - destruct H as [H1 H2]. f_equal; [apply IHa | apply IHb]; assumption.
Qed.

Lemma lift_closed : forall f, closed f -> lift 0 f = f.
Proof. intros f H. apply (lift_wf f 0). exact H. Qed.

Lemma subst_closed : forall f j s, closed f -> subst j s f = f.
Proof. intros f j s H. apply (subst_wf f j s). apply (wf_mono f 0 j H). lia. Qed.

(* ===================================================================== *)
(*  The Curry Y-combinator and the fixed-point property                    *)
(* ===================================================================== *)

Definition Wf (f : Term) : Term := Lam (App (lift 0 f) (App (Var 0) (Var 0))).  (* λx. f (x x) *)
Definition fixpoint (f : Term) : Term := App (Wf f) (Wf f).

(** ★ THE RECURSION THEOREM, GROUNDED: for any closed f, the fixed point steps to f applied to
    itself — a self-referential program, machine-verified. *)
Lemma Y_step2 : forall f, closed f ->
  step (fixpoint f) = Some (App f (fixpoint f)).
Proof.
  intros f Hcl. unfold fixpoint. unfold Wf at 1. cbn [step]. cbn [subst].
  rewrite (lift_closed f Hcl).
  rewrite (subst_closed f 0 (Wf f) Hcl).
  reflexivity.
Qed.

(** Curry's Y-combinator builds the fixed point: App Yc f β-steps to `fixpoint f`. *)
Definition Yc : Term :=
  Lam (App (Lam (App (Var 1) (App (Var 0) (Var 0))))
           (Lam (App (Var 1) (App (Var 0) (Var 0))))).

Lemma Y_step1 : forall f, step (App Yc f) = Some (fixpoint f).
Proof. intro f. unfold Yc, fixpoint, Wf. cbn [step subst]. reflexivity. Qed.

(** Grounded: the abstract recursion theorem (cs/RecursionTheorem.kleene_recursion_from_lawvere) is
    realised by a concrete Y-combinator in a real self-applicable λ — `fixpoint f` is a genuine
    self-describing program (step (fixpoint f) = Some (App f (fixpoint f))).  Together with
    cs/LambdaGrounding.v (Ω diverges, identity halts), Phase 0's machine, its halting boundary, AND
    the recursion theorem behind Rice are now grounded in real programs.  Full tie to the repo's
    typed Expr is the next step. *)

Print Assumptions Y_step2.
Print Assumptions Y_step1.
