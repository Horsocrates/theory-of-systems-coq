(** * LambdaGrounding.v — grounding computation-as-process in a real self-applicable λ-machine
      Discharges the abstractness of Phase 0 (cs/HaltingRoleLimit.v's Config/step/halted) by
      INSTANTIATING it with a concrete untyped de Bruijn λ-calculus — and exhibits BOTH sides of the
      Element/role-limit boundary as REAL programs:
        role-limit: Ω = (λx.xx)(λx.xx) steps into ITSELF (step Ω = Some Ω) ⟹ `diverges Ω` is PROVED
                    — a genuinely non-halting program, machine-verified;
        Element:    the identity-applied-to-identity term reaches a normal form ⟹ `halts` is proved;
                    and bounded halting (within n steps) is DECIDABLE here (computable via run).

    Why a self-contained λ (not the repo's src/Expressions.v / src/Reduction.v): the repo's `Expr`
    carries `Level` (ESystem : Level -> Expr), so importing it pulls the Core_ERR → ToS_Axioms →
    Distinction .vo chain (stale-.vo risk through OneDrive).  This minimal untyped λ MIRRORS that
    `Expr`/`try_step` (call-by-name weak-head reduction) self-contained.  Instantiating on the repo's
    typed `Expr`, and discharging SelfProgrammable/recursion via a Y-combinator, are the next steps.

    Reuses cs/HaltingRoleLimit.v (run, halts, diverges, run_S, bounded_halting_decidable).

    Elements: λ-terms (de Bruijn Term); the concrete Ω and the identity term
    Roles:    "normal form" (haltedT) = a term's status; Ω = a role-limit witness (a real
              non-terminating program); the identity term = an Element witness
    Rules:    β-reduction (step); self-application ω = λx.xx

    ============ E/R/R разбор ============
      Rules (L5): β-редукция (step); само-применение ω=λx.xx — предпосылка диагонали.
      Roles (L4): «нормальная форма» (haltedT) = статус терма; Ω = свидетель role-limit; identity-
                  терм = свидетель Element.
      Elements  : λ-термы (Term); конкретные Ω и identity-терм.
    ДИАГНОСТИКА (P4): заземление модели вычисления в РЕАЛЬНОЙ само-применимой λ-машине (зеркало repo
      Expressions/Reduction, реплицировано чтобы обойти .vo-цепь через Core_ERR).  Ω=(λx.xx)(λx.xx)
      ШАГАЕТ В СЕБЯ ⟹ diverges Ω доказано — role-limit реализован настоящей программой, машинно.
      Identity-терм останавливается — Element.  Ограниченная остановка разрешима (вычислимо).  Полная
      разрядка SelfProgrammable/рекурсии (Y) и инстанциация на typed Expr — следующий шаг.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat.
From ToS Require Import cs.HaltingRoleLimit.

(* ===================================================================== *)
(*  A minimal untyped de Bruijn λ-calculus (mirrors src/Expressions.v)     *)
(* ===================================================================== *)

Inductive Term : Type :=
  | Var : nat -> Term
  | Lam : Term -> Term
  | App : Term -> Term -> Term.

Fixpoint lift (c : nat) (t : Term) : Term :=
  match t with
  | Var n   => if Nat.ltb n c then Var n else Var (S n)
  | Lam b   => Lam (lift (S c) b)
  | App a b => App (lift c a) (lift c b)
  end.

Fixpoint subst (j : nat) (s : Term) (t : Term) : Term :=
  match t with
  | Var n   => if Nat.eqb n j then s else Var n
  | Lam b   => Lam (subst (S j) (lift 0 s) b)
  | App a b => App (subst j s a) (subst j s b)
  end.

(** Call-by-name weak-head β-reduction (one step), computable. *)
Fixpoint step (t : Term) : option Term :=
  match t with
  | App (Lam b) a => Some (subst 0 a b)
  | App f a       => match step f with
                     | Some f' => Some (App f' a)
                     | None    => None
                     end
  | Var _ => None
  | Lam _ => None
  end.

(** Total step (stuck = self) and the halted (normal-form) predicate, matching HaltingRoleLimit. *)
Definition stepT (t : Term) : Term := match step t with Some t' => t' | None => t end.
Definition haltedT (t : Term) : bool := match step t with Some _ => false | None => true end.

(* ===================================================================== *)
(*  role-limit side: Ω is a REAL non-halting program                       *)
(* ===================================================================== *)

Definition omega : Term := Lam (App (Var 0) (Var 0)).      (* λx. x x *)
Definition Omega : Term := App omega omega.                (* (λx.xx)(λx.xx) *)

(** Ω β-reduces to ITSELF — the canonical loop. *)
Lemma step_Omega : step Omega = Some Omega.
Proof. vm_compute. reflexivity. Qed.

Lemma haltedT_Omega : haltedT Omega = false.
Proof. vm_compute. reflexivity. Qed.

Lemma stepT_Omega : stepT Omega = Omega.
Proof. vm_compute. reflexivity. Qed.

(** Running Ω never changes it. *)
Lemma run_Omega : forall n, run Term stepT haltedT n Omega = Omega.
Proof.
  induction n.
  - reflexivity.
  - rewrite run_S, IHn, haltedT_Omega. exact stepT_Omega.
Qed.

(** ★ Ω DIVERGES — a genuinely non-halting program, machine-verified (role-limit grounded). *)
Lemma diverges_Omega : diverges Term stepT haltedT Omega.
Proof. intro n. rewrite run_Omega. exact haltedT_Omega. Qed.

(* ===================================================================== *)
(*  Element side: a halting program + decidable bounded halting            *)
(* ===================================================================== *)

Definition id_term : Term := Lam (Var 0).                  (* λx. x *)
Definition halt_term : Term := App id_term id_term.        (* (λx.x)(λx.x) → λx.x *)

(** ★ A real program that HALTS (reaches a normal form) — Element grounded. *)
Lemma halt_term_halts : halts Term stepT haltedT halt_term.
Proof. exists 3. vm_compute. reflexivity. Qed.

(** Element floor: halting WITHIN n steps is decidable for real λ-terms (computable via run). *)
Lemma halting_within_decidable :
  forall n t, {halts_in Term stepT haltedT n t} + {~ halts_in Term stepT haltedT n t}.
Proof. exact (bounded_halting_decidable Term stepT haltedT). Qed.

(** Grounded: Phase 0's computation-as-process is realised by a concrete self-applicable λ-machine.
    Ω (a real loop) is the role-limit side; the identity term is the Element side; bounded halting is
    decidable.  The language is self-applicable (ω applies its argument to itself — the precondition
    for the halting diagonal); discharging SelfProgrammable/recursion via a Y-combinator, and
    instantiating on the repo's typed Expr, are the next grounding steps. *)

Print Assumptions diverges_Omega.
Print Assumptions halt_term_halts.
