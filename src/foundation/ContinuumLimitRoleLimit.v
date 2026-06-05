(** * ContinuumLimitRoleLimit.v — the IMPORTANT half of Q1: the continuum limit of a ROLE-LIMIT target.
      ContinuumLimitProcess.v converged to a RATIONAL length (the warm-up, where the floor is exact and the
      limit is sometimes reached at finite density).  Here the target is IRRATIONAL — the length sqrt2 — a
      role-limit the process NEVER reaches.  The rational Pell convergents r_n = x_n/y_n approach sqrt2 with
      an explicit rate, and the NON-TERMINATION INVARIANT x_n^2 - 2 y_n^2 = +-1 (never 0) is EXACTLY why
      sqrt2 is role-limit — the same surd engine as H1-H14, now as the cause of the limit's non-termination.

    -- The construction --
      Pell recurrence for sqrt2: (x,y) |-> (x + 2y, x + y), seed (1,1).  Convergents 1/1, 3/2, 7/5, 17/12,
      41/29, ...  The Pell form pell_val n = x_n^2 - 2 y_n^2 satisfies pell_val 0 = -1 and
      pell_val (S n) = - pell_val n, hence pell_val n in {+1, -1} for all n — NEVER 0.  Therefore:
        - sqrt2 is NEVER reached:   x_n^2 <> 2 y_n^2  (no convergent squares to 2);
        - the error has constant numerator:  (r_n^2 - 2) * y_n^2 = pell_val n = +-1;
        - the denominator y_n grows without bound (y_n >= n+1), so the error r_n^2 - 2 = +-1/y_n^2 -> 0.
      The convergents are rational (Element) at every step; sqrt2 is the role-limit they approach but never
      touch; the invariant +-1 is the controlled, never-vanishing error numerator.

    -- The tie to the atlas --
      The very invariant x^2 - 2 y^2 = +-1 that makes sqrt2 a role-limit (sqrt2 irrational, H1) is here the
      CAUSE of the limit's non-termination.  Q1's continuum-limit-as-process closes the loop with the
      surd/Pell engine: the continuum length is a process; its non-reachability is the Pell invariant.

    -- HONEST scope --
      One concrete role-limit target (sqrt2) via its Pell process.  The general theorem "every irrational
      length is approached this way" is the uniform statement (the mechanism is universal — Pell for any
      non-square D, PellDichotomy.v) but is not proved here.  The 3+1D uniqueness (Hauptvermutung) is Q3.

    Elements: Pell recurrence (x,y)->(x+2y,x+y); pell_val n in {+1,-1}; x_n^2 <> 2 y_n^2; y_n >= n+1
    Roles:    convergents r_n = Element; sqrt2 = role-limit (unreached); invariant +-1 = error numerator
    Rules:    sqrt2 approached by a rational process, never reached (invariant <> 0), error +-1/y_n^2 -> 0

    ============ E/R/R разбор ============
      Rules (L5): предел role-limit-цели: длина sqrt2 приближается Pell-процессом r_n=x_n/y_n; инвариант
                  x^2-2y^2=+-1 (рекуррентно негируется, <> 0) => sqrt2 не достигается; ошибка +-1/y^2 -> 0.
      Roles (L4): конвергенты r_n = Element; sqrt2 = role-limit (недостижимый); инвариант +-1 = числитель
                  ошибки (тот же сурд-движок H1); y_n^2 = знаменатель скорости (-> infinity).
      Elements  : (x,y)->(x+2y,x+y); pell_val 0=-1, pell_val(S n)=-pell_val n => {+1,-1}; x^2<>2y^2; y>=n+1.
    ДИАГНОСТИКА (P4): важная половина Q1 -- предел role-limit-цели.  Машинно: sqrt2 НИКОГДА не достигается
    (инвариант <> 0, чистый Z), ошибка = +-1/y^2 -> 0 (числитель константа +-1, знаменатель -> infinity).
    ТОТ ЖЕ инвариант x^2-2y^2=+-1, что делает sqrt2 role-limit (H1), здесь = причина незавершаемости предела.
    Q1 смыкается с сурд-движком.  ЧЕСТНО: один инстанс (sqrt2); общая теорема = обобщение (Pell для любого
    non-square D); 3+1D единственность = Q3.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The Pell process for sqrt2                                             *)
(* ===================================================================== *)

(** Pell recurrence (x,y) |-> (x + 2y, x + y), seed (1,1): the convergents of sqrt2. *)
Fixpoint pell (n : nat) : Z * Z :=
  match n with
  | O => (1, 1)
  | S m => let (x, y) := pell m in (x + 2 * y, x + y)
  end.

Definition px (n : nat) : Z := fst (pell n).
Definition py (n : nat) : Z := snd (pell n).

Lemma pell_S : forall n, pell (S n) = (px n + 2 * py n, px n + py n).
Proof. intro n. unfold px, py. simpl. destruct (pell n) as [x y]. reflexivity. Qed.

Lemma px_succ : forall n, px (S n) = px n + 2 * py n.
Proof. intro n. unfold px at 1. rewrite pell_S. reflexivity. Qed.

Lemma py_succ : forall n, py (S n) = px n + py n.
Proof. intro n. unfold py at 1. rewrite pell_S. reflexivity. Qed.

Lemma pell_1 : pell 1 = (3, 2).
Proof. reflexivity. Qed.

Lemma pell_3 : pell 3 = (17, 12).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The non-termination invariant: the Pell form is always +-1            *)
(* ===================================================================== *)

Definition pell_val (n : nat) : Z := px n * px n - 2 * (py n * py n).

Lemma pell_val_0 : pell_val 0 = -1.
Proof. reflexivity. Qed.

(** The recurrence NEGATES the Pell form at every step. *)
Lemma pell_val_neg : forall n, pell_val (S n) = - pell_val n.
Proof. intro n. unfold pell_val. rewrite px_succ, py_succ. ring. Qed.

(** Hence the Pell form is +1 or -1 for every n. *)
Lemma pell_val_pm : forall n, pell_val n = 1 \/ pell_val n = -1.
Proof.
  induction n.
  - right. reflexivity.
  - rewrite pell_val_neg. destruct IHn as [H | H]; rewrite H; [ right | left ]; reflexivity.
Qed.

(** ...and never 0 — the non-termination invariant. *)
Lemma pell_val_nonzero : forall n, pell_val n <> 0.
Proof. intro n. destruct (pell_val_pm n) as [H | H]; rewrite H; discriminate. Qed.

(** The squared error numerator is the constant 1 (|pell_val n| = 1). *)
Lemma pell_val_sq : forall n, pell_val n * pell_val n = 1.
Proof. intro n. destruct (pell_val_pm n) as [H | H]; rewrite H; reflexivity. Qed.

(** ★ ROLE-LIMIT: no Pell convergent squares to 2 — sqrt2 is NEVER reached (it is irrational). *)
Lemma sqrt2_never_reached : forall n, px n * px n <> 2 * (py n * py n).
Proof. intro n. assert (H := pell_val_nonzero n). unfold pell_val in H. lia. Qed.

(* ===================================================================== *)
(*  Growth: the denominator goes to infinity (so the error -> 0)           *)
(* ===================================================================== *)

Lemma pxy_pos : forall n, px n >= 1 /\ py n >= 1.
Proof.
  induction n.
  - unfold px, py. simpl. split; lia.
  - destruct IHn as [Hx Hy]. rewrite px_succ, py_succ. split; lia.
Qed.

(** y_n >= n+1, so the denominator grows without bound. *)
Lemma py_ge : forall n, py n >= Z.of_nat (S n).
Proof.
  induction n.
  - unfold py. simpl. lia.
  - rewrite py_succ. destruct (pxy_pos n) as [Hx _]. lia.
Qed.

(* ===================================================================== *)
(*  The rational convergent and the explicit error rate                    *)
(* ===================================================================== *)

Definition r (n : nat) : Q := (inject_Z (px n) / inject_Z (py n))%Q.

Lemma py_inject_ne : forall n, ~ (inject_Z (py n) == 0)%Q.
Proof.
  intros n Hc. destruct (pxy_pos n) as [_ Hy].
  apply (proj1 (inject_Z_injective (py n) 0)) in Hc. lia.
Qed.

(** ★ The explicit error identity: (r_n^2 - 2) * y_n^2 = pell_val n = +-1.  So the error is +-1/y_n^2,
    a definite rational with constant numerator +-1 and denominator y_n^2 -> infinity. *)
Lemma r_sq_close : forall n,
  ((r n * r n - 2) * (inject_Z (py n) * inject_Z (py n)) == inject_Z (pell_val n))%Q.
Proof.
  intro n. assert (Hne := py_inject_ne n). unfold pell_val.
  assert (Hh : (inject_Z (px n * px n - 2 * (py n * py n))
            == inject_Z (px n) * inject_Z (px n) - 2 * (inject_Z (py n) * inject_Z (py n)))%Q).
  { replace (px n * px n - 2 * (py n * py n))%Z
       with (px n * px n + - (2 * (py n * py n)))%Z by ring.
    rewrite inject_Z_plus, inject_Z_opp, !inject_Z_mult.
    change (inject_Z 2) with (2 # 1)%Q. ring. }
  rewrite Hh. unfold r. field. exact Hne.
Qed.

(** ★ The rational length never squares to 2 (role-limit at the Q level), from the invariant <> 0. *)
Lemma r_sq_ne_2 : forall n, ~ (r n * r n == 2)%Q.
Proof.
  intros n H.
  assert (H0 : ((r n * r n - 2) * (inject_Z (py n) * inject_Z (py n)) == 0)%Q)
    by (rewrite H; ring).
  rewrite r_sq_close in H0.
  apply (pell_val_nonzero n).
  apply (proj1 (inject_Z_injective (pell_val n) 0)).
  rewrite H0. reflexivity.
Qed.

(* ===================================================================== *)
(*  Capstone: the continuum limit of a role-limit target                   *)
(* ===================================================================== *)

(** The continuum limit of a ROLE-LIMIT target (sqrt2), constructive:
      (never)   no convergent squares to 2 — sqrt2 is never reached (x_n^2 <> 2 y_n^2);
      (numer)   the error numerator is the constant +-1 (pell_val n ^2 = 1);
      (denom)   the denominator y_n grows without bound (y_n >= n+1);
      (rate)    so (r_n^2 - 2) * y_n^2 = +-1, i.e. the error is +-1/y_n^2 -> 0;
      (Q-never) the rational length never squares to 2.
    The continuum length sqrt2 is the limit of a rational (Element) process with an explicit rate, NEVER
    reached — and the non-termination is exactly the Pell invariant x^2 - 2 y^2 = +-1 of the surd engine. *)
Theorem continuum_limit_role_limit :
  (forall n, px n * px n <> 2 * (py n * py n))
  /\ (forall n, pell_val n * pell_val n = 1)
  /\ (forall n, py n >= Z.of_nat (S n))
  /\ (forall n, ((r n * r n - 2) * (inject_Z (py n) * inject_Z (py n)) == inject_Z (pell_val n))%Q)
  /\ (forall n, ~ (r n * r n == 2)%Q).
Proof.
  split; [ exact sqrt2_never_reached | ].
  split; [ exact pell_val_sq | ].
  split; [ exact py_ge | ].
  split; [ exact r_sq_close | exact r_sq_ne_2 ].
Qed.
