(** * SphaleronRateDescent.v — Baryogenesis boundary, BRANCH 2/3 (SphaleronRate, the B-violation
      magnitude): walking the box CONSTRUCTIVELY exhibits the finitization boundary.  The rate ∝
      exp(−E_sph/T); the exponential is the CANONICAL NON-TERMINATING process: its partial sums are
      RATIONAL (Element approximations), they strictly increase, and they NEVER stabilize — so the limit
      e^x is a ROLE-LIMIT, never reached by any finite truncation.  Exactly like the surd-Pell convergents
      → √D and nine_raw → 1 (the flagship H1).

    BaryogenesisBoundary.v tagged SphaleronRate → RoleLimit.  Walking it:
      Rules (L5):  rate = exp(exponent); exp(x) = Σ x^k/k! — an INFINITE sum, a process that does NOT halt.
      Roles (L4):  the exponent E_sph/T is a RATIO (rational ⟹ Element); exp plays the role of the
                   non-terminating process; the partial sums exp_partial play the role of Element approximations.
      Elements:    the partial sums are RATIONAL (Element) — exp_partial(1) = {1, 2, 5/2, 8/3, …} → e; each
                   is finite and computable, but the process STRICTLY INCREASES and NEVER stabilizes.

    THE SPLIT: rate = {exponent (Element ratio) + exp (role-limit, non-terminating)}.  The partial sums are
    the Element-side (rational, derived); the limit e^x is the role-limit, never reached by a finite
    truncation — the canonical instance of H1 (Element = terminating, role-limit = non-terminating).

    HONEST: we show NON-TERMINATION (exp_partial_never_stabilizes), not transcendence of e (which is hard)
    — but non-termination IS the finitization-boundary criterion for a role-limit (H1).  The Element-side
    (partial sums, positivity, the ratio exponent) is derived; the magnitude (the limit) is the wall.

    Elements: factorial, qpow, exp_term, exp_partial (rational partial sums); concrete approximations of e
    Roles:    the partial sums = Element approximations; the limit = the role-limit (never reached)
    Rules:    the partial sums strictly increase and never stabilize ⟹ the process does not terminate

    ============ E/R/R разбор ============
      Rules (L5): скорость = exp(показатель); exp = Σ x^k/k! — бесконечная сумма, процесс не обрывается.
      Roles (L4): показатель E/T = отношение (рац ⟹ Element); exp = нетерминирующий процесс; частичные суммы = Element-приближения.
      Elements  : частичные суммы рациональны (Element): {1,2,5/2,8/3,…}→e; строго возрастают, не стабилизируются.
    ДИАГНОСТИКА (P4): ветка сходится в ЯДРО границы финитизации (role-limit = нетерминирующий процесс),
    конструктивно. Показываю НЕТЕРМИНАЦИЮ (не трансцендентность e) — а это и есть критерий role-limit H1.
    Element-сторона (суммы, положительность, показатель) выведена; магнитуда (предел) = стена. Параллель surd-Pell/nine_raw.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Arith Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Factorial, power, and the exponential partial sum (rational = Element)  *)
(* ===================================================================== *)

Fixpoint fact (n : nat) : nat := match n with O => 1%nat | S k => (n * fact k)%nat end.

Fixpoint qpow (x : Q) (n : nat) : Q := match n with O => 1 | S k => x * qpow x k end.

(** The k-th term x^k / k! — rational. *)
Definition exp_term (x : Q) (k : nat) : Q := qpow x k * (1 # Pos.of_nat (fact k)).

(** The partial sum Σ_{k=0}^n x^k/k! — RATIONAL (an Element approximation of e^x). *)
Fixpoint exp_partial (x : Q) (n : nat) : Q :=
  match n with O => exp_term x 0 | S k => exp_partial x k + exp_term x (S k) end.

(* ===================================================================== *)
(*  Positivity of the terms                                                *)
(* ===================================================================== *)

Lemma one_over_fact_pos : forall k, 0 < (1 # Pos.of_nat (fact k)).
Proof. intro k. unfold Qlt. simpl. lia. Qed.

Lemma qpow_pos : forall x k, 0 < x -> 0 < qpow x k.
Proof.
  intros x k Hx. induction k as [|m IH].
  - simpl. lra.
  - simpl. apply Qmult_lt_0_compat; [ exact Hx | exact IH ].
Qed.

Lemma exp_term_pos : forall x k, 0 < x -> 0 < exp_term x k.
Proof.
  intros x k Hx. unfold exp_term.
  apply Qmult_lt_0_compat; [ apply qpow_pos; exact Hx | apply one_over_fact_pos ].
Qed.

(* ===================================================================== *)
(*  The process strictly increases and NEVER stabilizes (role-limit)       *)
(* ===================================================================== *)

(** ★ For x > 0, the Element approximations STRICTLY INCREASE — each step adds a positive term. *)
Lemma exp_partial_increasing : forall x n, 0 < x -> exp_partial x n < exp_partial x (S n).
Proof.
  intros x n Hx. pose proof (exp_term_pos x (S n) Hx) as Ht.
  assert (Heq : exp_partial x (S n) = exp_partial x n + exp_term x (S n)) by reflexivity.
  rewrite Heq. lra.
Qed.

(** ★ The process NEVER stabilizes: no partial sum equals the next.  This is the finitization-boundary
    signature of a ROLE-LIMIT (non-termination) — the limit e^x is never reached by a finite truncation. *)
Lemma exp_partial_never_stabilizes : forall x n, 0 < x -> ~ exp_partial x n == exp_partial x (S n).
Proof.
  intros x n Hx Heq. pose proof (exp_partial_increasing x n Hx) as Hlt. lra.
Qed.

(* ===================================================================== *)
(*  Concrete rational (Element) approximations of e                        *)
(* ===================================================================== *)

Lemma exp_partial_e_0 : exp_partial 1 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_partial_e_1 : exp_partial 1 1 == 2.
Proof. vm_compute. reflexivity. Qed.

(** exp_partial 1 2 = 1 + 1 + 1/2 = 5/2 — a rational Element approximation of e ≈ 2.718. *)
Lemma exp_partial_e_2 : exp_partial 1 2 == 5 # 2.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: branch 2 — the rate's exp is a non-terminating process        *)
(* ===================================================================== *)

(** Branch 2 (SphaleronRate) walked, constructively:
      (increase)   for x > 0 the Element approximations exp_partial strictly increase;
      (never halt) no partial sum equals the next — the process NEVER stabilizes (role-limit signature);
      (Element)    the partial sums are RATIONAL: exp_partial(1) = 1, 2, 5/2, … (approximations of e).
    The rate splits {exponent (Element ratio) + exp (role-limit, non-terminating)}.  The partial sums are
    the derived Element-side; the limit e^x is the wall, never reached — the canonical instance of the
    finitization boundary (H1), exactly like the surd-Pell convergents and nine_raw. *)
Theorem sphaleron_rate_descent :
  (forall x n, 0 < x -> exp_partial x n < exp_partial x (S n))
  /\ (forall x n, 0 < x -> ~ exp_partial x n == exp_partial x (S n))
  /\ exp_partial 1 0 == 1
  /\ exp_partial 1 1 == 2
  /\ exp_partial 1 2 == 5 # 2.
Proof.
  split; [ exact exp_partial_increasing | ].
  split; [ exact exp_partial_never_stabilizes | ].
  split; [ exact exp_partial_e_0 | ].
  split; [ exact exp_partial_e_1 | ].
  exact exp_partial_e_2.
Qed.
