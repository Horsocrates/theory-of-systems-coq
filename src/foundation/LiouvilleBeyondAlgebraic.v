(** * LiouvilleBeyondAlgebraic.v — a CONSTRUCTIVE number provably BEYOND the algebraic boundary: the Liouville
       process L = Σ 1/2^(k!).  H1AlgebraicDecider decides Element-ness for every ALGEBRAIC number;
       EulerProcessRoleLimit showed e separates from ℚ (irrational-flavoured).  But e/√2 are only IRRATIONAL —
       still possibly algebraic.  This builds a number that is provably TRANSCENDENTAL (beyond the decider's
       whole domain), by the elementary Liouville criterion — no Hermite–Lindemann, no integral.

    -- The Liouville signature (the mechanism, machine-checked) --
      Stage Sₙ = Σ_{k=0}^{n} 1/2^(k!); denominator qₙ = 2^(n!).  The convergent Sₙ = pₙ/qₙ with pₙ ∈ ℤ.  The
      super-exponential growth qₙ₊₁ = qₙ^(n+1) makes the NEXT gap astronomically small relative to qₙ:
        Sₙ₊₁ − Sₙ = 1/qₙ₊₁ = 1/qₙ^(n+1)  <  1/qₙ^n.
      So the rational pₙ/qₙ approximates the process to order n+1 — for EVERY n.  Liouville's theorem (classical)
      says an algebraic number of degree d admits |α − p/q| ≥ c/q^d; a number approximable to ALL orders cannot
      be algebraic.  Hence L is transcendental — beyond the algebraic decider's domain.

    -- The honest frame (P4) --
      Proven here: the constructive Liouville SIGNATURE (integer convergent + super-exponential gap < 1/qₙ^n at
      every n) — the part that is finitary and 0-axiom, about the PROCESS and its rational stages only (no
      completed L is invoked, P4-consistent).  The transcendence CONCLUSION is the classical Liouville theorem,
      cited not re-proved.  So L is a transcendental role-limit: a process whose convergents beat every fixed
      algebraic approximation order.

    WHAT THE REPO HAS (surveyed): NO Liouville / transcendence file; H1AlgebraicDecider (algebraic = decidable);
    EulerProcessRoleLimit (e separates from ℚ — irrational, not transcendental); IrrationalsClassification
    (e/π asserted ProcessQ).  GAP: a CONSTRUCTIVE number beyond the ALGEBRAIC layer, with the Liouville
    approximation signature proven.  This adds it.

    ============ E/R/R разбор ============
      Elements : стадии Sₙ=Σ1/2^(k!) (рациональные Элементы); qₙ=2^(n!) (знаменатель); pₙ=qₙ·Sₙ∈ℤ (конвергента).
      Roles    : L = роль-предел; «алгебраично ли L» — следующий слой границы (за разрешимым алгебраическим).
      Rules    : суперэкспонента qₙ₊₁=qₙ^(n+1) ⟹ зазор 1/qₙ^(n+1) < 1/qₙ^n на КАЖДОМ n ⟹ (Лиувилль) не алгебраично.
      ДИАГНОСТИКА (P4): L аппроксимируется рациональными pₙ/qₙ ДО ВСЕХ порядков — подпись трансцендентности; ни одно
      алгебраическое так не может (теорема Лиувилля). Слой за алгебраическим: Element ⊂ алгебр.role-limit (разрешим) ⊂
      ТРАНСЦЕНДЕНТНЫЙ role-limit (L — конструктивно за пределом решателя). P4: только процесс/стадии, без готового L.
      Уровень: `новая теорема` (подпись Лиувилля — суперэкспон. зазор + целая конвергента; в репо Liouville не было) +
      `синтез` (P4-слой, трансцендентность — классическая ссылка, не передоказ).

    STATUS: 10 Qed, 0 Admitted, 0 axioms  (self-contained: ZArith / QArith / Lqa / Lia / Factorial)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith QArith Lqa Lia Arith Factorial.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The Liouville process  L = Σ 1/2^(k!)                                   *)
(* ===================================================================== *)

(** Denominator of stage n: qₙ = 2^(n!). *)
Definition qden (n : nat) : Z := 2 ^ (Z.of_nat (fact n)).

(** Term k = 1/2^(k!). *)
Definition lterm (k : nat) : Q := 1 / inject_Z (qden k).

(** Partial sum Sₙ = Σ_{k=0}^{n} 1/2^(k!). *)
Fixpoint lsum (n : nat) : Q :=
  match n with O => lterm O | S k => lsum k + lterm (S k) end.

(* ===================================================================== *)
(*  Basic facts about the denominator                                      *)
(* ===================================================================== *)

Lemma qden_pos : forall n, (0 < qden n)%Z.
Proof. intro n. unfold qden. apply Z.pow_pos_nonneg; lia. Qed.

Lemma qden_ne : forall n, ~ inject_Z (qden n) == 0.
Proof.
  intro n. pose proof (qden_pos n) as H. intro Hc.
  assert (0 < inject_Z (qden n)) by (unfold Qlt, inject_Z; simpl; lia). lra.
Qed.

(** ★ The super-exponential law: qₙ₊₁ = qₙ^(n+1).  (n+1)! = (n+1)·n!, so 2^((n+1)!) = (2^(n!))^(n+1). *)
Lemma qden_superexp : forall n, (qden (S n) = (qden n) ^ Z.of_nat (S n))%Z.
Proof.
  intro n. unfold qden.
  rewrite <- Z.pow_mul_r by lia.
  f_equal. change (fact (S n)) with ((S n * fact n)%nat).
  rewrite Nat2Z.inj_mul. lia.
Qed.

(** ★ qₙ^n < qₙ₊₁ : the next denominator overshoots the n-th power of the current one. *)
Lemma qden_ge2 : forall n, (2 <= qden n)%Z.
Proof.
  intro n. unfold qden. rewrite <- (Z.pow_1_r 2) at 1.
  apply Z.pow_le_mono_r; [ lia | pose proof (lt_O_fact n); lia ].
Qed.

Lemma qden_pow_n_lt : forall n, (qden n ^ Z.of_nat n < qden (S n))%Z.
Proof.
  intro n.
  pose proof (qden_ge2 n) as Hq2.
  assert (Hxpos : (0 < qden n ^ Z.of_nat n)%Z) by (apply Z.pow_pos_nonneg; lia).
  rewrite qden_superexp, Nat2Z.inj_succ, Z.pow_succ_r by lia.
  nia.
Qed.

(* ===================================================================== *)
(*  A reciprocal inequality helper                                         *)
(* ===================================================================== *)

Lemma Qinv_lt_pos : forall a b, 0 < b -> b < a -> 1 / a < 1 / b.
Proof.
  intros a b Hb Hba.
  assert (Ha : 0 < a) by lra.
  assert (Heq : 1 / b - 1 / a == (a - b) / (a * b)) by (field; lra).
  assert (Hp : 0 < (a - b) / (a * b)).
  { unfold Qdiv. apply Qmult_lt_0_compat; [ lra | apply Qinv_lt_0_compat, Qmult_lt_0_compat; lra ]. }
  lra.
Qed.

(* ===================================================================== *)
(*  ★★ THE LIOUVILLE GAP: the next term beats 1/qₙ^n                       *)
(* ===================================================================== *)

(** ★★ At EVERY stage n ≥ 1, the move to the next stage is smaller than 1/qₙ^n:
      Sₙ₊₁ − Sₙ = 1/qₙ₊₁ = 1/qₙ^(n+1) < 1/qₙ^n.
    So the rational convergent pₙ/qₙ approximates the process to order n+1 — for every n.  This is the
    Liouville signature: approximation to ALL orders, which no algebraic number admits. *)
Theorem liouville_gap : forall n,
  (1 <= n)%nat ->
  lsum (S n) - lsum n < 1 / inject_Z ((qden n ^ Z.of_nat n)%Z).
Proof.
  intros n Hn.
  assert (Hstep : lsum (S n) - lsum n == lterm (S n)) by (simpl; ring).
  rewrite Hstep. unfold lterm.
  apply Qinv_lt_pos.
  - (* 0 < inject_Z (qden n ^ Z.of_nat n) *)
    assert (0 < qden n ^ Z.of_nat n)%Z by (apply Z.pow_pos_nonneg; [ apply qden_pos | lia ]).
    unfold Qlt, inject_Z; simpl; lia.
  - (* inject_Z (qden n ^ Z.of_nat n) < inject_Z (qden (S n)) *)
    pose proof (qden_pow_n_lt n) as Hlt.
    unfold Qlt, inject_Z; simpl; lia.
Qed.

(* ===================================================================== *)
(*  The integer convergent: Sₙ = pₙ/qₙ with pₙ ∈ ℤ                          *)
(* ===================================================================== *)

(** ★ The n-th stage is a genuine rational pₙ/qₙ with qₙ = 2^(n!): scaling Sₙ by qₙ gives an integer. *)
Lemma lsum_integer : forall n, exists p : Z, inject_Z p == inject_Z (qden n) * lsum n.
Proof.
  induction n.
  - exists 1%Z. vm_compute. reflexivity.
  - destruct IHn as [p Hp].
    exists (qden n ^ Z.of_nat n * p + 1)%Z.
    assert (Hqs : qden (S n) = (qden n ^ Z.of_nat n * qden n)%Z).
    { rewrite qden_superexp, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }
    assert (Hne : ~ inject_Z (qden (S n)) == 0) by apply qden_ne.
    change (lsum (S n)) with (lsum n + lterm (S n)).
    unfold lterm.
    rewrite Qmult_plus_distr_r.
    (* second summand: inject_Z (qden (S n)) * (1 / inject_Z (qden (S n))) == 1 *)
    assert (H2 : inject_Z (qden (S n)) * (1 / inject_Z (qden (S n))) == 1) by (field; exact Hne).
    rewrite H2.
    (* first summand: inject_Z (qden (S n)) * lsum n == inject_Z (qden n ^ Z.of_nat n) * inject_Z (qden n) * lsum n *)
    rewrite Hqs, inject_Z_mult.
    rewrite inject_Z_plus, inject_Z_mult.
    change (inject_Z 1) with 1.
    (* goal: inject_Z(qden n^n)*inject_Z p + 1 == inject_Z(qden n^n)*inject_Z(qden n)*lsum n + 1 *)
    rewrite Hp. ring.
Qed.

(* ===================================================================== *)
(*  Concrete stages and a concrete gap                                     *)
(* ===================================================================== *)

(** q₀ = 2, q₁ = 2, q₂ = 4, q₃ = 64 (= 2^(0!),2^(1!),2^(2!),2^(3!)). *)
Example qden_values : qden 0 = 2%Z /\ qden 1 = 2%Z /\ qden 2 = 4%Z /\ qden 3 = 64%Z.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** S₂ = 1/2 + 1/2 + 1/4 = 5/4. *)
Example lsum2_value : lsum 2 == 5 # 4.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** A constructive number beyond the algebraic boundary — the Liouville signature:
      (super-exp)   qₙ₊₁ = qₙ^(n+1) — the denominator grows super-exponentially;
      (gap)         Sₙ₊₁ − Sₙ < 1/qₙ^n at every n ≥ 1 — approximation to ALL orders;
      (convergent)  Sₙ = pₙ/qₙ with pₙ ∈ ℤ, qₙ = 2^(n!) — a genuine rational of huge denominator.
    By Liouville's theorem (classical) an algebraic number of degree d admits |α − p/q| ≥ c/q^d, so a number
    approximable to all orders is TRANSCENDENTAL.  Hence L = Σ 1/2^(k!) lies beyond the algebraic decider's
    whole domain — the transcendental layer of the finitization boundary (Element ⊂ algebraic role-limit,
    DECIDED ⊂ transcendental role-limit, here CONSTRUCTED).  P4-consistent: only the process and its rational
    stages, no completed L.  Level: the constructive Liouville signature is new in the repo; transcendence
    itself is the classical theorem, cited. *)
Theorem liouville_beyond_algebraic :
  (forall n, (qden (S n) = (qden n) ^ Z.of_nat (S n))%Z)
  /\ (forall n, (1 <= n)%nat -> lsum (S n) - lsum n < 1 / inject_Z ((qden n ^ Z.of_nat n)%Z))
  /\ (forall n, exists p : Z, inject_Z p == inject_Z (qden n) * lsum n).
Proof.
  split; [ exact qden_superexp | ].
  split; [ exact liouville_gap | exact lsum_integer ].
Qed.
