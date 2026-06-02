(** * ProcessExpProcess.v — The exponential e (and e^t) as a PROCESS over ℚ
      (Part VIII, batch C; bridge to Part IV)

    Elements: rational stages (1+1/(N+1))^(N+1); the Euler trajectory of y'=y
    Roles:    e = role-limit of the rising process; e^t = role-limit; each stage = role-approx
    Rules:    e-process = Euler trajectory of y'=y at t=1: y_{k+1}=y_k·(1+h), h=1/(N+1)

    e and e^t are NOT completed transcendentals plucked from ℝ — they are role-limits of
    rational Cauchy processes (the Euler trajectory of y'=y). Under P4, what is actual is the
    finite rational stage (1+1/(N+1))^(N+1); e is the Rule organizing the unbounded process.

    ============ E/R/R разбор ============
      Rules (L5): процесс e = Эйлер-траектория y'=y при t=1, y_{k+1}=y_k(1+h), h=1/(N+1);
                  ограниченность снизу (Бернулли ⟹ ≥2); рост к e.
      Roles (L4): (1+1/(N+1))^(N+1) = роль-приближение; e = роль-предел (НЕ Элемент);
                  «иррационально ли e» — не-вопрос (P4): e есть незавершённый ПРОЦЕСС.
      Elements  : каждая стадия (1+1/(N+1))^(N+1) — рациональный Элемент (актуальна).
    ДИАГНОСТИКА: e, e^t — роль-пределы рациональных процессов (финитно: каждая стадия над ℚ);
    «экспонента» = Правило, порождающее процесс (Эйлер y'=y), не завершённый объект из ℝ.

    HONEST FRONTIER: proved here — concrete stages, the Euler-of-y'=y bridge (closed form),
    a Bernoulli lower bound (e-process ≥ 2), concrete climb and concrete < 3. Full monotonicity,
    the uniform bound < 3 for all N (binomial), and the explicit is_cauchy limit are the
    role-properties (the last classic-based) — left as the honest P4 frontier; e itself is the
    role-limit, not a completed transcendental.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.

Open Scope Q_scope.

(* ---- local rational power (self-contained) ---- *)
Fixpoint qpow (b : Q) (n : nat) : Q :=
  match n with O => 1 | S k => b * qpow b k end.

(* ---- Euler method for y' = y  (f(t,y) = y): start y0, step h, M steps ---- *)
Fixpoint euler_yeqy (h y0 : Q) (M : nat) : Q :=
  match M with
  | O => y0
  | S k => euler_yeqy h y0 k + h * euler_yeqy h y0 k
  end.

(* ---- the e-process: stage N is (1 + 1/(N+1))^(N+1) ---- *)
Definition exp1_process (N : nat) : Q :=
  qpow (1 + 1 / inject_Z (Z.of_nat (S N))) (S N).

(* ---- the e^t-process: stage N is (1 + t/(N+1))^(N+1) ---- *)
Definition expt_process (t : Q) (N : nat) : Q :=
  qpow (1 + t / inject_Z (Z.of_nat (S N))) (S N).

(* ===================================================================== *)
(*  Concrete rational stages of the e-process                              *)
(* ===================================================================== *)

Lemma exp1_0 : exp1_process 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma exp1_1 : exp1_process 1 == 9 # 4.
Proof. vm_compute. reflexivity. Qed.

Lemma exp1_2 : exp1_process 2 == 64 # 27.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The e-process IS the Euler trajectory of y' = y at t = 1               *)
(* ===================================================================== *)

Lemma euler_yeqy_closed : forall h y0 M, euler_yeqy h y0 M == y0 * qpow (1 + h) M.
Proof.
  intros h y0 M. induction M as [|k IH].
  - cbn [euler_yeqy qpow]. ring.
  - cbn [euler_yeqy qpow]. rewrite !IH. ring.
Qed.

(** The N-th stage of the e-process equals the (N+1)-step Euler trajectory of y'=y,
    y(0)=1, step 1/(N+1): existence of e is a property of a PROCESS (the Euler run),
    not of a pre-existing transcendental. *)
Lemma exp1_is_euler : forall N,
  exp1_process N == euler_yeqy (1 / inject_Z (Z.of_nat (S N))) 1 (S N).
Proof.
  intro N. unfold exp1_process. rewrite euler_yeqy_closed. ring.
Qed.

(* ===================================================================== *)
(*  Bernoulli lower bound: the e-process is bounded below by 2             *)
(* ===================================================================== *)

Lemma bernoulli_nonneg : forall (x : Q) (n : nat),
  0 <= x -> 1 + inject_Z (Z.of_nat n) * x <= qpow (1 + x) n.
Proof.
  intros x n Hx. induction n as [|k IH].
  - cbn [qpow].
    assert (Hb0 : 1 + inject_Z (Z.of_nat 0) * x == 1).
    { replace (inject_Z (Z.of_nat 0)) with 0 by reflexivity. ring. }
    rewrite Hb0. apply Qle_refl.
  - cbn [qpow].
    set (m := inject_Z (Z.of_nat k)).
    assert (Hm : 0 <= m).
    { unfold m. change (inject_Z 0 <= inject_Z (Z.of_nat k)).
      rewrite <- Zle_Qle. lia. }
    assert (H1x : 0 <= 1 + x) by lra.
    assert (Hstep1 : (1 + m * x) * (1 + x) <= (1 + x) * qpow (1 + x) k).
    { rewrite (Qmult_comm (1 + x) (qpow (1 + x) k)).
      apply Qmult_le_compat_r; [ exact IH | exact H1x ]. }
    assert (HSk : inject_Z (Z.of_nat (S k)) == m + 1).
    { unfold m. rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1)%Z by lia.
      rewrite inject_Z_plus. reflexivity. }
    rewrite HSk.
    assert (Hmx2 : 0 <= m * x * x).
    { apply Qmult_le_0_compat;
        [ apply Qmult_le_0_compat; [ exact Hm | exact Hx ] | exact Hx ]. }
    apply (Qle_trans _ ((1 + m * x) * (1 + x))); [ | exact Hstep1 ].
    setoid_replace ((1 + m * x) * (1 + x)) with (1 + (m + 1) * x + m * x * x) by ring.
    lra.
Qed.

Lemma exp1_pos_denom : forall N, 0 < inject_Z (Z.of_nat (S N)).
Proof.
  intro N. change 0 with (inject_Z 0). rewrite <- Zlt_Qlt.
  rewrite Nat2Z.inj_succ. lia.
Qed.

(** The e-process never drops below 2 (Bernoulli applied to x = 1/(N+1)): a genuine
    over-ℚ lower bound for every stage, complementing the concrete climb. *)
Lemma exp1_lower : forall N, 2 <= exp1_process N.
Proof.
  intro N. unfold exp1_process.
  pose proof (exp1_pos_denom N) as Hd.
  remember (inject_Z (Z.of_nat (S N))) as d eqn:Hde.
  assert (Hx : 0 <= 1 / d).
  { apply Qlt_le_weak. unfold Qdiv. rewrite Qmult_1_l.
    apply Qinv_lt_0_compat. exact Hd. }
  pose proof (bernoulli_nonneg (1 / d) (S N) Hx) as HB.
  rewrite <- Hde in HB.
  assert (Hdne : ~ d == 0).
  { intro Hc. rewrite Hc in Hd. apply (Qlt_irrefl 0). exact Hd. }
  assert (He : 1 + d * (1 / d) == 2) by (field; exact Hdne).
  rewrite He in HB. exact HB.
Qed.

(* ===================================================================== *)
(*  Concrete monotone climb and concrete upper bound (< 3)                 *)
(* ===================================================================== *)

Lemma exp1_climb : exp1_process 0 < exp1_process 1 /\ exp1_process 1 < exp1_process 2.
Proof. split; now vm_compute. Qed.

Lemma exp1_below3 :
  exp1_process 0 < 3 /\ exp1_process 1 < 3 /\ exp1_process 2 < 3.
Proof. repeat split; now vm_compute. Qed.

(* ===================================================================== *)
(*  The e^t-process: concrete stages (e^0-process = 1, e^1 first stage = 2) *)
(* ===================================================================== *)

Lemma expt_0_0 : expt_process 0 0 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma expt_1_0 : expt_process 1 0 == 2.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions exp1_is_euler.
Print Assumptions exp1_lower.
