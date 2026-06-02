(** * ProcessODEStability.v — Continuous dependence on initial data (stability)
      of the Euler solution-process, with the e^{Lt} growth multiplier (Part VIII, batch B)

    Elements: rational divergences |y_n − ỹ_n|, growth factors (1+L·h)^n
    Roles:    |y_n − ỹ_n| = role-divergence; (1+L·h)^n = role-growth-factor; e^{Lt} = its
              role-limit; L = role-rate of error growth; y0 − z0 = role-perturbation
    Rules:    Lipschitz f ⟹ |Δ_{n+1}| ≤ (1+L·h)|Δ_n| ⟹ |Δ_n| ≤ (1+L·h)^n |Δ_0|; the factor
              (1+L·h)^n is the n-th stage of the e^{Lt}-process (Euler-of-y'=y, batch C)

    Stability (continuous dependence) is a controlled GROWTH of the divergence PROCESS,
    bounded by a finite rational factor (1+L·h)^n. The classical form e^{Lt} is the role-limit
    of that factor (the Euler process (1+L·t/n)^n → e^{Lt}, batch C), not a pre-given
    exponential. On a finite interval the divergence is finite — that is the content over ℚ.

    ============ E/R/R разбор ============
      Rules (L5): Липшиц ⟹ |Δ_{n+1}|≤(1+Lh)|Δ_n| ⟹ |Δ_n|≤(1+Lh)^n|Δ_0|; (1+Lh)^n = стадия
                  e^{Lt}-процесса (h=t/n).
      Roles (L4): |Δ_n| = роль-расхождение; (1+Lh)^n = роль-множитель роста; e^{Lt} = роль-предел;
                  L = роль-скорость; y0−z0 = роль-возмущение.
      Elements  : рациональные |Δ_n|, (1+Lh)^n, конечные n (L1+P4).
    ДИАГНОСТИКА: устойчивость = контролируемый рост расхождения процесса (конечный множитель);
    e^{Lt} — роль-предел множителя (Эйлер-процесс из C), не предзаданная экспонента.

    HONEST FRONTIER: proved over ℚ — the one-step divergence bound, the geometric bound
    |Δ_n| ≤ (1+L·h)^n |Δ_0|, and the identification of the time-uniform growth factor with the
    e^{Lt}-process stage. The COMPLETED e^{Lt} as an object is the role-limit (classic-based as a
    completed transcendental); global-in-time stability is the honest frontier.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessExpProcess.   (* qpow, expt_process *)

Open Scope Q_scope.

(* left multiplication is monotone (this Rocq build ships only Qmult_le_compat_r) *)
Lemma qmul_le_l : forall x y z, 0 <= x -> y <= z -> x * y <= x * z.
Proof.
  intros x y z Hx Hyz. rewrite (Qmult_comm x y), (Qmult_comm x z).
  apply Qmult_le_compat_r; assumption.
Qed.

Section Stability.

Variable f : Q -> Q -> Q.            (* f(t,y) — the ODE right-hand side *)
Variable L : Q.                      (* Lipschitz constant *)
Hypothesis HL : 0 <= L.
Hypothesis Hlip : forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2).
Variable h : Q.                      (* step size *)
Hypothesis Hh : 0 <= h.

Definition tg (n : nat) : Q := inject_Z (Z.of_nat n) * h.   (* grid time t_n = n·h *)

(* Euler trajectory of y' = f(t,y) from start y0 *)
Fixpoint euler (y0 : Q) (n : nat) : Q :=
  match n with
  | O => y0
  | S k => euler y0 k + h * f (tg k) (euler y0 k)
  end.

(** One Euler step expands the divergence of two trajectories by at most (1 + L·h). *)
Lemma euler_step_diff : forall y0 z0 k,
  Qabs (euler y0 (S k) - euler z0 (S k))
  <= (1 + L * h) * Qabs (euler y0 k - euler z0 k).
Proof.
  intros y0 z0 k. cbn [euler].
  set (a := euler y0 k). set (b := euler z0 k).
  eapply Qle_trans.
  { setoid_replace ((a + h * f (tg k) a) - (b + h * f (tg k) b))
      with ((a - b) + h * (f (tg k) a - f (tg k) b)) by ring.
    apply Qabs_triangle. }
  assert (Hh2 : Qabs (h * (f (tg k) a - f (tg k) b)) <= h * (L * Qabs (a - b))).
  { rewrite Qabs_Qmult. rewrite (Qabs_pos h Hh).
    apply qmul_le_l; [ exact Hh | apply Hlip ]. }
  apply Qle_trans with (Qabs (a - b) + h * (L * Qabs (a - b))).
  - apply Qplus_le_compat; [ apply Qle_refl | exact Hh2 ].
  - setoid_replace (Qabs (a - b) + h * (L * Qabs (a - b)))
      with ((1 + L * h) * Qabs (a - b)) by ring.
    apply Qle_refl.
Qed.

(** Continuous dependence on initial data: the divergence at step n is bounded by the
    geometric factor (1+L·h)^n times the initial perturbation. *)
Lemma euler_diff_bound : forall y0 z0 n,
  Qabs (euler y0 n - euler z0 n) <= qpow (1 + L * h) n * Qabs (y0 - z0).
Proof.
  intros y0 z0 n. induction n as [|k IH].
  - cbn [euler qpow].
    setoid_replace (1 * Qabs (y0 - z0)) with (Qabs (y0 - z0)) by ring.
    apply Qle_refl.
  - eapply Qle_trans; [ apply euler_step_diff | ].
    apply Qle_trans with ((1 + L * h) * (qpow (1 + L * h) k * Qabs (y0 - z0))).
    + apply qmul_le_l.
      * assert (Hlh : 0 <= L * h) by (apply Qmult_le_0_compat; assumption). lra.
      * exact IH.
    + cbn [qpow].
      setoid_replace ((1 + L * h) * (qpow (1 + L * h) k * Qabs (y0 - z0)))
        with (((1 + L * h) * qpow (1 + L * h) k) * Qabs (y0 - z0)) by ring.
      apply Qle_refl.
Qed.

End Stability.

(** Bridge to batch C: with the time-uniform step h = t/n (so n·h = t reaches time t), the
    growth factor (1 + L·t/n)^n is EXACTLY the n-th stage of the e^{L·t}-process expt_process.
    Hence euler_diff_bound reads |Δ_n| ≤ expt_process(L·t)(n−1) · |Δ_0|, whose role-limit is
    e^{L·t}: the classical continuous-dependence bound, with e^{Lt} as a PROCESS. *)
Lemma euler_growth_is_expt_process : forall (s : Q) (k : nat),
  qpow (1 + s / inject_Z (Z.of_nat (S k))) (S k) == expt_process s k.
Proof. intros s k. unfold expt_process. reflexivity. Qed.

(** Concrete growth factor: L=1, h=1, 3 steps ⟹ multiplier 2^3 = 8. *)
Lemma stability_mult_8 : qpow (1 + 1 * 1) 3 == 8.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions euler_diff_bound.
Print Assumptions euler_growth_is_expt_process.
