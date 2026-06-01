(** * ProcessMCT.v — Monotone Convergence Theorem for integrals (F-27, Part VI)

    Elements: rational Riemann-sum integral values  ∫fₖ = w·Σ fₖ(xᵢ)
    Roles:    ∫f as the role-limit of the increasing bounded integral sequence
    Rules:    integral-monotone + bounded ⇒ monotone-bounded ⇒ Cauchy (classic/L3)

    Beppo-Levi / Monotone Convergence: if f₀ <= f₁ <= ... (pointwise increasing)
    and the fₖ are uniformly bounded, then ∫fₖ increases to ∫f (f = lim fₖ).
    We give the PROCESS form of the convergence core on a concrete, self-contained
    Riemann-sum integral over Q:
        riemann_sum f pts w N  :=  w · Σ_{i<N} f(pts i)        (width w, N cells)
    The sequence of integral VALUES k ↦ riemann_sum (fs k) pts w N is monotone
    increasing (riemann_sum_monotone) and bounded above by w·N·M
    (riemann_sum_bounded), hence — by monotone_bounded_Cauchy — it is a Cauchy
    process in k: the integrals CONVERGE.  That limit is ∫f.

    ============ E/R/R разбор (СНАЧАЛА) ============
      Elements (L1): рациональные значения интегралов ∫fₖ = w·Σ fₖ(xᵢ); сама
                     последовательность функций fs и узлы pts.
      Roles (L4):    ∫f = роль-предел растущей ограниченной последовательности
                     интегралов; «интеграл предела» = роль, которую играет sup.
      Rules (L5):    монотонность интеграла (riemann_sum_monotone) + ограниченность
                     (riemann_sum_bounded) ⇒ монотонно-ограниченный процесс ⇒ Cauchy
                     (monotone_bounded_Cauchy, использует classic/L3); правило
                     обмена ∫lim = lim∫.
      ЧЕСТНОСТЬ:
        • ДОКАЗАНО: последовательность интегралов ∫fₖ монотонна, ограничена и
          потому СХОДИТСЯ (is_Cauchy; цена — classic/L3, как и в MonotoneConvergence.v).
        • СОДЕРЖАТЕЛЬНАЯ ИНТЕРПРЕТАЦИЯ: этот предел ЕСТЬ ∫f.
        • ПРОГРАММА: отождествление с ∫(завершённого lim fₖ) требует завершённой
          предельной функции — P4-граница (актуальная бесконечность).
      НАШ ПУТЬ: формализуем процессную MCT (сходимость процесса интегралов) на
        самодостаточном Римановом интеграле, выводя монотонность интеграла ИЗ
        поточечного порядка функций (это и есть нетривиальное ядро MCT), а не
        «∫ завершённого предела». Зеркалит дисциплину F-30/F-32.
      ДИАГНОСТИКА: классическое «∫lim = lim∫» предполагает завершённую lim fₖ;
        у нас и fₖ, и предел — ПРОЦЕССЫ, а доказуемое ядро — сходимость
        монотонного ограниченного процесса интегралов.

    ПРИМЕЧАНИЕ (репликация): библиотечный lebesgue_process удовлетворяет ТЕМИ ЖЕ
    леммами — lebesgue_monotone и lebesgue_bounded (доказаны в ProcessLebesgue.v /
    используются в ProcessFatou.v). MCT доказана здесь для self-contained riemann_sum,
    чтобы не тянуть всю интегральную цепочку (Decision Log 2026-03: локальная
    репликация против stale .vo); доказательство переносится на lebesgue_process
    дословно, т.к. использует ТОЛЬКО монотонность + ограниченность.

    STATUS: 9 Qed, 0 Admitted, uses classic (L3) — MCT ⇔ LEM/LPO, no NEW axiom
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Finite sum  Σ_{i<N} g(i)  over Q                                       *)
(* ===================================================================== *)

Fixpoint q_sum (g : nat -> Q) (N : nat) : Q :=
  match N with
  | O => 0
  | S k => q_sum g k + g k
  end.

(** Sums of pointwise-ordered families are ordered. *)
Lemma q_sum_le : forall (g1 g2 : nat -> Q) (N : nat),
  (forall i, g1 i <= g2 i) -> q_sum g1 N <= q_sum g2 N.
Proof.
  intros g1 g2 N H. induction N as [|k IH]; cbn [q_sum].
  - apply Qle_refl.
  - apply Qplus_le_compat; [ exact IH | apply H ].
Qed.

(** A sum of nonneg terms is nonneg. *)
Lemma q_sum_nonneg : forall (g : nat -> Q) (N : nat),
  (forall i, 0 <= g i) -> 0 <= q_sum g N.
Proof.
  intros g N H. induction N as [|k IH]; cbn [q_sum].
  - apply Qle_refl.
  - apply Qle_trans with (q_sum g k + 0).
    + assert (E : q_sum g k + 0 == q_sum g k) by ring. rewrite E. exact IH.
    + apply Qplus_le_compat; [ apply Qle_refl | apply H ].
Qed.

(** Absolute bound: |Σ g| <= N · M  when every |g i| <= M. *)
Lemma q_sum_abs_bound : forall (g : nat -> Q) (M : Q) (N : nat),
  (forall i, Qabs (g i) <= M) ->
  Qabs (q_sum g N) <= inject_Z (Z.of_nat N) * M.
Proof.
  intros g M N HM. induction N as [|k IH]; cbn [q_sum].
  - assert (H0 : Qabs (0:Q) == 0) by (apply Qabs_pos; apply Qle_refl).
    rewrite H0.
    assert (HE : inject_Z (Z.of_nat 0) * M == 0) by (simpl; ring).
    rewrite HE. apply Qle_refl.
  - replace (Z.of_nat (S k)) with (Z.of_nat k + 1)%Z by lia.
    rewrite inject_Z_plus.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    change (inject_Z 1) with (1 # 1).
    assert (HRHS : (inject_Z (Z.of_nat k) + (1 # 1)) * M
                   == inject_Z (Z.of_nat k) * M + M) by ring.
    rewrite HRHS.
    apply Qplus_le_compat; [ exact IH | apply HM ].
Qed.

(* ===================================================================== *)
(*  The Riemann-sum integral:  ∫f ≈ w · Σ_{i<N} f(pts i)                  *)
(* ===================================================================== *)

Definition riemann_sum (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat) : Q :=
  w * q_sum (fun i => f (pts i)) N.

(** Rule 1: pointwise f <= g  ⇒  ∫f <= ∫g  (integral is monotone). *)
Lemma riemann_sum_monotone : forall (f g : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w -> (forall x, f x <= g x) ->
  riemann_sum f pts w N <= riemann_sum g pts w N.
Proof.
  intros f g pts w N Hw Hfg. unfold riemann_sum.
  rewrite (Qmult_comm w (q_sum (fun i => f (pts i)) N)).
  rewrite (Qmult_comm w (q_sum (fun i => g (pts i)) N)).
  apply Qmult_le_compat_r; [ apply q_sum_le; intro i; apply Hfg | exact Hw ].
Qed.

(** Rule 2: |f| <= M everywhere  ⇒  |∫f| <= w·N·M  (integral is bounded). *)
Lemma riemann_sum_bounded : forall (f : Q -> Q) (pts : nat -> Q) (w M : Q) (N : nat),
  0 <= w -> (forall i, Qabs (f (pts i)) <= M) ->
  Qabs (riemann_sum f pts w N) <= w * (inject_Z (Z.of_nat N) * M).
Proof.
  intros f pts w M N Hw HM. unfold riemann_sum.
  rewrite Qabs_Qmult.
  assert (Hwabs : Qabs w == w) by (apply Qabs_pos; exact Hw).
  rewrite Hwabs.
  rewrite (Qmult_comm w (Qabs (q_sum (fun i => f (pts i)) N))).
  rewrite (Qmult_comm w (inject_Z (Z.of_nat N) * M)).
  apply Qmult_le_compat_r; [ apply q_sum_abs_bound; exact HM | exact Hw ].
Qed.

(** Side fact: nonneg integrand ⇒ nonneg integral (standard MCT hypothesis). *)
Lemma riemann_sum_nonneg : forall (f : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w -> (forall i, 0 <= f (pts i)) ->
  0 <= riemann_sum f pts w N.
Proof.
  intros f pts w N Hw Hnn. unfold riemann_sum.
  rewrite (Qmult_comm w (q_sum (fun i => f (pts i)) N)).
  apply Qle_trans with (0 * w).
  - assert (E : 0 * w == 0) by ring. rewrite E. apply Qle_refl.
  - apply Qmult_le_compat_r; [ apply q_sum_nonneg; exact Hnn | exact Hw ].
Qed.

(* ===================================================================== *)
(*  MAIN: Monotone Convergence (process core).                            *)
(*  An increasing, uniformly bounded sequence of integrands has a         *)
(*  CONVERGENT (Cauchy) sequence of integrals — ∫fₖ ↑ ∫f.                 *)
(* ===================================================================== *)

Theorem process_mct : forall (fs : nat -> Q -> Q) (pts : nat -> Q) (w M : Q) (N : nat),
  0 <= w ->
  (forall k x, fs k x <= fs (S k) x) ->          (* pointwise increasing in k  *)
  (forall k x, Qabs (fs k x) <= M) ->             (* uniformly bounded          *)
  is_Cauchy (fun k => riemann_sum (fs k) pts w N).
Proof.
  intros fs pts w M N Hw Hmon Hbnd.
  apply monotone_bounded_Cauchy with (ub := w * (inject_Z (Z.of_nat N) * M)).
  - unfold monotone_increasing. intro k.
    apply riemann_sum_monotone; [ exact Hw | intro x; apply Hmon ].
  - intro k.
    apply Qle_trans with (Qabs (riemann_sum (fs k) pts w N)).
    + apply Qle_Qabs.
    + apply riemann_sum_bounded; [ exact Hw | intro i; apply Hbnd ].
Qed.

(* ===================================================================== *)
(*  Packaged MCT for nonneg increasing sequences (the classic statement). *)
(* ===================================================================== *)

Theorem process_mct_nonneg : forall (fs : nat -> Q -> Q) (pts : nat -> Q) (w M : Q) (N : nat),
  0 <= w ->
  (forall k x, 0 <= fs k x) ->                    (* nonnegative                *)
  (forall k x, fs k x <= fs (S k) x) ->           (* increasing                 *)
  (forall k x, Qabs (fs k x) <= M) ->             (* uniformly bounded          *)
  (forall k, 0 <= riemann_sum (fs k) pts w N) /\
  monotone_increasing (fun k => riemann_sum (fs k) pts w N) /\
  is_Cauchy (fun k => riemann_sum (fs k) pts w N).
Proof.
  intros fs pts w M N Hw Hnn Hmon Hbnd.
  split; [ | split ].
  - intro k. apply riemann_sum_nonneg; [ exact Hw | intro i; apply Hnn ].
  - unfold monotone_increasing. intro k.
    apply riemann_sum_monotone; [ exact Hw | intro x; apply Hmon ].
  - apply process_mct with (M := M); auto.
Qed.

(* Computational sanity check: ∫ of the constant 1 (width 1, 3 cells) = 3. *)
Example riemann_sum_const_1 :
  riemann_sum (fun _ => 1) (fun _ => 0) 1 3 == 3.
Proof. reflexivity. Qed.

Print Assumptions process_mct.
