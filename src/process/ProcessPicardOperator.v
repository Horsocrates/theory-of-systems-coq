(** * ProcessPicardOperator.v — The Picard operator as a contraction on the SPACE
      OF FUNCTIONS (finite grid), over ℚ (Part VIII / centerpiece)

    Elements: grid functions y : nat→Q (values y_k at t_k = k·h, k ≤ N); rational
    Roles:    Φ = the Picard operator (a map of functions); sup-bound = role-metric
    Rules:    Φ(y)_k = y₀ + h·Σ_{j<k} f(t_j, y_j); under Lipschitz f, Φ is a CONTRACTION
              in the sup-metric over the grid with rate L·T (T = N·h)

    Closes the gap diagnosed for the existing ProcessPicard.v: there the strong
    contraction theorem is the SCALAR Euler–Picard fixed-step map on ℚ (rate L·h). Here
    the Picard operator Φ acts on the SPACE OF FUNCTIONS y↦y(·) (a grid function, a point
    of ℚ^{N+1}), and we prove it is a contraction in the SUP-metric (uniform bound D over
    the grid) with rate L·T. This is the genuine function-space Picard–Lindelöf, finite
    over ℚ, 0 axioms.

    PROVEN HERE (all 0 axioms): (1) Φ is a contraction in the sup-metric, rate L·T
    (picard_op_contraction); (2) the iterates have geometric gap ≤ (L·T)ⁿ·C₀, the sup-Cauchy
    content (picard_iter_gap); (3) the grid solution is UNIQUE — sup-norm Banach uniqueness via
    a finite-grid max gmax + contraction + L·T<1 (picard_unique).
    HONEST FRONTIER: the explicit is_cauchy/limit wrapper (iterates → completed solution-
    function) reuses the repo's geometric-series layer, which is L3/classic-based; global
    continuation, blow-up, and the COMPLETED solution-function as an object remain role-limits.

    ============ E/R/R разбор ============
      Rules (L5): Φ(y)_k=y₀+h·Σ_{j<k}f(t_j,y_j); Липшиц ⟹ Φ сжатие в sup-метрике, rate L·T;
                  итераты — геометрический зазор (LT)ⁿ (Коши при LT<1); неподвижная точка
                  (решение на сетке) единственна.
      Roles (L4): Φ = роль-оператор (отображение функций); равномерная оценка = роль-метрика;
                  итерат Φⁿ = роль-приближение; неподвижная точка = роль-решение; LT<1 = режим.
      Elements  : грид-функции y:nat→Q, значения y_k, конечные суммы, k≤N (L1+P4).
    ДИАГНОСТИКА: существование (Коши-зазор) + единственность решения = сходимость/жёсткость
    процесса сжатия на ПРОСТРАНСТВЕ ФУНКЦИЙ (финитно: сетка ℚ^{N+1}, sup-оценка) — над ℚ, 0 акс;
    завершённая функция-решение (предел) / глобальное продолжение — роль-предел / граница.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.   (* q_sum *)

Open Scope Q_scope.

Section PicardOperator.

Variable f : Q -> Q -> Q.            (* f(t,y) — the ODE right-hand side *)
Variable L : Q.
Hypothesis HL : 0 < L.
Hypothesis Hlip : forall t y1 y2, Qabs (f t y1 - f t y2) <= L * Qabs (y1 - y2).
Variable h : Q.
Hypothesis Hh : 0 <= h.
Variable y0 : Q.
Variable N : nat.                    (* grid: t_k = k·h, k ≤ N, interval length T = N·h *)

Definition Tlen : Q := inject_Z (Z.of_nat N) * h.
Definition tgrid (j : nat) : Q := inject_Z (Z.of_nat j) * h.

(** Picard operator on grid functions: Φ(y)_k = y₀ + h·Σ_{j<k} f(t_j, y_j). *)
Definition picard_sum (y : nat -> Q) (k : nat) : Q :=
  q_sum (fun j => f (tgrid j) (y j)) k.
Definition picard_op (y : nat -> Q) : nat -> Q :=
  fun k => y0 + h * picard_sum y k.

(** Difference of partial integral sums, bounded termwise by Lipschitz. *)
Lemma picard_diff_bound : forall (y z : nat -> Q) (D : Q) (k : nat),
  (forall j, (j < k)%nat -> Qabs (y j - z j) <= D) ->
  Qabs (picard_sum y k - picard_sum z k) <= inject_Z (Z.of_nat k) * (L * D).
Proof.
  intros y z D k. induction k as [|k IH]; intro Hb.
  - unfold picard_sum. cbn [q_sum].
    assert (Ha : Qabs (0 - 0) == 0) by (vm_compute; reflexivity).
    assert (Hz : inject_Z (Z.of_nat 0) * (L * D) == 0).
    { change (inject_Z (Z.of_nat 0)) with 0. ring. }
    rewrite Ha, Hz. apply Qle_refl.
  - assert (Hstep : picard_sum y (S k) - picard_sum z (S k)
                    == (picard_sum y k - picard_sum z k)
                       + (f (tgrid k) (y k) - f (tgrid k) (z k))).
    { unfold picard_sum. cbn [q_sum]. ring. }
    rewrite Hstep.
    eapply Qle_trans; [ apply Qabs_triangle | ].
    assert (HIH : Qabs (picard_sum y k - picard_sum z k)
                  <= inject_Z (Z.of_nat k) * (L * D)).
    { apply IH. intros j Hj. apply Hb. lia. }
    assert (Hterm : Qabs (f (tgrid k) (y k) - f (tgrid k) (z k)) <= L * D).
    { pose proof (Hlip (tgrid k) (y k) (z k)) as Hl.
      assert (Hyz : Qabs (y k - z k) <= D) by (apply Hb; lia).
      nra. }
    assert (Hsk : inject_Z (Z.of_nat (S k)) == inject_Z (Z.of_nat k) + 1).
    { rewrite Nat2Z.inj_succ, <- Z.add_1_r, inject_Z_plus. reflexivity. }
    rewrite Hsk.
    assert (Hexp : (inject_Z (Z.of_nat k) + 1) * (L * D)
                   == inject_Z (Z.of_nat k) * (L * D) + (L * D)) by ring.
    rewrite Hexp.
    apply Qplus_le_compat; [ exact HIH | exact Hterm ].
Qed.

(** ★ THE FUNCTION-SPACE PICARD CONTRACTION:
    if y and z are within uniform distance D over the grid (k ≤ N), then Φ y and Φ z
    are within L·T·D — Φ is a contraction in the sup-metric with rate L·T. *)
Theorem picard_op_contraction : forall (y z : nat -> Q) (D : Q) (k : nat),
  0 <= D ->
  (k <= N)%nat ->
  (forall j, (j <= N)%nat -> Qabs (y j - z j) <= D) ->
  Qabs (picard_op y k - picard_op z k) <= (L * Tlen) * D.
Proof.
  intros y z D k Hd HkN Hb.
  unfold picard_op.
  assert (Heq : y0 + h * picard_sum y k - (y0 + h * picard_sum z k)
                == h * (picard_sum y k - picard_sum z k)) by ring.
  rewrite Heq, Qabs_Qmult, (Qabs_pos h Hh).
  assert (Hpd : Qabs (picard_sum y k - picard_sum z k)
                <= inject_Z (Z.of_nat k) * (L * D)).
  { apply picard_diff_bound. intros j Hj. apply Hb. lia. }
  assert (Hk : inject_Z (Z.of_nat k) <= inject_Z (Z.of_nat N)).
  { unfold Qle; simpl; lia. }
  assert (Hc : 0 <= h * (L * D)).
  { apply Qmult_le_0_compat; [ exact Hh | apply Qmult_le_0_compat; [ lra | exact Hd ] ]. }
  apply Qle_trans with (h * (inject_Z (Z.of_nat k) * (L * D))).
  - assert (E0 : h * Qabs (picard_sum y k - picard_sum z k)
                 == Qabs (picard_sum y k - picard_sum z k) * h) by ring.
    assert (E0' : h * (inject_Z (Z.of_nat k) * (L * D))
                  == (inject_Z (Z.of_nat k) * (L * D)) * h) by ring.
    rewrite E0, E0'. apply Qmult_le_compat_r; [ exact Hpd | exact Hh ].
  - assert (E1 : h * (inject_Z (Z.of_nat k) * (L * D))
                 == inject_Z (Z.of_nat k) * (h * (L * D))) by ring.
    assert (E2 : (L * Tlen) * D == inject_Z (Z.of_nat N) * (h * (L * D))).
    { unfold Tlen. ring. }
    rewrite E1, E2. apply Qmult_le_compat_r; [ exact Hk | exact Hc ].
Qed.

(* ===================================================================== *)
(*  Max over a finite grid (realises the sup-metric)                       *)
(* ===================================================================== *)

Definition qmax2 (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma qmax2_le_l : forall a b, a <= qmax2 a b.
Proof.
  intros a b. unfold qmax2. destruct (Qle_bool a b) eqn:E.
  - rewrite <- Qle_bool_iff. exact E.
  - apply Qle_refl.
Qed.

Lemma qmax2_le_r : forall a b, b <= qmax2 a b.
Proof.
  intros a b. unfold qmax2. destruct (Qle_bool a b) eqn:E.
  - apply Qle_refl.
  - apply Qlt_le_weak, Qnot_le_lt. rewrite <- Qle_bool_iff, E. discriminate.
Qed.

Lemma qmax2_lub : forall a b c, a <= c -> b <= c -> qmax2 a b <= c.
Proof. intros a b c Ha Hb. unfold qmax2. destruct (Qle_bool a b); assumption. Qed.

Fixpoint gmax (g : nat -> Q) (n : nat) : Q :=
  match n with O => g O | S n' => qmax2 (gmax g n') (g (S n')) end.

Lemma gmax_ub : forall g n j, (j <= n)%nat -> g j <= gmax g n.
Proof.
  intros g n. induction n as [|n IH]; intros j Hj.
  - assert (j = O) by lia. subst. apply Qle_refl.
  - cbn [gmax]. destruct (Nat.eq_dec j (S n)) as [E|E].
    + subst. apply qmax2_le_r.
    + eapply Qle_trans; [ apply IH; lia | apply qmax2_le_l ].
Qed.

Lemma gmax_lub : forall g n c, (forall j, (j <= n)%nat -> g j <= c) -> gmax g n <= c.
Proof.
  intros g n. induction n as [|n IH]; intros c Hc.
  - apply Hc. lia.
  - cbn [gmax]. apply qmax2_lub.
    + apply IH. intros j Hj. apply Hc. lia.
    + apply Hc. lia.
Qed.

(* ===================================================================== *)
(*  Uniqueness of the grid solution (sup-norm Banach, 0 axioms)            *)
(* ===================================================================== *)

Hypothesis Hrate : L * Tlen < 1.

Theorem picard_unique : forall (y z : nat -> Q),
  (forall k, (k <= N)%nat -> picard_op y k == y k) ->
  (forall k, (k <= N)%nat -> picard_op z k == z k) ->
  forall k, (k <= N)%nat -> y k == z k.
Proof.
  intros y z Hy Hz.
  set (Dstar := gmax (fun j => Qabs (y j - z j)) N).
  assert (HD0 : 0 <= Dstar).
  { unfold Dstar. eapply Qle_trans;
      [ apply Qabs_nonneg | apply (gmax_ub (fun j => Qabs (y j - z j)) N 0); lia ]. }
  assert (Hbnd : forall j, (j <= N)%nat -> Qabs (y j - z j) <= Dstar).
  { intros j Hj. unfold Dstar. apply (gmax_ub (fun j0 => Qabs (y j0 - z j0)) N j Hj). }
  assert (Hctr : forall k, (k <= N)%nat -> Qabs (y k - z k) <= (L * Tlen) * Dstar).
  { intros k Hk.
    assert (Hyk := Hy k Hk). assert (Hzk := Hz k Hk).
    setoid_rewrite <- Hyk. setoid_rewrite <- Hzk.
    apply picard_op_contraction; [ exact HD0 | exact Hk | exact Hbnd ]. }
  assert (HDfix : Dstar <= (L * Tlen) * Dstar).
  { unfold Dstar at 1. apply gmax_lub. intros j Hj. apply Hctr. exact Hj. }
  set (r := L * Tlen) in *.
  assert (HDzero : Dstar == 0) by (apply Qle_antisym; [ nra | exact HD0 ]).
  intros k Hk.
  assert (Hb := Hbnd k Hk). rewrite HDzero in Hb.
  apply Qabs_Qle_condition in Hb. lra.
Qed.

(* ===================================================================== *)
(*  Picard iterates: geometric contraction (the Cauchy content)            *)
(* ===================================================================== *)

Fixpoint picard_iter (n : nat) : nat -> Q :=
  match n with O => (fun _ => y0) | S n' => picard_op (picard_iter n') end.

Fixpoint rpow (n : nat) : Q :=
  match n with O => 1 | S k => (L * Tlen) * rpow k end.

Lemma Tlen_nonneg : 0 <= Tlen.
Proof. unfold Tlen. apply Qmult_le_0_compat; [ unfold Qle; simpl; lia | exact Hh ]. Qed.

Lemma rpow_nonneg : forall n, 0 <= rpow n.
Proof.
  induction n as [|n IH]; cbn [rpow].
  - lra.
  - apply Qmult_le_0_compat; [ | exact IH ].
    apply Qmult_le_0_compat; [ lra | apply Tlen_nonneg ].
Qed.

(** ★ Geometric gap of the Picard iterates: gap_n ≤ (L·T)ⁿ · C₀.
    Together with L·T < 1 this is the sup-Cauchy of the iterate process — its
    limit (the solution) is the role-limit (the explicit is_cauchy wrapper reuses
    the repo's geometric-series layer, which is L3/classic-based). *)
Theorem picard_iter_gap : forall (C : Q) (n : nat),
  0 <= C ->
  (forall k, (k <= N)%nat -> Qabs (picard_iter 1 k - picard_iter 0 k) <= C) ->
  forall k, (k <= N)%nat ->
    Qabs (picard_iter (S n) k - picard_iter n k) <= rpow n * C.
Proof.
  intros C n HC Hfirst. induction n as [|n IH]; intros k Hk.
  - assert (Hr0 : rpow 0 * C == C) by (cbn [rpow]; ring).
    rewrite Hr0. apply Hfirst; exact Hk.
  - assert (Hstep : Qabs (picard_iter (S (S n)) k - picard_iter (S n) k)
                    <= (L * Tlen) * (rpow n * C)).
    { apply (picard_op_contraction (picard_iter (S n)) (picard_iter n) (rpow n * C) k).
      - apply Qmult_le_0_compat; [ apply rpow_nonneg | exact HC ].
      - exact Hk.
      - exact IH. }
    eapply Qle_trans; [ exact Hstep | ].
    assert (Hr : (L * Tlen) * (rpow n * C) == rpow (S n) * C) by (cbn [rpow]; ring).
    rewrite Hr. apply Qle_refl.
Qed.

End PicardOperator.

Print Assumptions picard_op_contraction.
Print Assumptions picard_unique.
Print Assumptions picard_iter_gap.
