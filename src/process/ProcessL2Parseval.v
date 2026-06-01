(** * ProcessL2Parseval.v — Parseval equality as a completeness criterion
      (F-29 frontier, Part VI)

    Elements: coefficients cₖ = ⟨eₖ,f⟩; residual coordinates f − Σcₖeₖ; finite sums
    Roles:    ⟨eₖ,f⟩ = projection coordinate; ‖r_K‖² = completeness defect;
              Parseval equality = no energy loss; completeness = system exhausts f
    Rules:    Σ_{k<K}⟨eₖ,f⟩² + ‖r_K‖² = ‖f‖² (energy split);
              Σ_{k<K}⟨eₖ,f⟩² = ‖f‖²  ⟺  ‖r_K‖² = 0  ⟺  f recovered by its expansion

    Building on the general Bessel inequality (ProcessL2BesselGeneral.resid_norm),
    we close the gap to EQUALITY. The residual-norm identity ‖r_K‖² = ‖f‖² − Σcₖ²
    immediately gives the energy split, hence Parseval equality holds EXACTLY iff the
    residual has zero norm. Over ℚ a finite sum of squares is zero iff every term is
    zero, so ‖r_K‖² = 0 iff the expansion reconstructs f on all N coordinates. This
    is the honest, constructive content of "Parseval = completeness criterion": for a
    FINITE orthonormal system on N coordinates it is a pure process/algebra fact.

    HONEST FRONTIER (P4 boundary): the INFINITE-basis Parseval (K,N → ∞), the closed
    span equalling the whole space, and the unconditional equality for a completed
    orthonormal basis are role-limits — we do NOT construct a completed basis. Here we
    prove the finite completeness criterion exactly.

    ============ E/R/R разбор ============
      Rules (L5): Σ⟨eₖ,f⟩²+‖r_K‖²=‖f‖² (сохранение энергии); Парсеваль ⟺ ‖r_K‖²=0 ⟺
                  f точно восстановлена разложением (полнота).
      Roles (L4): ⟨eₖ,f⟩ = роль-координата; ‖r_K‖² = роль-дефект полноты; Парсеваль =
                  роль-равенство (нет потери энергии); полнота = роль-свойство системы.
      Elements  : cₖ=⟨eₖ,f⟩, координаты остатка, конечные суммы Σ_{i<N}, Σ_{k<K} (L1+P4).
    ДИАГНОСТИКА: для КОНЕЧНОЙ системы (K векторов, N координат) равенство и критерий —
    процессно-алгебраический факт (resid_norm + «Σ квадратов=0 ⟹ каждый=0»); бесконечный
    базис / замкнутая оболочка = всё пространство — роль-предел, P4-граница.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.             (* q_sum, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.   (* q_sum_zero *)
From ToS Require Import process.ProcessCompactSpectral. (* seq_inner *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg *)
From ToS Require Import process.ProcessL2BesselGeneral. (* resid_norm, q_sum_ext_bounded *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  A finite sum of squares over ℚ is zero iff every term is zero.        *)
(* ===================================================================== *)

Lemma q_sum_sq_zero : forall (g : nat -> Q) (N : nat),
  q_sum (fun i => g i * g i) N == 0 ->
  forall i, (i < N)%nat -> g i == 0.
Proof.
  intros g N. induction N as [|k IH]; intros Hsum i Hi.
  - lia.
  - cbn [q_sum] in Hsum.
    assert (Hnn1 : 0 <= q_sum (fun j => g j * g j) k)
      by (apply q_sum_nonneg; intro j; apply q_sq_nonneg).
    assert (Hnn2 : 0 <= g k * g k) by (apply q_sq_nonneg).
    assert (Hk0 : g k * g k == 0) by lra.
    assert (Hrest : q_sum (fun j => g j * g j) k == 0) by lra.
    assert (Hgk : g k == 0)
      by (destruct (Qmult_integral _ _ Hk0) as [H0 | H0]; exact H0).
    destruct (Nat.eqb i k) eqn:E.
    + apply Nat.eqb_eq in E. subst i. exact Hgk.
    + apply Nat.eqb_neq in E. apply IH; [ exact Hrest | lia ].
Qed.

(* ===================================================================== *)
(*  Parseval equality as a completeness criterion for an orthonormal      *)
(*  system {eₖ} on N coordinates.                                         *)
(* ===================================================================== *)

Section ON.

Variable e : nat -> nat -> Q.
Variable N : nat.
Hypothesis Hon : forall i j, seq_inner (e i) (e j) N == (if Nat.eqb i j then 1 else 0).
Variable f : nat -> Q.

(* The partial reconstruction and its residual (display-only notations, so the
   underlying terms match ProcessL2BesselGeneral.resid_norm exactly). *)
Local Notation Resid K :=
  (fun m => f m - q_sum (fun k => seq_inner (e k) f N * e k m) K).
Local Notation ParsevalSum K :=
  (q_sum (fun k => seq_inner (e k) f N * seq_inner (e k) f N) K).

(** Energy split: Σ_{k<K} ⟨eₖ,f⟩² + ‖r_K‖² = ‖f‖². *)
Lemma energy_split : forall K,
  ParsevalSum K + seq_inner (Resid K) (Resid K) N == seq_inner f f N.
Proof.
  intro K. pose proof (resid_norm e N Hon f K) as H. lra.
Qed.

(** Parseval equality holds exactly iff the residual has zero norm. *)
Lemma parseval_iff_resid_zero : forall K,
  (ParsevalSum K == seq_inner f f N)
  <-> (seq_inner (Resid K) (Resid K) N == 0).
Proof.
  intro K. pose proof (energy_split K) as H. split; intro Hx; lra.
Qed.

(** Completeness ⟹ Parseval: if the expansion reconstructs f on every coordinate
    m < N, the equality holds. *)
Lemma parseval_of_complete : forall K,
  (forall m, (m < N)%nat ->
     q_sum (fun k => seq_inner (e k) f N * e k m) K == f m) ->
  ParsevalSum K == seq_inner f f N.
Proof.
  intros K Hc.
  pose proof (energy_split K) as H.
  assert (Hz : seq_inner (Resid K) (Resid K) N == 0).
  { unfold seq_inner.
    transitivity (q_sum (fun _ : nat => 0) N).
    - apply q_sum_ext_bounded. intros i Hi. cbn beta.
      assert (Hr : f i - q_sum (fun k => seq_inner (e k) f N * e k i) K == 0)
        by (rewrite (Hc i Hi); ring).
      rewrite Hr. ring.
    - apply q_sum_zero. }
  lra.
Qed.

(** Parseval ⟹ completeness: equality forces the residual to vanish on every
    coordinate, so the expansion reconstructs f. *)
Lemma complete_of_parseval : forall K,
  ParsevalSum K == seq_inner f f N ->
  forall m, (m < N)%nat ->
    q_sum (fun k => seq_inner (e k) f N * e k m) K == f m.
Proof.
  intros K Hp m Hm.
  pose proof (proj1 (parseval_iff_resid_zero K) Hp) as Hz.
  unfold seq_inner in Hz.
  pose proof (q_sum_sq_zero (Resid K) N Hz m Hm) as Hgm.
  cbn beta in Hgm.
  lra.
Qed.

(** Capstone: Parseval equality ⟺ the orthonormal system completely reconstructs
    f on the N coordinates. *)
Theorem parseval_iff_complete : forall K,
  (ParsevalSum K == seq_inner f f N)
  <-> (forall m, (m < N)%nat ->
         q_sum (fun k => seq_inner (e k) f N * e k m) K == f m).
Proof.
  intro K. split.
  - apply complete_of_parseval.
  - apply parseval_of_complete.
Qed.

End ON.

(* Concrete witness that Parseval is ATTAINED: standard basis on N=2 coordinates,
   f = (3,4). Σ_{k<2} ⟨eₖ,f⟩² = 9 + 16 = 25 = ‖f‖². *)
Example parseval_std_concrete :
  let e := fun i m => if Nat.eqb i m then 1 else 0 in
  let f := fun n => if Nat.eqb n 0 then 3 else 4 in
  q_sum (fun k => seq_inner (e k) f 2 * seq_inner (e k) f 2) 2 == seq_inner f f 2.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions parseval_iff_resid_zero.
Print Assumptions parseval_iff_complete.
