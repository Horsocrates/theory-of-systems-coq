(** * ProcessL2Triangle.v — L² (squared) distance and its triangle inequality
      (F-29 / Riesz–Fischer core, Part VI)

    Elements: rational sample differences (aᵢ−bᵢ); finite squared-distance sums
    Roles:    L²-distance d²(a,b) as a closeness measure of two L²-processes
    Rules:    d²(a,c) ≤ 2·d²(a,b) + 2·d²(b,c) (sqrt-free triangle, from (x−y)²≥0)

    Completeness of L² (Riesz–Fischer) rests on the metric structure. We give the
    SQUARED L²-distance on process L² (sequences nat→Q) and prove its key
    properties, above all the sqrt-FREE triangle inequality
        d²(a,c) ≤ 2·d²(a,b) + 2·d²(b,c),
    which is exactly the tool L²-completeness arguments use (it lets a Cauchy
    process name a limit-role). The inequality is purely algebraic: the gap
        2(a−b)² + 2(b−c)² − (a−c)²  =  (a − 2b + c)²  ≥  0,
    so no square roots and no completed object enter. Working on sequences
    (not composed functions) keeps it clean; the full Riesz–Fischer (a Cauchy
    sequence converges to a CONSTRUCTED limit) needs the L²-completion limit
    construction and stays a process-frontier — this is the metric it rests on.

    ============ E/R/R разбор ============
      Rules (L5): d²(a,c) ≤ 2d²(a,b)+2d²(b,c); d²≥0; симметрия; d²(a,a)=0.
      Roles (L4): d² = роль-мера близости; треугольник = роль-связь, делающая
                  Коши-процесс именующим предел-роль (полнота).
      Elements  : рациональные sample-разности (aᵢ−bᵢ), конечные суммы (L1+P4).
    ДИАГНОСТИКА: полнота L² — не свойство завершённого гильбертова, а процессная
    связь; sqrt-free треугольник = то, что позволяет Коши-процессу именовать предел.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.            (* q_sum, q_sum_le, q_sum_nonneg *)
From ToS Require Import process.ProcessFubiniGeneral.  (* q_sum_zero, q_sum_ext, q_sum_plus, q_sum_scale *)
From ToS Require Import process.ProcessL2CauchySchwarz. (* q_sq_nonneg : 0 <= x*x *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Squared L²-distance on process L² (sequences nat → Q).               *)
(*    d²(a,b)_N = Σ_{i<N} (aᵢ − bᵢ)²                                      *)
(* ===================================================================== *)

Definition l2_dist_sq (a b : nat -> Q) (N : nat) : Q :=
  q_sum (fun i => (a i - b i) * (a i - b i)) N.

(** Nonnegativity. *)
Lemma l2_dist_sq_nonneg : forall a b N, 0 <= l2_dist_sq a b N.
Proof.
  intros a b N. unfold l2_dist_sq. apply q_sum_nonneg. intro i. apply q_sq_nonneg.
Qed.

(** Symmetry. *)
Lemma l2_dist_sq_sym : forall a b N, l2_dist_sq a b N == l2_dist_sq b a N.
Proof.
  intros a b N. unfold l2_dist_sq. apply q_sum_ext. intro i. ring.
Qed.

(** Distance to self is zero. *)
Lemma l2_dist_sq_self : forall a N, l2_dist_sq a a N == 0.
Proof.
  intros a N. unfold l2_dist_sq.
  transitivity (q_sum (fun _ : nat => 0) N).
  - apply q_sum_ext. intro i. ring.
  - apply q_sum_zero.
Qed.

(* ===================================================================== *)
(*  MAIN: sqrt-free triangle inequality (the completeness workhorse).     *)
(* ===================================================================== *)

Theorem l2_dist_sq_triangle : forall a b c N,
  l2_dist_sq a c N <= 2 * l2_dist_sq a b N + 2 * l2_dist_sq b c N.
Proof.
  intros a b c N. unfold l2_dist_sq.
  apply Qle_trans with
    (q_sum (fun i => 2 * ((a i - b i) * (a i - b i))
                     + 2 * ((b i - c i) * (b i - c i))) N).
  - (* pointwise: (a−c)² ≤ 2(a−b)² + 2(b−c)²  since gap = (a−2b+c)² ≥ 0 *)
    apply q_sum_le. intro i.
    assert (Hgap : 2 * ((a i - b i) * (a i - b i)) + 2 * ((b i - c i) * (b i - c i))
                   - (a i - c i) * (a i - c i)
                   == (a i - 2 * b i + c i) * (a i - 2 * b i + c i)) by ring.
    assert (Hsq : 0 <= (a i - 2 * b i + c i) * (a i - 2 * b i + c i)) by apply q_sq_nonneg.
    lra.
  - (* Σ(2X+2Y) = 2ΣX + 2ΣY *)
    assert (Hp :
      q_sum (fun i => 2 * ((a i - b i) * (a i - b i))
                      + 2 * ((b i - c i) * (b i - c i))) N
      == q_sum (fun i => 2 * ((a i - b i) * (a i - b i))) N
         + q_sum (fun i => 2 * ((b i - c i) * (b i - c i))) N)
      by apply q_sum_plus.
    rewrite Hp.
    assert (Hsx :
      q_sum (fun i => 2 * ((a i - b i) * (a i - b i))) N
      == 2 * q_sum (fun i => (a i - b i) * (a i - b i)) N) by apply q_sum_scale.
    assert (Hsy :
      q_sum (fun i => 2 * ((b i - c i) * (b i - c i))) N
      == 2 * q_sum (fun i => (b i - c i) * (b i - c i)) N) by apply q_sum_scale.
    rewrite Hsx, Hsy. apply Qle_refl.
Qed.

(* Computational sanity: a, b, c three constant sample sequences. *)
Example l2_dist_sq_concrete :
  (* a≡1, b≡0 on 3 samples: d²(a,b) = 3·1 = 3 *)
  l2_dist_sq (fun _ => 1) (fun _ => 0) 3 == 3.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions l2_dist_sq_triangle.
