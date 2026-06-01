(** * ProcessSigmaAdditive.v — Countable additivity of measure (F-26, Part VI)

    Elements: rational measures μ(Aₖ) ≥ 0 of disjoint sets; partial sums Sₙ
    Roles:    μ(⨆ₖ Aₖ) as the role-limit of the partial-measure process Sₙ
    Rules:    nonneg ⇒ Sₙ increasing; finite total mass ⇒ bounded ⇒ Cauchy (L3)

    σ-additivity: for pairwise-disjoint measurable A₀, A₁, ...,
        μ(⨆ₖ Aₖ)  =  Σₖ μ(Aₖ).
    The right side is the limit of the partial sums
        partial_measure μ n  :=  Σ_{k<n} μ(Aₖ)        (= q_sum μ n).
    If each μ(Aₖ) ≥ 0 then the partial sums are monotone increasing; if the total
    mass is finite (Sₙ ≤ B, e.g. B = μ of the whole space) they are bounded, hence
    — by monotone_bounded_Cauchy — they form a Cauchy process: the series CONVERGES.
    That limit is μ(⨆ₖ Aₖ).  We state σ-additivity in the P4 / process sense: the
    partial-measure process names the measure of the (never-completed) union.

    ============ E/R/R разбор (СНАЧАЛА) ============
      Elements (L1): рациональные меры μ(Aₖ) ≥ 0 непересекающихся множеств;
                     частичные суммы Sₙ = Σ_{k<n} μ(Aₖ).
      Roles (L4):    «мера объединения» μ(⨆Aₖ) = роль-предел процесса частичных сумм;
                     σ-аддитивность = роль, которую мера целого играет относительно частей.
      Rules (L5):    неотрицательность ⇒ Sₙ монотонно растёт; конечная общая масса B
                     ⇒ ограничено; ⇒ Cauchy (monotone_bounded_Cauchy, classic/L3);
                     правило перехода к пределу = конечная аддитивность + lim.
      ЧЕСТНОСТЬ:
        • ДОКАЗАНО: Sₙ растут (partial_measure_monotone, partial_measure_le),
          ограничены и потому СХОДЯТСЯ (is_Cauchy; цена — classic/L3).
        • СОДЕРЖАТЕЛЬНАЯ ИНТЕРПРЕТАЦИЯ: этот предел ЕСТЬ μ(⨆Aₖ).
        • ПРОГРАММА: завершённое счётное объединение ⨆ₖ Aₖ как ОБЪЕКТ —
          P4-граница (актуальная бесконечность).
      НАШ ПУТЬ: формализуем σ-аддитивность как СХОДИМОСТЬ процесса частичных сумм
        мер (через q_sum + monotone_bounded_Cauchy), а не равенство с мерой
        завершённого объединения. Зеркалит F-27/F-30/F-32.
      ДИАГНОСТИКА: классическое μ(⨆Aₖ)=Σμ(Aₖ) предполагает завершённое ⨆; у нас
        и объединение, и его мера — ПРОЦЕССЫ, а доказуемое ядро — сходимость
        монотонного ограниченного процесса частичных сумм.

    STATUS: 5 Qed, 0 Admitted, uses classic (L3) — σ-add ⇔ monotone limit, no NEW axiom
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The partial-measure process:  Sₙ = Σ_{k<n} μ(Aₖ)                      *)
(* ===================================================================== *)

Definition partial_measure (mu : nat -> Q) : RealProcess := q_sum mu.

(** Finite additivity (one step): adding the n-th disjoint set adds μ(Aₙ). *)
Lemma partial_measure_additive : forall (mu : nat -> Q) (n : nat),
  partial_measure mu (S n) == partial_measure mu n + mu n.
Proof.
  intros mu n. unfold partial_measure. cbn [q_sum]. reflexivity.
Qed.

(** Nonnegative measures ⇒ the partial-measure process is monotone increasing. *)
Lemma partial_measure_monotone : forall (mu : nat -> Q),
  (forall k, 0 <= mu k) ->
  monotone_increasing (partial_measure mu).
Proof.
  intros mu Hnn. unfold monotone_increasing, partial_measure. intro n.
  cbn [q_sum].
  assert (E : q_sum mu n == q_sum mu n + 0) by ring.
  rewrite E at 1.
  apply Qplus_le_compat; [ apply Qle_refl | apply Hnn ].
Qed.

(** Monotonicity of measure: more sets ⇒ at least as much measure (n ≤ m). *)
Lemma partial_measure_le : forall (mu : nat -> Q),
  (forall k, 0 <= mu k) ->
  forall m n, (n <= m)%nat -> partial_measure mu n <= partial_measure mu m.
Proof.
  intros mu Hnn m. unfold partial_measure. induction m as [|m IH]; intros n Hnm.
  - assert (Hn0 : n = 0%nat) by lia. subst. apply Qle_refl.
  - destruct (Nat.eq_dec n (S m)) as [->|Hne].
    + apply Qle_refl.
    + assert (Hnm' : (n <= m)%nat) by lia.
      apply Qle_trans with (q_sum mu m).
      * apply IH; exact Hnm'.
      * cbn [q_sum].
        assert (E : q_sum mu m == q_sum mu m + 0) by ring.
        rewrite E at 1.
        apply Qplus_le_compat; [ apply Qle_refl | apply Hnn ].
Qed.

(* ===================================================================== *)
(*  MAIN: σ-additivity (process core).                                    *)
(*  A nonneg measure with finite total mass has a CONVERGENT (Cauchy)     *)
(*  partial-sum process — Σₖ μ(Aₖ) converges to μ(⨆ₖ Aₖ).                *)
(* ===================================================================== *)

Theorem sigma_additive_converges : forall (mu : nat -> Q) (B : Q),
  (forall k, 0 <= mu k) ->                  (* each piece has nonneg measure *)
  (forall n, partial_measure mu n <= B) ->  (* finite total mass B           *)
  is_Cauchy (partial_measure mu).
Proof.
  intros mu B Hnn Hbnd.
  apply monotone_bounded_Cauchy with (ub := B).
  - apply partial_measure_monotone; exact Hnn.
  - exact Hbnd.
Qed.

(* Computational sanity: three disjoint sets each of measure 2 sum to 6. *)
Example sigma_finite_additivity : partial_measure (fun _ => 2) (3%nat) = 6.
Proof. reflexivity. Qed.

Print Assumptions sigma_additive_converges.
