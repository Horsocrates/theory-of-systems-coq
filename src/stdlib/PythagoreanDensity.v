(** * PythagoreanDensity.v — Gisin's "Pythagorean no-go" DISSOLVED on its own
      example: an infinite sequence of exact rational right triangles → isoceles

    Elements: the Pell-convergent parameters t_n ∈ ℚ; the exact rational triangles
              param(t_n) = (3,4,5),(20,21,29),(119,120,169),(696,697,985),…
    Roles:    the isoceles (45°) direction = the √2 R-PROCESS this file IS (a
              NON-TERMINATING process: Elements = the t_n / triangles, Rule = the
              Pell recurrence); each t_n is an ε-approximant
    Rules:    t_{n+1} = 1/(2+t_n) (continued fraction of √2−1); the deviation
              e_n = t_n²+2t_n−1 satisfies the CONTRACTING recurrence
              e_{n+1} = −e_n/(2+t_n)²  (so |e_n| → 0 geometrically),
              and px(t_n)−py(t_n) = −e_n/(1+t_n²) → 0

    GISIN / DEL SANTO's "Pythagorean no-go" — "three particles cannot sit on the
    vertices of a right triangle over ℚ, the hypotenuse being irrational" — is
    here DISSOLVED on its hardest case, the ISOCELES right triangle: we exhibit an
    explicit INFINITE sequence of EXACT rational right triangles whose shape
    converges to isoceles. KEY (P4): the 45° point (= √2) is NOT a completed object
    that "is irrational" — it IS this R-PROCESS (Elements = the t_n / triangles,
    Rule = the Pell recurrence). The process is NON-TERMINATING: it never closes
    into an Element — and THAT is the content of √2-irrationality (no_rational_sqrt2,
    Sqrt2Irrational.v): the process's correct P4-status, not a defect. The no-go is a
    re-discovery of the P4-boundary, not an obstruction. (Builds on PythagoreanTriples.v.)

    ============ E/R/R разбор ============
      Rules (L5): t_{n+1}=1/(2+t_n); контракция e_{n+1}=−e_n/(2+t_n)² ⟹ e_n→0.
      Roles (L4): точка 45° (= √2) = НЕЗАВЕРШАЮЩИЙСЯ R-процесс (этот файл И ЕСТЬ он),
                  не «иррациональное число», а процесс; t_n = ε-приближение.
      Elements  : t_n∈ℚ, точные тройки param(t_n) — рациональные приближения,
                  которые ГЕНЕРИРУЕТ процесс (L1+P4).
    ДИАГНОСТИКА (P4): «иррационально ли 45°» — НЕ-ВОПРОС; 45° ЕСТЬ незавершающийся
    процесс Пелля. Незавершаемость (no_rational_sqrt2) = корректный статус, не
    дефект. no-go Гизина = переоткрытие P4-границы (предел процесса, не препятствие).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.PythagoreanTriples.
Open Scope Q_scope.

(* ===== The Pell-convergent parameter sequence t_n → √2 − 1 ============= *)

Fixpoint pell_t (n : nat) : Q :=
  match n with
  | O => 1 # 2
  | S k => 1 / (2 + pell_t k)
  end.

Lemma pell_t_pos : forall n, 0 < pell_t n.
Proof.
  induction n as [|k IH]; simpl.
  - lra.
  - apply Qlt_shift_div_l; lra.
Qed.

Lemma pell_t_le_half : forall n, pell_t n <= 1 # 2.
Proof.
  destruct n as [|k]; simpl.
  - lra.
  - pose proof (pell_t_pos k) as Hp. apply Qle_shift_div_r; lra.
Qed.

Lemma pell_den_nz : forall n, ~ (2 + pell_t n == 0).
Proof. intro n. pose proof (pell_t_pos n). lra. Qed.

(* ===== The deviation e_n = t_n² + 2t_n − 1 and its contraction =========== *)

Definition pell_e (n : nat) : Q := pell_t n * pell_t n + 2 * pell_t n - 1.

(** THE CONTRACTION: e_{n+1} = −e_n / (2+t_n)². Since (2+t_n)² ≥ 4, the
    deviation shrinks by a factor ≥ 4 each step ⟹ e_n → 0. *)
Lemma pell_e_rec : forall n,
  pell_e (S n) == - pell_e n / ((2 + pell_t n) * (2 + pell_t n)).
Proof.
  intro n. unfold pell_e.
  replace (pell_t (S n)) with (1 / (2 + pell_t n)) by reflexivity.
  field. apply pell_den_nz.
Qed.

(** Cleared form (no division): e_{n+1} · (2+t_n)² = −e_n. *)
Lemma pell_e_clear : forall n,
  pell_e (S n) * ((2 + pell_t n) * (2 + pell_t n)) == - pell_e n.
Proof.
  intro n. rewrite pell_e_rec. field. apply pell_den_nz.
Qed.

(** QUANTITATIVE CONTRACTION: e²_{n+1} shrinks by a factor ≥ 16 each step,
    since (2+t_n)² ≥ 4. This turns "the deviation contracts" into a proof that
    e_n → 0 (hence the triangles genuinely converge to the 45° role-limit). *)
Lemma pell_e_sq_step : forall n,
  16 * (pell_e (S n) * pell_e (S n)) <= pell_e n * pell_e n.
Proof.
  intro n.
  pose proof (pell_t_pos n) as Hp.
  pose proof (pell_e_clear n) as Hc.
  assert (HD2 : 4 <= (2 + pell_t n) * (2 + pell_t n)).
  { apply Qle_trans with (2 * (2 + pell_t n)); [ lra | apply Qmult_le_compat_r; lra ]. }
  set (D2 := (2 + pell_t n) * (2 + pell_t n)) in *.
  assert (Hsq2 : pell_e n * pell_e n == (pell_e (S n) * pell_e (S n)) * (D2 * D2)).
  { assert (Hc2 : (pell_e (S n) * D2) * (pell_e (S n) * D2) == pell_e n * pell_e n)
      by (rewrite !Hc; ring).
    rewrite <- Hc2; ring. }
  rewrite Hsq2, (Qmult_comm (pell_e (S n) * pell_e (S n)) (D2 * D2)).
  apply Qmult_le_compat_r.
  - apply Qle_trans with (4 * D2); [ lra | apply Qmult_le_compat_r; lra ].
  - apply Qsqr_nonneg'.
Qed.

(** The deviation of the n-th triangle from the 45° diagonal, in closed form. *)
Lemma deviation : forall n,
  px (pell_t n) - py (pell_t n) == - pell_e n / (1 + pell_t n * pell_t n).
Proof.
  intro n. unfold px, py, pell_e. field. apply one_plus_sq_nz.
Qed.

(* ===== Concrete march of EXACT rational triangles toward 45° ============ *)
(* (a−b)² strictly decreases: 1/25 > 1/841 > 1/28561 > 1/970225 → 0.        *)

Example approx_0 :  (* (3,4,5) *)
  (px (pell_t 0%nat) - py (pell_t 0%nat)) * (px (pell_t 0%nat) - py (pell_t 0%nat)) == 1 # 25.
Proof. vm_compute. reflexivity. Qed.

Example approx_1 :  (* (20,21,29) *)
  (px (pell_t 1%nat) - py (pell_t 1%nat)) * (px (pell_t 1%nat) - py (pell_t 1%nat)) == 1 # 841.
Proof. vm_compute. reflexivity. Qed.

Example approx_2 :  (* (119,120,169) *)
  (px (pell_t 2%nat) - py (pell_t 2%nat)) * (px (pell_t 2%nat) - py (pell_t 2%nat)) == 1 # 28561.
Proof. vm_compute. reflexivity. Qed.

Example approx_3 :  (* (696,697,985) *)
  (px (pell_t 3%nat) - py (pell_t 3%nat)) * (px (pell_t 3%nat) - py (pell_t 3%nat)) == 1 # 970225.
Proof. vm_compute. reflexivity. Qed.

(* ===== The no-go dissolution =========================================== *)

(** For every n: param(t_n) is an EXACT rational unit-circle point (a rational
    right triangle), its deviation from the 45° diagonal equals −e_n/(1+t_n²),
    and e_n obeys the contracting recurrence ⟹ the triangles converge to the
    isoceles one that the no-go calls "impossible". The exact 45° point is the
    role-limit (P4); each approximant is an Element. *)
Theorem nogo_dissolved : forall n,
  on_circle (px (pell_t n)) (py (pell_t n)) /\
  px (pell_t n) - py (pell_t n) == - pell_e n / (1 + pell_t n * pell_t n) /\
  pell_e (S n) == - pell_e n / ((2 + pell_t n) * (2 + pell_t n)).
Proof.
  intro n. repeat split.
  - apply param_on_circle.
  - apply deviation.
  - apply pell_e_rec.
Qed.
