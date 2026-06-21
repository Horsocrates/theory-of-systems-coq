(** * WidthProcessKernel.v — ширина-как-ПРОЦЕСС: ∞-ширинное ядро (NTK/NNGP) есть role-limit
      конечно-ширинных рациональных ядер (закрывает горизонт F отчёта
      docs/AI-ProcessMath-vs-Infinity.md на СТРУКТУРНОМ уровне).

    Каталог AI #3–5 (Neal 1996 NNGP, Jacot 2018 NTK, mean-field): при ширине n→∞ ядро сети
    становится завершённым ∞-мерным объектом (детерминированное ядро / гауссовский процесс).
    ToS: ширина — это ПРОЦЕСС.  Ядро ширины n  Θ_n(x,y) = Σ_{i<n} φ_i(x)·φ_i(y)  (мономиальные
    признаки φ_i = ·^i) на каждой ширине ТОЧНО рационально (Element); ∞-ширинное ядро —
    role-limit: Θ_n строго растёт с n и НИКОГДА не достигает предела при конечной ширине
    (достигается лишь как процесс), а размерность признаков неограниченна (нет завершённого
    ядра-объекта = аксиома полноты = ¬P4, ср. ERRHilbertProcess).

    ============ E/R/R разбор ============
      Rules (L5): ширина n → размерность признаков; ядро = Gram-сумма Σ_{i<n} φ_i(x)φ_i(y);
        предел n→∞ = завершённое ∞-ширинное ядро (NTK/NNGP).
      Roles (L4): Θ_n — роль-величина (рациональная Gram-сумма) на каждой ширине; ∞-ширина = role-limit.
      Elements (L1+P4): φ_i(x)=x^i (rpow); конечная сумма (ksum); каждая ширина точна над ℚ.
    ДИАГНОСТИКА (P4): завершённое ∞-ширинное ядро реифицирует role-limit.  Θ_n строго растёт
      (Theta_grows) и Θ_n < ∞-предел ∀n (infinite_width_never_reached) — предел только как процесс;
      размерность неограниченна (width_unbounded), нет конечной ширины-завершения (¬P4, ERRHilbertProcess).
      Element = конечная ширина (точно); role-limit = ∞-ширина.
    ЧЕСТНАЯ СТЕНА: СТРУКТУРНАЯ граница ширина-как-процесс, НЕ архитектурно-специфичный NTK Жако;
      конкретное ядро — геометрическое (мономиальные признаки).  Связь: Neal NNGP / Jacot NTK =
      этот n→∞ роль-предел; обучение на конечной ширине = Element.  Самодостаточно (Stdlib), 0 аксиом.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ================================================================= *)
(*  Степень r^n без Qpower — несущая рекуррентность                    *)
(* ================================================================= *)

Fixpoint rpow (r : Q) (n : nat) : Q :=
  match n with O => 1 | S m => r * rpow r m end.

Lemma rpow_pos : forall r n, 0 < r -> 0 < rpow r n.
Proof.
  intros r n Hr. induction n as [| m IH]; simpl.
  - lra.
  - apply Qmult_lt_0_compat; assumption.
Qed.

(* ================================================================= *)
(*  Ядро ширины n:  Θ_n(x,y) = Σ_{i<n} (x·y)^i  (мономиальные признаки) *)
(* ================================================================= *)

Fixpoint ksum (r : Q) (n : nat) : Q :=
  match n with O => 0 | S m => rpow r m + ksum r m end.

Definition Theta (x y : Q) (n : nat) : Q := ksum (x * y) n.

(** Нулевая ширина — нулевое ядро. *)
Lemma Theta_zero_width : forall x y, Theta x y 0 == 0.
Proof. intros x y. reflexivity. Qed.

(** ELEMENT: конечная ширина даёт ТОЧНУЮ рациональную Gram-сумму.
    Θ_3(½,½) = Σ_{i<3}(¼)^i = 1 + ¼ + 1/16 = 21/16. *)
Lemma Theta_finite_exact : Theta (1#2) (1#2) 3 == 21 # 16.
Proof. vm_compute; reflexivity. Qed.

(** Θ_2(⅓,⅓) = 1 + 1/9 = 10/9. *)
Lemma Theta_finite_exact2 : Theta (1#3) (1#3) 2 == 10 # 9.
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  ДРУГАЯ ФОРМУЛА: закрытая форма конечно-ширинного ядра             *)
(* ================================================================= *)

(** (1 − r)·Θ_n = 1 − r^n  — конечно-ширинное ядро есть точная геометрическая частичная сумма. *)
Lemma ksum_geom : forall r n, (1 - r) * ksum r n == 1 - rpow r n.
Proof.
  intros r n. induction n as [| m IH]; simpl.
  - ring.
  - rewrite Qmult_plus_distr_r. rewrite IH. ring.
Qed.

(* ================================================================= *)
(*  ШИРИНА-ПРОЦЕСС: строгий рост и недостижимость ∞-предела (role-limit) *)
(* ================================================================= *)

(** Ширина-процесс строго растёт: Θ_{n+1} > Θ_n — ядро меняется с шириной, не финально
    при конечной ширине. *)
Lemma Theta_grows : forall x y n, 0 < x * y -> Theta x y n < Theta x y (S n).
Proof.
  intros x y n Hr. unfold Theta. simpl.
  assert (Hp : 0 < rpow (x * y) n) by (apply rpow_pos; exact Hr).
  lra.
Qed.

(** ∞-ширинное ядро = role-limit: НИКОГДА не достигается при конечной ширине.
    Кросс-умноженная форма Θ_n < 1/(1−xy):  Θ_n·(1−xy) < 1 (для 0 < xy < 1). *)
Lemma infinite_width_never_reached : forall x y n,
  0 < x * y -> x * y < 1 -> Theta x y n * (1 - x * y) < 1.
Proof.
  intros x y n Hr Hr1. unfold Theta.
  assert (Hp : 0 < rpow (x * y) n) by (apply rpow_pos; exact Hr).
  assert (Hg : (1 - x * y) * ksum (x * y) n == 1 - rpow (x * y) n) by (apply ksum_geom).
  rewrite Qmult_comm. rewrite Hg. lra.
Qed.

(** Размерность/ширина растёт за любой предел — нет завершённой ∞-ширины (ср. ERRHilbertProcess). *)
Lemma width_unbounded : forall B : nat, exists n : nat, (B < n)%nat.
Proof. intro B. exists (S B). lia. Qed.

(* ================================================================= *)
(*  CAPSTONE                                                          *)
(* ================================================================= *)

(** ★★★ ШИРИНА-КАК-ПРОЦЕСС — ГРАНИЦА Element ↔ role-limit:
      (Element)    конечная ширина → ТОЧНОЕ рациональное ядро (Θ_3(½,½)=21/16);
      (процесс)    ширина-процесс строго растёт (Θ_{n+1}>Θ_n);
      (role-limit) ∞-ширинное ядро никогда не достигается при конечной ширине (Θ_n·(1−xy)<1);
      (¬P4)        размерность признаков неограниченна (нет завершённого ядра-объекта).
    ∞-ширинное (NTK/NNGP) ядро — role-limit процесса конечно-ширинных рациональных ядер; не
    завершённый объект.  (СТРУКТУРНО; конкретное ядро — геометрическое.) *)
Theorem width_kernel_boundary :
  (Theta (1#2) (1#2) 3 == 21 # 16)
  /\ (forall x y n, 0 < x * y -> Theta x y n < Theta x y (S n))
  /\ (forall x y n, 0 < x * y -> x * y < 1 -> Theta x y n * (1 - x * y) < 1)
  /\ (forall B : nat, exists n : nat, (B < n)%nat).
Proof.
  split; [ exact Theta_finite_exact
         | split; [ exact Theta_grows
                  | split; [ exact infinite_width_never_reached | exact width_unbounded ] ] ].
Qed.

Print Assumptions width_kernel_boundary.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  9 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Ширина-как-процесс: конечная ширина → ТОЧНОЕ рациональное ядро (Element,   *)
(*  Theta_finite_exact = 21/16); закрытая форма (1−r)Θ_n=1−r^n (ksum_geom);    *)
(*  ширина-процесс строго растёт (Theta_grows); ∞-ширинное ядро никогда не     *)
(*  достигается при конечной ширине (infinite_width_never_reached) и           *)
(*  размерность неограниченна (width_unbounded) = role-limit (¬P4, ср.         *)
(*  ERRHilbertProcess).  Капстоун width_kernel_boundary.  Закрывает горизонт F  *)
(*  отчёта AI-ProcessMath СТРУКТУРНО (не архитектурный NTK).                    *)
(* ========================================================================= *)
