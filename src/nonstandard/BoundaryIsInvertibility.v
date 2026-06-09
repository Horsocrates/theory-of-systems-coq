(** * BoundaryIsInvertibility.v — A2 направления: ДВА атласа проекта = ОДНА обратимость.
      Element-сторона = ЕДИНИЦЫ кольца — целочисленные матрицы det ±1 (редукционный атлас) И germ-процессы
      в-конце-ненулевые (A1).  role-limit = НЕ-единицы (делители нуля).  Граница = обратимость, на обеих сторонах.

   КОНТЕКСТ.  A1 (UnitZeroDivisorBoundary) показал: граница = обратимость germ-кольца (единица ⟺ в-конце-ненулев,
   делитель ⟺ нуль-множество кофинально).  Редукционный атлас (H73–H78) показал: пять движков рациональности =
   пять координат одной 2×2 матрицы, а Element-сторона держится на УНИМОДУЛЯРНОМ det ±1.  ЗДЕСЬ замыкается мост:
   det ±1 = ЕДИНИЦА целочисленной матрицы (обратимость над ℤ) — ТА ЖЕ обратимость, что germ-единицы A1.
   Два атласа проекта (Element=атлас единиц ⊕ role-limit=синтез XVIII делителей) суть два полюса инвертируемости.

   ★ ЕДИНИЦА ЦЕЛОЧИСЛЕННОЙ МАТРИЦЫ ⟺ det ±1 (genuine, доказано):
     (⟹) обратима ⟹ det·det⁻¹=1 в ℤ ⟹ det=±1 (det мультипликативна);
     (⟸) det=±1 ⟹ явный целочисленный обратный (adj при det=1, −adj при det=−1).
   Анкеры: fib-генератор (1 1;0 1) (det 1) ОБРАТИМ; масштаб (2 0;0 1) (det 2) НЕОБРАТИМ.

   ★ МОСТ К A1: germ-процесс-константа gconst q (q≠0) — ЕДИНИЦА germ-кольца (обратный gconst (/q)).
   Element-сторона = единицы НА ОБЕИХ аренах (матрицы det±1 ⊕ germ в-конце-ненулев).

   ★ КОНСТРУКТИВНО (0 аксиом).  det мультипликативна (ring); обратный матрицы выписан явно (adj/−adj);
   germ-обратный явен (gconst (/q)).  Никакой classic.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  det ±1 ⟺ обратимость — доказано здесь (переказ Element-стороны
   атласа на язык единиц кольца).  ⚠ Полная связь со ВСЕМИ пятью движками атласа (H78) — цитата; здесь — unit-ядро
   (det ±1) + germ-мост (gconst).  «role-limit = не-единицы» — цитата к A1 (even_ind делитель) / синтезу XVIII.

   Elements: Mat2/det2/mul2/invertible2 (над ℤ); germ gconst/g_unit (над ℚ); fib_gen/scale2.
   Roles:    det±1=роль-единица-матрицы; обратимость=Element-маркер на обеих сторонах; не-единица=role-limit-маркер.
   Rules:    invertible2 ⟺ det±1; gconst q единица ⟺ q≠0; обе стороны Element = единицы кольца.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: два атласа = одна обратимость; Element=единицы (матрицы det±1 ⊕ germ в-конце-ненулев).
     Rules (L5): invertible2 M ⟺ det2 M=±1 (явный обратный adj/−adj); gconst q единица ⟺ q≠0; обе = unit кольца.
     Roles (L4): det±1=роль-единица-матрицы; обратимость=Element-маркер; не-единица=role-limit-маркер.
     Elements  : Mat2/det2/mul2/invertible2; germ gconst/g_unit; fib_gen (det1), scale2 (det2).
     ОБРАЗУЮЩИЕ: редукционный атлас (H73–78, det±1, цитата+переказ); A1 UnitZeroDivisorBoundary (germ-единицы);
                 синтез XVIII (role-limit=делители, цитата).
     ВЛОЖЕННЫЕ : матричная единица (det±1) ↔ germ-единица (в-конце-ненулев) — одна обратимость.
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (целочисленная матрица): Elements — 4 числа; Roles — линейное преобразование;
                 Rules — обратима над ℤ ⟺ det=±1 (единица).
   ДИАГНОСТИКА (P4): конструктивно (det мультипликативна ring; обратный adj/−adj явен; germ-обратный gconst(/q))
                 => 0 акс. ЧЕСТНО: связь со всеми 5 движками атласа = цитата; здесь unit-ядро + germ-мост.

   STATUS: 13 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.

(* ===================================================================== *)
(*  Целочисленные 2×2 матрицы: Element-сторона атласа = единицы (det ±1)    *)
(* ===================================================================== *)

Open Scope Z_scope.

Record Mat2 := mk { m11 : Z; m12 : Z; m21 : Z; m22 : Z }.

Definition det2 (M : Mat2) : Z := m11 M * m22 M - m12 M * m21 M.

Definition mul2 (M N : Mat2) : Mat2 :=
  mk (m11 M * m11 N + m12 M * m21 N) (m11 M * m12 N + m12 M * m22 N)
     (m21 M * m11 N + m22 M * m21 N) (m21 M * m12 N + m22 M * m22 N).

Definition id2 : Mat2 := mk 1 0 0 1.
Definition adj (M : Mat2) : Mat2 := mk (m22 M) (- m12 M) (- m21 M) (m11 M).
Definition negadj (M : Mat2) : Mat2 := mk (- m22 M) (m12 M) (m21 M) (- m11 M).

Definition invertible2 (M : Mat2) : Prop := exists N, mul2 M N = id2 /\ mul2 N M = id2.

(** det мультипликативна (ядро направления (⟹)). *)
Lemma det_mult : forall M N, det2 (mul2 M N) = det2 M * det2 N.
Proof. intros [a b c d] [e f g h]. unfold det2, mul2. simpl. ring. Qed.

(** M·adj(M) = det·I (адъюгат). *)
Lemma mul2_M_adj : forall M, mul2 M (adj M) = mk (det2 M) 0 0 (det2 M).
Proof. intros [a b c d]. unfold mul2, adj, det2. simpl. f_equal; ring. Qed.
Lemma mul2_adj_M : forall M, mul2 (adj M) M = mk (det2 M) 0 0 (det2 M).
Proof. intros [a b c d]. unfold mul2, adj, det2. simpl. f_equal; ring. Qed.
Lemma mul2_M_negadj : forall M, mul2 M (negadj M) = mk (- det2 M) 0 0 (- det2 M).
Proof. intros [a b c d]. unfold mul2, negadj, det2. simpl. f_equal; ring. Qed.
Lemma mul2_negadj_M : forall M, mul2 (negadj M) M = mk (- det2 M) 0 0 (- det2 M).
Proof. intros [a b c d]. unfold mul2, negadj, det2. simpl. f_equal; ring. Qed.

(** Целочисленные единицы: a·b = 1 ⟹ a = ±1 (через |a|·|b|=1 и Nat.mul_eq_1). *)
Lemma Z_mul_one : forall a b : Z, a * b = 1 -> a = 1 \/ a = -1.
Proof.
  intros a b H.
  assert (Habs : Z.abs a * Z.abs b = 1).
  { rewrite <- Z.abs_mul, H. reflexivity. }
  assert (Hna : (Z.to_nat (Z.abs a) * Z.to_nat (Z.abs b) = 1)%nat).
  { rewrite <- Z2Nat.inj_mul by apply Z.abs_nonneg. rewrite Habs. reflexivity. }
  apply Nat.mul_eq_1 in Hna. destruct Hna as [Hna _].
  assert (Ha1 : Z.abs a = 1).
  { rewrite <- (Z2Nat.id (Z.abs a)) by apply Z.abs_nonneg. rewrite Hna. reflexivity. }
  destruct (Z.le_gt_cases 0 a) as [Hpos | Hneg].
  - left. rewrite Z.abs_eq in Ha1 by assumption. exact Ha1.
  - right. rewrite Z.abs_neq in Ha1 by lia. lia.
Qed.

(** ⟹ : обратима ⟹ det = ±1 (det·det⁻¹ = 1 в ℤ). *)
Lemma invertible_det_pm1 : forall M, invertible2 M -> det2 M = 1 \/ det2 M = -1.
Proof.
  intros M [N [HMN _]].
  assert (Hd : det2 M * det2 N = 1).
  { rewrite <- det_mult. rewrite HMN. reflexivity. }
  apply (Z_mul_one (det2 M) (det2 N) Hd).
Qed.

(** ⟸ : det = ±1 ⟹ обратима (явный целочисленный обратный). *)
Lemma det_pm1_invertible : forall M, det2 M = 1 \/ det2 M = -1 -> invertible2 M.
Proof.
  intros M [H1 | Hm1].
  - exists (adj M). split.
    + rewrite mul2_M_adj, H1. reflexivity.
    + rewrite mul2_adj_M, H1. reflexivity.
  - exists (negadj M). split.
    + rewrite mul2_M_negadj, Hm1. reflexivity.
    + rewrite mul2_negadj_M, Hm1. reflexivity.
Qed.

(** ★ ЕДИНИЦА целочисленной матрицы ⟺ det ±1. *)
Lemma det_pm1_iff_invertible : forall M, invertible2 M <-> det2 M = 1 \/ det2 M = -1.
Proof.
  intro M. split; [ apply invertible_det_pm1 | apply det_pm1_invertible ].
Qed.

(** Анкеры: унимодулярный генератор обратим; det-2 — нет. *)
Definition fib_gen : Mat2 := mk 1 1 0 1.
Definition scale2 : Mat2 := mk 2 0 0 1.

Lemma fib_gen_invertible : invertible2 fib_gen.
Proof. apply det_pm1_invertible. left. reflexivity. Qed.

Lemma scale2_not_invertible : ~ invertible2 scale2.
Proof.
  intro H. apply invertible_det_pm1 in H.
  destruct H as [H | H]; vm_compute in H; discriminate.
Qed.

(* ===================================================================== *)
(*  Мост к A1: germ-процесс-константа (q≠0) = единица germ-кольца           *)
(* ===================================================================== *)

Open Scope Q_scope.

Definition GProc : Type := nat -> Q.
Definition geq (x y : GProc) : Prop := exists N, forall n, (N <= n)%nat -> x n == y n.
Definition gmul (x y : GProc) : GProc := fun n => x n * y n.
Definition gconst (q : Q) : GProc := fun _ => q.
Definition g_unit (x : GProc) : Prop := exists y, geq (gmul x y) (gconst 1).

(** ★ Element-процесс gconst q (q≠0) — ЕДИНИЦА germ-кольца (обратный gconst (/q)). *)
Lemma gconst_unit : forall q, ~ q == 0 -> g_unit (gconst q).
Proof.
  intros q Hq. exists (gconst (/ q)). exists 0%nat. intros n _.
  unfold gmul, gconst. apply Qmult_inv_r. exact Hq.
Qed.

(* ===================================================================== *)
(*  Капстоун: два атласа — одна обратимость                                 *)
(* ===================================================================== *)

(** ★ Два атласа проекта = ОДНА обратимость (0 аксиом):
      (атлас)      обратима ⟺ det ±1 — Element-сторона редукционного атласа = единицы SL₂(ℤ);
      (унимодуляр) fib-генератор (1 1;0 1) обратим;
      (не-единица) масштаб (2 0;0 1), det 2, НЕОБРАТИМ;
      (germ)       Element-процесс gconst q (q≠0) — единица germ-кольца.
    Element = единицы кольца на обеих аренах (матрицы det±1 ⊕ germ в-конце-ненулев, A1);
    role-limit = не-единицы (делители нуля, A1/синтез XVIII).  Граница = обратимость. *)
Theorem two_atlases_one_invertibility :
  (forall M, invertible2 M <-> (det2 M = 1 \/ det2 M = -1)%Z)
  /\ invertible2 fib_gen
  /\ ~ invertible2 scale2
  /\ (forall q, ~ q == 0 -> g_unit (gconst q)).
Proof.
  split; [ exact det_pm1_iff_invertible |].
  split; [ exact fib_gen_invertible |].
  split; [ exact scale2_not_invertible | exact gconst_unit ].
Qed.
