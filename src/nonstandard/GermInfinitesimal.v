(** * GermInfinitesimal.v — бесконечно малое как ПРОЦЕСС: germ-кольцо ℚ^ℕ/Фреше
      (пилот Части XVIII «Нестандартный анализ над процессами»; Element-ядро, БЕЗ ультрафильтра).

   Нестандартный анализ строит гипердействительные `*ℝ = ℚ^ℕ / U` через неглавный ультрафильтр U
   (role-limit: завершённый выбор на 2^ℕ).  ЗДЕСЬ — Element-ЯДРО: фактор по фильтру ФРЕШЕ
   (ко-конечное = eventual-равенство), который КОНСТРУКТИВЕН.  Получается germ-КОЛЬЦО (с делителями нуля
   — НЕ поле; поле требует ультрафильтра).  Достаточно для исчисления ∞-малых (Шмиден–Лаугвиц, 1958, над
   процессами nat→ℚ).

   ★ ГЛАВНОЕ.  Бесконечно малое `δ = 1/(n+1)` — ПРОЦЕСС: НЕНУЛЕВО как germ (1/(n+1)≠0 всегда), ∞-МАЛО как
   роль (< всякого стандартного ε eventually).  «Парадокс» растворён: не завершённое число, а процесс;
   ненулевость = факт об элементах, ∞-малость = роль.  Обратное `ω = n+1` — ∞-большое, `ω·δ = 1`.

   ★★ СЛЕД ОТСУТСТВУЮЩЕГО УЛЬТРАФИЛЬТРА.  Кольцо имеет ДЕЛИТЕЛИ НУЛЯ: `even_ind·odd_ind ~ 0`, оба ≁ 0.
   Машинный след role-limit: ультрафильтр решил бы «чётные ИЛИ нечётные велики», сделав ровно один
   обратимым; без него оба ненулевые, произведение нулевое.  Неразрешённость = LPO-зазор.

   HONEST SCOPE.  0 аксиом.  Element-ядро (Фреше); ПОЛЕ `*ℝ`, полный Łoś, насыщенность = role-limit
   (ультрафильтр), НЕ здесь.  Традиция Шмиден–Лаугвиц / smooth infinitesimal; вклад ToS = над процессами +
   делители-нуля как след ультрафильтра + граница финитизации.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: germ-кольцо ℚ^ℕ/Фреше — ∞-малые как процессы, без ультрафильтра.
     Rules (L5): x~y ⟺ xₙ=yₙ при n≥N (Фреше); кольцо поточечно (конгруэнтно); роли по eventual-поведению.
     Roles (L4): germ-класс; ∞-малое/конечное/∞-большое (= bounded/unbounded); δ канон ∞-малого, ω=1/δ.
     Elements  : процессы nat→ℚ; δₙ=1/(n+1); ωₙ=n+1; индикаторы чёт/нечёт.
     ОБРАЗУЮЩИЕ: Фреше (ядро); CauchyReal; DynamicBoundaryFrontier (bounded/unbounded); arch_nat;
                 ультрафильтр (role-limit, НЕ берём).
     ВЛОЖЕННЫЕ : δ (∞-малое); ω (∞-большое); делители нуля even·odd (след ультрафильтра).
   ДИАГНОСТИКА (P4): ★ δ ненулево (элемент) + ∞-мало (роль) = парадокс растворён (процесс). ★★ делители
   нуля = след отсутствующего ультрафильтра (цена «кольцо, не поле» = LPO-зазор). Поле = role-limit.

   --- Разбор ЭЛЕМЕНТА-как-системы: δ (любой элемент сам есть система) ---
     Rules:   δ конституирован правилом порождения n↦1/(n+1) (архимедов спуск) — правило, не значение.
     Roles:   роль δ в кольце — ненулевой, но НЕобратимый; роль «< всякого стандартного ε».
     Elements: δₙ=1/(n+1)∈ℚ — конечно-актуальны; нет завершённого «∞-малого числа».
     P4: δ — полная E/R/R-система-процесс (правило-спуск + роль-∞-малость + элементы-рациональные).

   STATUS: 19 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia Arith.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Инфраструктура: архимед + обратные над Q                               *)
(* ===================================================================== *)

Lemma arch_nat : forall B : Q, exists n : nat, B < inject_Z (Z.of_nat n).
Proof.
  intro B. destruct (Qarchimedean B) as [p Hp]. exists (Pos.to_nat p).
  unfold inject_Z. rewrite positive_nat_Z. exact Hp.
Qed.

Lemma Qle_of_nat_le : forall a b : nat,
  (a <= b)%nat -> inject_Z (Z.of_nat a) <= inject_Z (Z.of_nat b).
Proof. intros a b H. rewrite <- Zle_Qle. apply (proj1 (Nat2Z.inj_le _ _)). exact H. Qed.

(** Реципрокное переворачивание неравенства: /a < b -> /b < a (для положительных). *)
Lemma Qinv_lt_swap : forall a b : Q, 0 < a -> 0 < b -> / a < b -> / b < a.
Proof.
  intros a b Ha Hb H.
  assert (Hab : 1 < a * b).
  { setoid_replace 1 with (a * / a) by (field; lra).
    apply (proj2 (Qmult_lt_l (/ a) b a Ha)). exact H. }
  apply (proj1 (Qmult_lt_l (/ b) a b Hb)).
  setoid_replace (b * / b) with 1 by (field; lra).
  setoid_replace (b * a) with (a * b) by ring.
  exact Hab.
Qed.

(** Деление положительных положительно. *)
Lemma Qdiv_pos : forall a b : Q, 0 < a -> 0 < b -> 0 < a / b.
Proof.
  intros a b Ha Hb.
  assert (Hinv : 0 < / b) by (apply Qinv_lt_0_compat; exact Hb).
  apply (proj2 (Qmult_lt_l 0 (/ b) a Ha)) in Hinv.
  rewrite Qmult_0_r in Hinv. unfold Qdiv. exact Hinv.
Qed.

(* ===================================================================== *)
(*  Процессы, germ-равенство (фильтр Фреше) и кольцевые операции            *)
(* ===================================================================== *)

Definition GProc := nat -> Q.

Definition geq (x y : GProc) : Prop := exists N, forall n, (N <= n)%nat -> x n == y n.

Definition gadd (x y : GProc) : GProc := fun n => x n + y n.
Definition gmul (x y : GProc) : GProc := fun n => x n * y n.
Definition gconst (c : Q) : GProc := fun _ => c.

Lemma geq_refl : forall x, geq x x.
Proof. intro x. exists O. intros n _. reflexivity. Qed.

Lemma geq_sym : forall x y, geq x y -> geq y x.
Proof. intros x y [N HN]. exists N. intros n Hn. symmetry. apply HN. exact Hn. Qed.

Lemma geq_trans : forall x y z, geq x y -> geq y z -> geq x z.
Proof.
  intros x y z [N1 H1] [N2 H2]. exists (Nat.max N1 N2). intros n Hn.
  rewrite H1 by lia. apply H2. lia.
Qed.

Lemma gadd_geq : forall x x' y y', geq x x' -> geq y y' -> geq (gadd x y) (gadd x' y').
Proof.
  intros x x' y y' [N1 H1] [N2 H2]. exists (Nat.max N1 N2). intros n Hn.
  unfold gadd. rewrite H1 by lia. rewrite H2 by lia. reflexivity.
Qed.

Lemma gmul_geq : forall x x' y y', geq x x' -> geq y y' -> geq (gmul x y) (gmul x' y').
Proof.
  intros x x' y y' [N1 H1] [N2 H2]. exists (Nat.max N1 N2). intros n Hn.
  unfold gmul. rewrite H1 by lia. rewrite H2 by lia. reflexivity.
Qed.

(* ===================================================================== *)
(*  Роли: бесконечно малое / конечное / бесконечно большое                  *)
(* ===================================================================== *)

Definition g_infinitesimal (x : GProc) : Prop :=
  forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> Qabs (x n) < eps.
Definition g_finite (x : GProc) : Prop :=
  exists B N, forall n, (N <= n)%nat -> Qabs (x n) <= B.
Definition g_infinite (x : GProc) : Prop :=
  forall B, exists N, forall n, (N <= n)%nat -> B < Qabs (x n).

(* ===================================================================== *)
(*  Канонические δ = 1/(n+1) и ω = n+1                                      *)
(* ===================================================================== *)

Definition Qsn (n : nat) : Q := inject_Z (Z.of_nat (S n)).

Lemma Qsn_pos : forall n, 0 < Qsn n.
Proof. intro n. unfold Qsn, Qlt. simpl. lia. Qed.

Lemma Qsn_nonzero : forall n, ~ Qsn n == 0.
Proof. intro n. apply Qnot_eq_sym, Qlt_not_eq, Qsn_pos. Qed.

Definition delta : GProc := fun n => / Qsn n.
Definition omega : GProc := fun n => Qsn n.

(** ★ δ ненулево как germ. *)
Lemma delta_nonzero : ~ geq delta (gconst 0).
Proof.
  intros [N HN]. specialize (HN N (le_n N)). unfold delta, gconst in HN.
  assert (Hpos : 0 < / Qsn N) by (apply Qinv_lt_0_compat, Qsn_pos).
  rewrite HN in Hpos. apply (Qlt_irrefl 0). exact Hpos.
Qed.

(** ★ δ бесконечно мало. *)
Lemma delta_infinitesimal : g_infinitesimal delta.
Proof.
  intros eps Heps. destruct (arch_nat (/ eps)) as [m Hm]. exists m. intros n Hn.
  unfold delta.
  assert (Hsn : 0 < Qsn n) by apply Qsn_pos.
  assert (Hinv : 0 < / Qsn n) by (apply Qinv_lt_0_compat; exact Hsn).
  rewrite Qabs_pos by (apply Qlt_le_weak; exact Hinv).
  assert (Hen : / eps < Qsn n).
  { apply Qlt_le_trans with (inject_Z (Z.of_nat m)). exact Hm.
    unfold Qsn. apply Qle_of_nat_le. lia. }
  apply (Qinv_lt_swap eps (Qsn n) Heps Hsn). exact Hen.
Qed.

(** ★ ω бесконечно велико. *)
Lemma omega_infinite : g_infinite omega.
Proof.
  intro B. destruct (arch_nat B) as [m Hm]. exists m. intros n Hn.
  unfold omega.
  assert (Hsn : 0 < Qsn n) by apply Qsn_pos.
  rewrite Qabs_pos by (apply Qlt_le_weak; exact Hsn).
  apply Qlt_le_trans with (inject_Z (Z.of_nat m)). exact Hm.
  unfold Qsn. apply Qle_of_nat_le. lia.
Qed.

(** ★ ω·δ = 1. *)
Lemma omega_delta_one : geq (gmul omega delta) (gconst 1).
Proof.
  exists O. intros n _. unfold gmul, omega, delta, gconst.
  apply Qmult_inv_r. apply Qsn_nonzero.
Qed.

(* ===================================================================== *)
(*  ★★ Делители нуля = след отсутствующего ультрафильтра                    *)
(* ===================================================================== *)

Definition even_ind : GProc := fun n => if Nat.even n then 1 else 0.
Definition odd_ind  : GProc := fun n => if Nat.even n then 0 else 1.

Lemma zero_divisors_exist :
  (~ geq even_ind (gconst 0)) /\ (~ geq odd_ind (gconst 0))
  /\ geq (gmul even_ind odd_ind) (gconst 0).
Proof.
  split; [| split].
  - intros [N HN]. specialize (HN (2 * N)%nat ltac:(lia)).
    unfold even_ind, gconst in HN.
    assert (He : Nat.even (2 * N) = true) by (rewrite Nat.even_mul; reflexivity).
    rewrite He in HN. simpl in HN. lra.
  - intros [N HN]. specialize (HN (2 * N + 1)%nat ltac:(lia)).
    unfold odd_ind, gconst in HN.
    assert (Ho : Nat.even (2 * N + 1) = false).
    { rewrite Nat.add_comm. rewrite Nat.even_add_mul_2. reflexivity. }
    rewrite Ho in HN. simpl in HN. lra.
  - exists O. intros n _. unfold gmul, even_ind, odd_ind, gconst.
    destruct (Nat.even n); ring.
Qed.

(* ===================================================================== *)
(*  Бесконечно малые образуют идеал                                         *)
(* ===================================================================== *)

Lemma infinitesimal_add : forall x y,
  g_infinitesimal x -> g_infinitesimal y -> g_infinitesimal (gadd x y).
Proof.
  intros x y Hx Hy eps Heps.
  destruct (Hx ((1#2) * eps) ltac:(lra)) as [N1 H1].
  destruct (Hy ((1#2) * eps) ltac:(lra)) as [N2 H2].
  exists (Nat.max N1 N2). intros n Hn. unfold gadd.
  apply Qle_lt_trans with (Qabs (x n) + Qabs (y n)).
  - apply Qabs_triangle.
  - apply Qlt_le_trans with ((1#2) * eps + (1#2) * eps).
    + apply Qplus_lt_le_compat.
      * apply H1. lia.
      * apply Qlt_le_weak. apply H2. lia.
    + lra.
Qed.

Lemma finite_times_infinitesimal : forall x y,
  g_finite x -> g_infinitesimal y -> g_infinitesimal (gmul x y).
Proof.
  intros x y [B [Nb HB]] Hy eps Heps.
  assert (HBpos : 0 < B + 1).
  { specialize (HB Nb (le_n Nb)). pose proof (Qabs_nonneg (x Nb)). lra. }
  assert (Hdiv : 0 < eps / (B + 1)) by (apply Qdiv_pos; [ exact Heps | exact HBpos ]).
  destruct (Hy (eps / (B + 1)) Hdiv) as [Ny Hy'].
  exists (Nat.max Nb Ny). intros n Hn. unfold gmul.
  rewrite Qabs_Qmult.
  apply Qle_lt_trans with ((B + 1) * Qabs (y n)).
  - apply Qmult_le_compat_r.
    + apply Qle_trans with B. apply HB. lia. lra.
    + apply Qabs_nonneg.
  - setoid_replace eps with ((B + 1) * (eps / (B + 1))) by (field; lra).
    apply (proj2 (Qmult_lt_l (Qabs (y n)) (eps / (B + 1)) (B + 1) HBpos)).
    apply Hy'. lia.
Qed.

(* ===================================================================== *)
(*  Капстоун                                                                *)
(* ===================================================================== *)

(** Бесконечно малое как ПРОЦЕСС — Element-ядро NSA (germ-кольцо ℚ^ℕ/Фреше):
      (★ δ)        δ=1/(n+1) НЕНУЛЕВО (элемент) и ∞-мало (роль) — парадокс растворён;
      (★ ω·δ=1)    ∞-большое ω=n+1, ω·δ=1;
      (★★ дел. 0)  делители нуля (even·odd~0, оба≠0) = след отсутствующего ультрафильтра;
      (идеал)      ∞-малые замкнуты по +, конечное×∞-малое=∞-малое.
    Поле *ℝ (тотальный порядок, полный перенос) = role-limit-замыкание через ультрафильтр — НЕ здесь. *)
Theorem germ_ring_infinitesimal_summary :
  g_infinitesimal delta
  /\ (~ geq delta (gconst 0))
  /\ g_infinite omega
  /\ geq (gmul omega delta) (gconst 1)
  /\ ((~ geq even_ind (gconst 0)) /\ (~ geq odd_ind (gconst 0))
        /\ geq (gmul even_ind odd_ind) (gconst 0)).
Proof.
  split; [ exact delta_infinitesimal |].
  split; [ exact delta_nonzero |].
  split; [ exact omega_infinite |].
  split; [ exact omega_delta_one | exact zero_divisors_exist ].
Qed.
