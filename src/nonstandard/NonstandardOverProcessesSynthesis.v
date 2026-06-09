(** * NonstandardOverProcessesSynthesis.v — КАПСТОУН Части XVIII: ОДНО структурное свойство
      (undecided S: и S, и not-S кофинальны) ПОРОЖДАЕТ ТРИ алгебраические формы role-limit-зазора —
      делитель нуля (×), осциллятор-без-тени (+), необратимость (кольцо).  Один зазор, три формы.

   СИНТЕЗ.  Часть XVIII построила: germ-кольцо + δ (GermInfinitesimal), тень st (StandardPart),
   germ-не-поле (UltrafilterRoleLimit), производную и интеграл через st (Derivative/HyperfiniteSum),
   вердикт-реестр (IllusoryConstructions).  ЗДЕСЬ извлекается ЕДИНЫЙ КОРЕНЬ всех role-limit-явлений:
   неразрешённость Фреше «какое подмножество велико».  Абстрагируем от частного Evens (UltrafilterRoleLimit,
   StandardPart) к ОБЩЕМУ undecided S и доказываем, что ОДНО это свойство даёт ВСЕ три формы.

   ★ ЕДИНЫЙ КОРЕНЬ (genuine унифицирующая теорема, не повтор).  undecided S (и S, и not-S истинны
   бесконечно часто — Фреше их не различает) ВЛЕЧЁТ:
     (× мультипликативно)  ind S · ind not-S ~ 0, но ни ind S, ни ind not-S не ~ 0 — ДЕЛИТЕЛЬ НУЛЯ;
     (+ аддитивно)         osc S = (ind S − ind not-S) НЕ имеет константной тени — ОСЦИЛЛЯТОР;
     (кольцо)              ind S НЕОБРАТИМ — НЕ-ЕДИНИЦА.
   Три алгебраические формы (×, +, кольцо) одного зазора.  Evens — лишь частный undecided.

   ★ КОНСТРУКТИВНО (0 аксиом, важно).  undecided определён ПОЗИТИВНО (cofinal S /\ cofinal not-S =
   «оба истинны бесконечно часто»), НЕ через двойное отрицание (~cofinite ... — потребовало бы classic/DNE).
   Поэтому все три формы выводятся БЕЗ аксиомы classic — чистая Element-сторона.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  ⚠ Это СИНТЕЗ / УНИФИКАЦИЯ — абстрагирование Evens-результатов
   (UltrafilterRoleLimit/StandardPart) к общему undecided + доказательство, что ОДНО свойство даёт три формы.
   Genuine содержание = унификация (один корень → три формы) машинно.  «Исчисление = одна операция st»
   (f'=st(Δf/δ), ∫=st(Σfδ)) и трёхзначный вердикт {Element/role-limit/illusory} — установлены в файлах Части
   XVIII (Derivative/HyperfiniteSum/IllusoryConstructions), здесь ЦИТИРУЮТСЯ, не передоказываются.

   Elements: GProc; cofinal/undecided (позитивные); ind/osc; evens; geq/gmul/gconst.
   Roles:    undecided=роль-неразрешённое-различение; ind=индикатор; osc=осциллятор; делитель/тень/единица=формы.
   Rules:    undecided S => делитель нуля (×) + осциллятор-без-тени (+) + необратимость (кольцо); один корень.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: ОДНО свойство undecided S порождает ТРИ алгебраические формы role-limit-зазора.
     Rules (L5): undecided S => (a) делитель нуля; (b) осциллятор без тени; (c) необратимость. Один зазор, три формы.
     Roles (L4): undecided=неразрешённое различение; ind=индикатор; osc=осциллятор; делитель/тень/единица=проявления.
     Elements  : GProc; cofinal/undecided (позитивные, конструктивные); ind/osc; evens; geq/gmul/gconst.
     ОБРАЗУЮЩИЕ: UltrafilterRoleLimit (делитель нуля, Evens-частность); StandardPart (osc=alt без тени);
                 GermInfinitesimal (germ-кольцо); Derivative/HyperfiniteSum (исчисление=st, цитата);
                 IllusoryConstructions (вердикт, цитата).
     ВЛОЖЕННЫЕ : три формы одного зазора; Evens = частный undecided.
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (undecided S): Elements — S и not-S оба кофинальны; Roles — неразрешённое различение;
                 Rules — ни одно конечное наблюдение не решает «что велико» => требует внешнего L5/ультрафильтра =>
                 КОРЕНЬ всех трёх форм.
   ДИАГНОСТИКА (P4): всё конструктивно (позитивный undecided, без classic) => 0 акс; единственный role-limit —
                 разрешение undecided (ультрафильтр), НЕ ассертим. ЧЕСТНО: синтез/унификация; исчисление=st и
                 вердикт — цитаты к файлам XVIII.

   STATUS: 10 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  germ-процессы (реплицировано) + позитивное «неразрешённое различение»  *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.
Definition geq (x y : GProc) : Prop := exists N, forall n, (N <= n)%nat -> x n == y n.
Definition gmul (x y : GProc) : GProc := fun n => x n * y n.
Definition gconst (q : Q) : GProc := fun _ => q.
Definition g_invertible (x : GProc) : Prop := exists y, geq (gmul x y) (gconst 1).

(** S истинно бесконечно часто (позитивно — конструктивно, без classic). *)
Definition cofinal (S : nat -> bool) : Prop := forall N, exists n, (N <= n)%nat /\ S n = true.

(** ★ Неразрешённое различение: и S, и not-S истинны бесконечно часто (Фреше не решает «что велико»). *)
Definition undecided (S : nat -> bool) : Prop := cofinal S /\ cofinal (fun n => negb (S n)).

Definition ind (S : nat -> bool) : GProc := fun n => if S n then 1 else 0.
Definition osc (S : nat -> bool) : GProc := fun n => if S n then 1 else Qopp 1.

Definition evens (n : nat) : bool := Nat.even n.

(* ===================================================================== *)
(*  Evens — каноническое неразрешённое различение                          *)
(* ===================================================================== *)

Lemma cofinal_evens : cofinal evens.
Proof.
  intro N. exists (2 * N)%nat. split; [ lia |].
  unfold evens. replace (2 * N)%nat with (0 + 2 * N)%nat by lia.
  rewrite Nat.even_add_mul_2. reflexivity.
Qed.

Lemma cofinal_odds : cofinal (fun n => negb (evens n)).
Proof.
  intro N. exists (2 * N + 1)%nat. split; [ lia |].
  unfold evens. replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
  rewrite Nat.even_add_mul_2. reflexivity.
Qed.

Lemma undecided_evens : undecided evens.
Proof. split; [ exact cofinal_evens | exact cofinal_odds ]. Qed.

(* ===================================================================== *)
(*  ★ Форма ×: делитель нуля                                                *)
(* ===================================================================== *)

(** ind S · ind not-S = 0 поточечно (никакое n не в S И в not-S). *)
Lemma ind_complement_product_zero :
  forall S, geq (gmul (ind S) (ind (fun n => negb (S n)))) (gconst 0).
Proof.
  intro S. exists 0%nat. intros n _. unfold gmul, ind, gconst.
  destruct (S n); simpl; ring.
Qed.

(** Если S кофинально, ind S НЕ ~ 0 (значение 1 бесконечно часто). *)
Lemma ind_not_zero : forall S, cofinal S -> ~ geq (ind S) (gconst 0).
Proof.
  intros S Hc [N HN]. destruct (Hc N) as [n [Hn Hs]].
  pose proof (HN n Hn) as A. unfold ind, gconst in A.
  rewrite Hs in A. simpl in A. lra.
Qed.

(** ★ undecided S => ДЕЛИТЕЛЬ НУЛЯ: произведение ~ 0, но ни один множитель не ~ 0. *)
Theorem undecided_zero_divisor : forall S, undecided S ->
  geq (gmul (ind S) (ind (fun n => negb (S n)))) (gconst 0)
  /\ ~ geq (ind S) (gconst 0)
  /\ ~ geq (ind (fun n => negb (S n))) (gconst 0).
Proof.
  intros S [HcS HcN]. split; [ apply ind_complement_product_zero |].
  split; [ apply ind_not_zero; exact HcS | apply ind_not_zero; exact HcN ].
Qed.

(* ===================================================================== *)
(*  ★ Форма +: осциллятор без тени                                          *)
(* ===================================================================== *)

Lemma osc_true : forall S n, S n = true -> osc S n = 1.
Proof. intros S n H. unfold osc. rewrite H. reflexivity. Qed.

Lemma osc_false : forall S n, S n = false -> osc S n = Qopp 1.
Proof. intros S n H. unfold osc. rewrite H. reflexivity. Qed.

(** ★ undecided S => осциллятор osc S НЕ имеет константной тени (значения +1 и −1 бесконечно часто). *)
Theorem undecided_no_shadow : forall S, undecided S -> ~ exists L, geq (osc S) (gconst L).
Proof.
  intros S [HcS HcN] [L [N HN]].
  destruct (HcS N) as [n1 [H1 Hs1]].
  destruct (HcN N) as [n2 [H2 Hs2]].
  assert (Hf2 : S n2 = false).
  { destruct (S n2). - simpl in Hs2. discriminate. - reflexivity. }
  pose proof (HN n1 H1) as A. pose proof (HN n2 H2) as B.
  unfold gconst in A, B.
  rewrite (osc_true S n1 Hs1) in A. rewrite (osc_false S n2 Hf2) in B.
  lra.
Qed.

(* ===================================================================== *)
(*  ★ Форма кольцо: необратимость                                           *)
(* ===================================================================== *)

(** ★ undecided S => ind S НЕОБРАТИМ (обратный был бы 1/0 на not-S, кофинальном). *)
Theorem undecided_non_unit : forall S, undecided S -> ~ g_invertible (ind S).
Proof.
  intros S [HcS HcN] [y [N HN]].
  destruct (HcN N) as [n [Hn Hneg]].
  assert (Hf : S n = false).
  { destruct (S n). - simpl in Hneg. discriminate. - reflexivity. }
  pose proof (HN n Hn) as A. unfold gmul, ind, gconst in A.
  rewrite Hf in A. simpl in A. rewrite Qmult_0_l in A. lra.
Qed.

(* ===================================================================== *)
(*  Капстоун: один зазор — три формы                                        *)
(* ===================================================================== *)

(** ★ Синтез Части XVIII (0 аксиом): ОДНО неразрешённое различение undecided S порождает ТРИ
    алгебраические формы role-limit-зазора:
      (Evens)       evens — каноническое неразрешённое различение;
      (× делитель)  ind S · ind not-S ~ 0, но ни один не ~ 0;
      (+ осциллятор) osc S не имеет константной тени;
      (кольцо)      ind S необратим.
    Все три — проявления ОДНОГО корня: Фреше не решает «какое подмножество велико» (= role-limit,
    разрешается лишь внешним ультрафильтром).  Конструктивно (позитивный undecided, без classic).
    Цитаты к Части XVIII: исчисление = одна операция st (Derivative/HyperfiniteSum); трёхзначный вердикт
    {Element/role-limit/illusory} (IllusoryConstructions). *)
Theorem nonstandard_synthesis :
  undecided evens
  /\ (forall S, undecided S ->
        geq (gmul (ind S) (ind (fun n => negb (S n)))) (gconst 0)
        /\ ~ geq (ind S) (gconst 0))
  /\ (forall S, undecided S -> ~ exists L, geq (osc S) (gconst L))
  /\ (forall S, undecided S -> ~ g_invertible (ind S)).
Proof.
  split; [ exact undecided_evens |].
  split.
  - intros S HS. split.
    + apply ind_complement_product_zero.
    + apply ind_not_zero. exact (proj1 HS).
  - split; [ exact undecided_no_shadow | exact undecided_non_unit ].
Qed.
