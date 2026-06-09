(** * UnitZeroDivisorBoundary.v — A1 направления «Порождающая структура границы»:
      граница финитизации = ОБРАТИМОСТЬ в germ-кольце.  Единица ⟺ в-конце-ненулев (Element);
      делитель нуля ⟺ нуль-множество кофинально (role-limit/undecided).  δ — единица, even_ind — делитель.

   КОНТЕКСТ.  Часть XVIII показала: undecided S порождает делитель нуля (×), осциллятор (+), не-единицу
   (кольцо).  ЗДЕСЬ извлекается дно: ВСЯ граница финитизации = вопрос ОБРАТИМОСТИ в germ-кольце ℚ^ℕ/Фреше.
   Element-сторона = ЕДИНИЦЫ (обратимые; редукционный атлас держится на det ±1 = единице SL₂(ℤ));
   role-limit-сторона = ДЕЛИТЕЛИ НУЛЯ (необратимые; undecided).  Два атласа проекта (Element=атлас,
   role-limit=синтез XVIII) суть два полюса инвертируемости.

   ★ ХАРАКТЕРИЗАЦИЯ (genuine, провабельно — здесь доказано):
     (единица)        x обратим ⟺ x В КОНЦЕ НЕНУЛЕВОЙ (∃N ∀n≥N, x n ≠ 0) — обратный = /x на хвосте;
     (делитель нуля)  x — делитель нуля ⟺ нуль-множество x КОФИНАЛЬНО (x = 0 бесконечно часто) — свидетель
                      = индикатор нуль-множества.
   Между ними: разрешить, какой полюс = разрешить «конечно ли нуль-множество» = LPO/halting.

   ★ АНКЕРЫ: δ = 1/(n+1) ЕДИНИЦА (всюду ненулева, δ·ω=1) — Element-инфинитезималь обратима;
            even_ind ДЕЛИТЕЛЬ НУЛЯ (нуль на нечётных, кофинально) — undecided необратим.

   ★ КОНСТРУКТИВНО (0 аксиом).  Обе характеризации БЕЗ classic: единица строит явный обратный /x;
   делитель использует ПОЗИТИВНЫЙ cofinal (бесконечно часто, не двойное отрицание) + Qmult_integral.

   HONEST SCOPE.  Машинно-закрыто, 0 аксиом.  Доказаны обе характеризации (единица⟺в-конце-ненулев,
   делитель⟺нуль-множество-кофинально) + анкеры (δ единица, even_ind делитель).  ⚠ «Element = единицы
   атласа» — связь к редукционному атласу (det ±1 = единица) ЦИТИРУЕТСЯ (мост A2); здесь — алгебраическое
   ядро.  «Разрешить полюс = LPO/halting» — наблюдение (cs/ScaleFlowUndecidable), не передоказывается здесь.

   Elements: germ-кольцо; eventually_nonzero/cofinal_z (позитивные); g_unit/g_zero_divisor; delta/even_ind.
   Roles:    обратимость=Element-маркер; необратимость=role-limit-маркер; нуль-множество=носитель неразрешённости.
   Rules:    единица ⟺ в-конце-ненулев; делитель ⟺ нуль-множество кофинально; δ единица, even_ind делитель.

   ============ E/R/R разбор (осн. + образующие + вложенные + элемент-как-система) ============
     ОСН.: граница финитизации = обратимость germ-кольца (единица=Element, делитель=role-limit).
     Rules (L5): unit_iff (единица ⟺ в-конце-ненулев, обратный /x); zero_divisor_iff (делитель ⟺ нуль-множество
                 кофинально); δ единица, even_ind делитель.
     Roles (L4): обратимость=Element-маркер; необратимость=role-limit-маркер; нуль-множество=носитель неразрешённости.
     Elements  : germ-кольцо; eventually_nonzero/cofinal_z; g_unit/g_zero_divisor; delta/even_ind.
     ОБРАЗУЮЩИЕ: GermInfinitesimal (δ=единица, δ·ω=1); синтез XVIII (even_ind=делитель); редукционный атлас
                 (det±1=единица SL₂(ℤ), цитата, мост A2); cs/ScaleFlowUndecidable (разрешить полюс = halting, цитата).
     ВЛОЖЕННЫЕ : трихотомия (0 / единица / делитель) = (в-конце-ноль / в-конце-ненулев / undecided).
     ★ ЭЛЕМЕНТ-КАК-СИСТЕМА (обратимость x): Elements — (x, кандидат /x); Roles — Element-маркер; Rules —
                 обратимость разрешима ⟺ нуль-множество разрешимо ⟺ не упёрлись в undecided.
   ДИАГНОСТИКА (P4): конструктивно (явный /x, позитивный cofinal, Qmult_integral) => 0 акс; единственный
                 role-limit — undecided нуль-множество, НЕ ассертим. ЧЕСТНО: связь к атласу = цитата (A2).

   STATUS: 11 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  germ-кольцо + полюса инвертируемости (позитивные, конструктивные)       *)
(* ===================================================================== *)

Definition GProc : Type := nat -> Q.
Definition geq (x y : GProc) : Prop := exists N, forall n, (N <= n)%nat -> x n == y n.
Definition gmul (x y : GProc) : GProc := fun n => x n * y n.
Definition gconst (q : Q) : GProc := fun _ => q.

(** ЕДИНИЦА: обратим в germ-кольце. *)
Definition g_unit (x : GProc) : Prop := exists y, geq (gmul x y) (gconst 1).

(** «В конце ненулевой»: ∃N, на хвосте x n ≠ 0. *)
Definition eventually_nonzero (x : GProc) : Prop :=
  exists N, forall n, (N <= n)%nat -> ~ x n == 0.

(** Кофинально-ненулевой / кофинально-нулевой (позитивно — конструктивно). *)
Definition cofinal_nz (x : GProc) : Prop := forall N, exists n, (N <= n)%nat /\ ~ x n == 0.
Definition cofinal_z  (x : GProc) : Prop := forall N, exists n, (N <= n)%nat /\ x n == 0.

(** ДЕЛИТЕЛЬ НУЛЯ: ∃ y кофинально-ненулевой с x·y ~ 0. *)
Definition g_zero_divisor (x : GProc) : Prop :=
  exists y, cofinal_nz y /\ geq (gmul x y) (gconst 0).

(* ===================================================================== *)
(*  ★ Характеризация ЕДИНИЦЫ: обратим ⟺ в конце ненулевой                   *)
(* ===================================================================== *)

(** ⟸ : в-конце-ненулев => обратим (обратный = /x на хвосте). *)
Lemma eventually_nonzero_unit : forall x, eventually_nonzero x -> g_unit x.
Proof.
  intros x [N HN]. exists (fun n => / x n). exists N. intros n Hn.
  unfold gmul, gconst. apply Qmult_inv_r. apply HN. exact Hn.
Qed.

(** ⟹ : обратим => в-конце-ненулев (иначе 0 = 1 на нуле). *)
Lemma unit_eventually_nonzero : forall x, g_unit x -> eventually_nonzero x.
Proof.
  intros x [y [N HN]]. exists N. intros n Hn Hc.
  specialize (HN n Hn). unfold gmul, gconst in HN.
  rewrite Hc in HN. rewrite Qmult_0_l in HN. lra.
Qed.

(** ★ ЕДИНИЦА ⟺ в конце ненулевой. *)
Lemma unit_iff_eventually_nonzero : forall x, g_unit x <-> eventually_nonzero x.
Proof.
  intro x. split; [ apply unit_eventually_nonzero | apply eventually_nonzero_unit ].
Qed.

(* ===================================================================== *)
(*  ★ Характеризация ДЕЛИТЕЛЯ НУЛЯ: ⟺ нуль-множество кофинально             *)
(* ===================================================================== *)

(** ⟸ : нуль-множество кофинально => делитель нуля (свидетель = индикатор нуль-множества). *)
Lemma cofinal_z_zero_divisor : forall x, cofinal_z x -> g_zero_divisor x.
Proof.
  intros x Hz. exists (fun n => if Qeq_bool (x n) 0 then 1 else 0). split.
  - intros N. destruct (Hz N) as [n [Hn Hxz]]. exists n. split; [ exact Hn |].
    assert (E : Qeq_bool (x n) 0 = true) by (apply Qeq_bool_iff; exact Hxz).
    rewrite E. intro Hc. simpl in Hc. lra.
  - exists 0%nat. intros n _. unfold gmul, gconst.
    destruct (Qeq_bool (x n) 0) eqn:E.
    + simpl. apply Qeq_bool_iff in E. rewrite E. ring.
    + simpl. ring.
Qed.

(** ⟹ : делитель нуля => нуль-множество кофинально (y≠0 кофинально + x·y~0 => x=0 там). *)
Lemma zero_divisor_cofinal_z : forall x, g_zero_divisor x -> cofinal_z x.
Proof.
  intros x [y [Hynz [M HM]]] N.
  destruct (Hynz (Nat.max N M)) as [n [Hn Hyn]].
  exists n. split.
  - apply Nat.le_trans with (Nat.max N M); [ apply Nat.le_max_l | exact Hn ].
  - assert (HMn : (M <= n)%nat)
      by (apply Nat.le_trans with (Nat.max N M); [ apply Nat.le_max_r | exact Hn ]).
    specialize (HM n HMn). unfold gmul, gconst in HM.
    apply Qmult_integral in HM. destruct HM as [Hx | Hy].
    + exact Hx.
    + exfalso. apply Hyn. exact Hy.
Qed.

(** ★ ДЕЛИТЕЛЬ НУЛЯ ⟺ нуль-множество кофинально. *)
Lemma zero_divisor_iff_cofinal_z : forall x, g_zero_divisor x <-> cofinal_z x.
Proof.
  intro x. split; [ apply zero_divisor_cofinal_z | apply cofinal_z_zero_divisor ].
Qed.

(* ===================================================================== *)
(*  ★ Анкеры: δ — единица; even_ind — делитель нуля                         *)
(* ===================================================================== *)

Definition Qof (n : nat) : Q := inject_Z (Z.of_nat n).
Lemma Qof_pos : forall m, 0 < Qof (S m).
Proof. intro m. unfold Qof, Qlt. simpl. lia. Qed.

Definition delta (m : nat) : Q := / Qof (S m).
Definition even_ind (n : nat) : Q := if Nat.even n then 1 else 0.

(** ★ δ = 1/(n+1) — ЕДИНИЦА (всюду ненулева; обратный = ω = n+1). *)
Lemma delta_is_unit : g_unit delta.
Proof.
  apply eventually_nonzero_unit. exists 0%nat. intros n _ Hc.
  assert (Hp : 0 < delta n) by (unfold delta; apply Qinv_lt_0_compat; apply Qof_pos).
  rewrite Hc in Hp. exact (Qlt_irrefl 0 Hp).
Qed.

(** even_ind нулевой на нечётных — кофинально. *)
Lemma even_ind_cofinal_z : cofinal_z even_ind.
Proof.
  intro N. exists (2 * N + 1)%nat. split; [ lia |].
  unfold even_ind.
  assert (Ho : Nat.even (2 * N + 1) = false).
  { replace (2 * N + 1)%nat with (1 + 2 * N)%nat by lia.
    rewrite Nat.even_add_mul_2. reflexivity. }
  rewrite Ho. reflexivity.
Qed.

(** ★ even_ind — ДЕЛИТЕЛЬ НУЛЯ (undecided необратим). *)
Lemma even_ind_is_zero_divisor : g_zero_divisor even_ind.
Proof. apply cofinal_z_zero_divisor. exact even_ind_cofinal_z. Qed.

(* ===================================================================== *)
(*  Капстоун: граница = обратимость                                         *)
(* ===================================================================== *)

(** ★ Граница финитизации = ОБРАТИМОСТЬ в germ-кольце (0 аксиом):
      (единица)    обратим ⟺ в конце ненулевой — Element-полюс (атлас, det ±1);
      (делитель)   делитель нуля ⟺ нуль-множество кофинально — role-limit-полюс (undecided);
      (δ единица)  Element-инфинитезималь 1/(n+1) обратима;
      (even_ind делитель) undecided-индикатор необратим.
    Два полюса инвертируемости = две стороны границы.  Разрешить полюс = «конечно ли нуль-множество» =
    LPO/halting (cs/ScaleFlowUndecidable, цитата).  Связь Element=единицы-атласа — мост A2. *)
Theorem boundary_is_invertibility :
  (forall x, g_unit x <-> eventually_nonzero x)
  /\ (forall x, g_zero_divisor x <-> cofinal_z x)
  /\ g_unit delta
  /\ g_zero_divisor even_ind.
Proof.
  split; [ exact unit_iff_eventually_nonzero |].
  split; [ exact zero_divisor_iff_cofinal_z |].
  split; [ exact delta_is_unit | exact even_ind_is_zero_divisor ].
Qed.
