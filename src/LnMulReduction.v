(** * LnMulReduction.v — ЭНДШПИЛЬ: горизонт ln_mul СВЕДЁН к одному ключевому факту
    Elements: рациональные x,y∈[0,1); процессы-числа ln_proc, geometric_limit, exp_R.
    Roles:    редукция-СБОРКА — показать, что функц. уравнение логарифма
              L(x)+L(y) ~~ L(x⊕y) (горизонт ln_mul_functional_equation) ПОЛНОСТЬЮ следует
              из единственного факта exp_R(L(z)) ~~ 1/(1−z) (мост exp∘L = геометрическая),
              через мультипликативность exp_R (exp_R_add) и его инъективность (exp_R_inj).
    Rules:    geom_inv ((1−z)·(1/(1−z))~~1, через geometric_sum_identity + zⁿ→0);
              geom_mul (1/(1−x)·1/(1−y) ~~ 1/(1−x⊕y), через (1−x)(1−y)=1−(x⊕y) + сокращение);
              затем exp_R_inj сводит горизонт к произведению.

    ЭТА ВЕХА: горизонт ИЗОЛИРОВАН.  ln_mul_from_key: ЕСЛИ exp_R(ln_proc z) ~~ geometric_limit z
    для всех z∈[0,1), ТО горизонт ln_mul_functional_equation доказан.  Остаётся ровно ОДИН факт
    (мост exp_R∘ln_proc = 1/(1−z)), который строит FPSEval-цепочка (закон композиции).
    Это НЕ Admit — это conditional-теорема, честно отделяющая сделанную сборку от оставшегося босса.

    ============ E/R/R разбор ============
      Elements: частичные суммы геометрического/лог-ряда и их произведения — конечные Q на стадии n.
      Roles:    geom_inv = роль-обратная (1−z); geom_mul = роль-мультипликативность геометрической
                (1/(1−x)·1/(1−y)=1/(1−x⊕y)); ln_mul_from_key = роль-редукция горизонта к ключу.
      Rules:    geometric_sum_identity ((1−r)Σ=1−rⁿ⁺¹); сокращение на cauchy_const≠0; exp_R_add/inj.
    ДИАГНОСТИКА (P4): exp_R линеаризует логарифм-процесс (L(x)+L(y) ↦ exp_R(L(x))·exp_R(L(y))),
      сводя аддитивность к мультипликативности, замкнутой на геометрической стороне.  Унаследует classic.

    STATUS: 8 Qed, 0 Admitted, 0 axioms (наследует classic через ProcessExp/анализ).
            ГОТОВО: ВЕСЬ эндшпиль — geom_inv, geom_mul, и ln_mul_from_key (горизонт ⟸ ключевой факт).
            ОСТАЁТСЯ (единственный босс): exp_R(ln_proc z) ~~ geometric_limit z — закон композиции
            eval(exp∘log1m)=exp_R∘ln_proc (внешний Fubini), строится в FPSEval.
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia.
From ToS Require Import CauchyReal.
From ToS Require Import RealField.
From ToS Require Import SeriesConvergence.
From ToS Require Import ProcessExp.
From ToS Require Import Log2Process.
From ToS Require Import Log2FunctionalEq.

Open Scope Q_scope.
Open Scope cauchy_scope.

(* ================================================================== *)
(*  Мелкие хелперы: равенство стадий ⟹ ~~; cauchy_const                 *)
(* ================================================================== *)

Lemma cs_eq_equiv : forall (P R : CauchySeq),
  (forall n, cs_seq P n == cs_seq R n) -> P ~~ R.
Proof.
  intros P R H eps Heps. exists 0%nat. intros n _.
  rewrite (H n).
  assert (Hz : cs_seq R n - cs_seq R n == 0) by ring.
  rewrite Hz. change (Qabs 0) with (0:Q). exact Heps.
Qed.

Lemma cauchy_const_wd : forall a b : Q, a == b -> cauchy_const a ~~ cauchy_const b.
Proof. intros a b H. apply cs_eq_equiv. intro n. exact H. Qed.

Lemma cauchy_const_mul : forall a b : Q,
  cauchy_const (a * b) ~~ cauchy_mul (cauchy_const a) (cauchy_const b).
Proof. intros a b. apply cs_eq_equiv. intro n. reflexivity. Qed.

(* ================================================================== *)
(*  ★ geom_inv: (1−z)·(1/(1−z)) ~~ 1  (процессная обратная геометрической)*)
(* ================================================================== *)

Lemma geom_inv : forall (z : Q) (Hz : 0 <= z) (Hz1 : z < 1),
  cauchy_mul (cauchy_const (1 - z)) (geometric_limit z Hz Hz1) ~~ cauchy_one.
Proof.
  intros z Hz Hz1 eps Heps.
  destruct (Qpow_limit_zero z Hz Hz1 eps Heps) as [N HN].
  exists N. intros n Hn.
  change (cs_seq (cauchy_mul (cauchy_const (1 - z)) (geometric_limit z Hz Hz1)) n)
    with ((1 - z) * partial_sum (fun k => Qpow z k) n).
  change (cs_seq cauchy_one n) with (1:Q).
  assert (Hgs : (1 - z) * partial_sum (fun k => Qpow z k) n == 1 - Qpow z (S n))
    by apply geometric_sum_identity.
  rewrite Hgs.
  assert (Hd : 1 - Qpow z (S n) - 1 == - Qpow z (S n)) by ring.
  rewrite Hd, Qabs_opp.
  rewrite (Qabs_pos (Qpow z (S n)) (Qpow_nonneg z (S n) Hz)).
  apply HN. lia.
Qed.

(* ================================================================== *)
(*  Сокращение на cauchy_const + перестановка 4 множителей              *)
(* ================================================================== *)

(** Если c·A ~~ 1 и c·B ~~ 1, то A ~~ B (единственность обратного). *)
Lemma cauchy_const_cancel : forall (c : Q) (A B : CauchySeq),
  cauchy_mul (cauchy_const c) A ~~ cauchy_one ->
  cauchy_mul (cauchy_const c) B ~~ cauchy_one ->
  A ~~ B.
Proof.
  intros c A B HA HB.
  eapply cauchy_equiv_trans; [ apply cauchy_equiv_sym; apply cauchy_mul_one_r | ].
  eapply cauchy_equiv_trans.
  - apply cauchy_mul_compat; [ apply cauchy_equiv_refl | apply cauchy_equiv_sym; exact HB ].
  - eapply cauchy_equiv_trans; [ apply cauchy_equiv_sym; apply cauchy_mul_assoc | ].
    eapply cauchy_equiv_trans.
    + apply cauchy_mul_compat; [ apply cauchy_mul_comm | apply cauchy_equiv_refl ].
    + eapply cauchy_equiv_trans.
      * apply cauchy_mul_compat; [ exact HA | apply cauchy_equiv_refl ].
      * apply cauchy_mul_one_l.
Qed.

(** (a·b)·(c·d) ~~ (a·c)·(b·d) — перестановка 4 множителей (комм. моноид). *)
Lemma cmul4_swap : forall a b c d : CauchySeq,
  cauchy_mul (cauchy_mul a b) (cauchy_mul c d)
  ~~ cauchy_mul (cauchy_mul a c) (cauchy_mul b d).
Proof.
  intros a b c d.
  eapply cauchy_equiv_trans; [ apply cauchy_mul_assoc | ].
  eapply cauchy_equiv_trans.
  { apply cauchy_mul_compat; [ apply cauchy_equiv_refl | ].
    eapply cauchy_equiv_trans; [ apply cauchy_equiv_sym; apply cauchy_mul_assoc | ].
    apply cauchy_mul_compat; [ apply cauchy_mul_comm | apply cauchy_equiv_refl ]. }
  eapply cauchy_equiv_trans.
  { apply cauchy_mul_compat; [ apply cauchy_equiv_refl | apply cauchy_mul_assoc ]. }
  apply cauchy_equiv_sym. apply cauchy_mul_assoc.
Qed.

(* ================================================================== *)
(*  ★ geom_mul: 1/(1−x)·1/(1−y) ~~ 1/(1−(x⊕y))                          *)
(* ================================================================== *)

Lemma geom_mul : forall (x y : Q) (Hx : 0 <= x) (Hx1 : x < 1) (Hy : 0 <= y) (Hy1 : y < 1)
    (Hxy : 0 <= x + y - x * y) (Hxy1 : x + y - x * y < 1),
  cauchy_mul (geometric_limit x Hx Hx1) (geometric_limit y Hy Hy1)
  ~~ geometric_limit (x + y - x * y) Hxy Hxy1.
Proof.
  intros x y Hx Hx1 Hy Hy1 Hxy Hxy1.
  apply (cauchy_const_cancel (1 - (x + y - x * y))).
  - eapply cauchy_equiv_trans.
    + apply cauchy_mul_compat; [ | apply cauchy_equiv_refl ].
      eapply cauchy_equiv_trans with (cauchy_const ((1 - x) * (1 - y))).
      * apply cauchy_const_wd. ring.
      * apply cauchy_const_mul.
    + eapply cauchy_equiv_trans; [ apply cmul4_swap | ].
      eapply cauchy_equiv_trans.
      * apply cauchy_mul_compat; apply geom_inv.
      * apply cauchy_mul_one_l.
  - apply geom_inv.
Qed.

(* ================================================================== *)
(*  ★★ ГОРИЗОНТ ⟸ КЛЮЧЕВОЙ ФАКТ                                         *)
(* ================================================================== *)

(** ★★ ln_mul_functional_equation СЛЕДУЕТ из exp_R(ln_proc z) ~~ geometric_limit z.
    exp_R_inj сводит L(x)+L(y)~~L(x⊕y) к exp-уровню; exp_R_add даёт произведение;
    KEY превращает каждый множитель в 1/(1−·); geom_mul = 1/(1−x⊕y); KEY обратно.
    Изолирует оставшийся босс — ровно ОДИН факт (мост exp_R∘ln_proc). *)
Theorem ln_mul_from_key :
  (forall (z : Q) (Hz : 0 <= z) (Hz1 : z < 1),
     exp_R (ln_proc z Hz Hz1) ~~ geometric_limit z Hz Hz1) ->
  ln_mul_functional_equation.
Proof.
  intros KEY. unfold ln_mul_functional_equation.
  intros x y Hx Hx1 Hy Hy1 Hxy Hxy1.
  apply exp_R_inj.
  eapply cauchy_equiv_trans; [ apply exp_R_add | ].
  eapply cauchy_equiv_trans.
  { apply cauchy_mul_compat; apply KEY. }
  eapply cauchy_equiv_trans; [ apply geom_mul | ].
  apply cauchy_equiv_sym. apply KEY.
Qed.

(** Аудит аксиом. *)
Print Assumptions geom_inv.
Print Assumptions geom_mul.
Print Assumptions ln_mul_from_key.

(* ================================================================== *)
(*  СВОДКА: эндшпиль ln_mul СОБРАН.  Горизонт L(x)+L(y)~~L(x⊕y) сведён  *)
(*  к ЕДИНСТВЕННОМУ факту exp_R(ln_proc z)~~1/(1−z) (мост exp∘L=геом.,   *)
(*  строится в FPSEval законом композиции).  geom_inv/geom_mul + exp_R_  *)
(*  add/inj замыкают всё остальное.                                      *)
(* ================================================================== *)
