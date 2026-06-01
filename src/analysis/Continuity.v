(** * Continuity.v — Unified head file of the (Q-level) continuity theory (F-7)

    Консолидация: каноничные определения непрерывности / равномерной
    непрерывности для f : Q -> Q на [a,b], алгебра и мост от липшицевости —
    в ОДНОМ файле (сейчас `uniformly_continuous_on` определён ПОРОЗНЬ в
    IVT_ERR/EVT_ERR/EVT_idx/HeineBorelComplete). Определения совпадают с
    HeineBorelComplete.v.

    ============ E/R/R разбор: непрерывность как система ============
      Rules (L5): ε-δ — правило связи близости (вход → выход); мост
                  Lipschitz ⇒ uniform; РАЗЛИЧИЕ uniform/pointwise = зависит ли
                  модуль δ от точки.
      Roles (L4): «вход x» / «выход f x» / «модуль δ»; «равномерный модуль»
                  (один на весь отрезок) vs «поточечный» (свой в каждой точке).
      Elements  : рациональные значения f(x) (L1+P4).

    ДИАГНОСТИКА / честная граница: непрерывность — ПРАВИЛО (отношение
    близостей), не объект. Над ℚ непрерывность ⇏ равномерность (НЕТ
    компактности / теорема Гейне–Кантора не выполнена) — поэтому здесь
    доказан лишь ПРОВИЗНЫЙ мост Lipschitz ⇒ uniform ⇒ pointwise; обратного
    (pointwise ⇒ uniform) НЕТ (честно, см. гл. 5.3).

    NB: МИГРАЦИЯ IVT_ERR/EVT/HeineBorelComplete на этот файл — отложена
    (не трогаем существующие, чтобы не каскадить на downstream); здесь —
    канонический головной файл, на который они смогут ссылаться.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs Qminmax.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Canonical definitions (f : Q -> Q on [a,b])                           *)
(* ===================================================================== *)

(** Pointwise continuity at x0 (within [a,b]): δ may depend on x0. *)
Definition continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall x0 : Q, a <= x0 <= b ->
    forall eps : Q, eps > 0 ->
      exists delta : Q, delta > 0 /\
        forall x : Q, a <= x <= b -> Qabs (x - x0) < delta -> Qabs (f x - f x0) < eps.

(** Uniform continuity: one δ works for ALL points of [a,b]. *)
Definition uniformly_continuous_on (f : Q -> Q) (a b : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists delta : Q, delta > 0 /\
      forall x y : Q, a <= x <= b -> a <= y <= b ->
        Qabs (x - y) < delta -> Qabs (f x - f y) < eps.

(** K-Lipschitz on [a,b]. *)
Definition Lipschitz_on (f : Q -> Q) (a b K : Q) : Prop :=
  K > 0 /\
  forall x y : Q, a <= x <= b -> a <= y <= b ->
    Qabs (f x - f y) <= K * Qabs (x - y).

(* ===================================================================== *)
(*  Bridges: Lipschitz ⇒ uniform ⇒ pointwise                              *)
(* ===================================================================== *)

Theorem lipschitz_uniform : forall f a b K,
  Lipschitz_on f a b K -> uniformly_continuous_on f a b.
Proof.
  intros f a b K [HK HL] eps Heps.
  exists (eps / K). split.
  - unfold Qdiv. apply Qmult_lt_0_compat; [ exact Heps | apply Qinv_lt_0_compat; exact HK ].
  - intros x y Hx Hy Hxy.
    apply Qle_lt_trans with (K * Qabs (x - y)).
    + apply HL; assumption.
    + assert (Heq : (eps / K) * K == eps) by (field; lra).
      apply Qlt_le_trans with ((eps / K) * K).
      * rewrite (Qmult_comm K (Qabs (x - y))).
        apply Qmult_lt_compat_r; [ exact HK | exact Hxy ].
      * rewrite Heq. apply Qle_refl.
Qed.

Theorem uniformly_continuous_pointwise : forall f a b,
  uniformly_continuous_on f a b -> continuous_on f a b.
Proof.
  intros f a b H x0 Hx0 eps Heps.
  destruct (H eps Heps) as [delta [Hd Hu]].
  exists delta. split; [ exact Hd | ].
  intros x Hx Hxy. apply Hu; assumption.
Qed.

(* ===================================================================== *)
(*  Algebra of (uniformly) continuous functions                           *)
(* ===================================================================== *)

(** Constants are uniformly continuous. *)
Theorem uniformly_continuous_const : forall c a b,
  uniformly_continuous_on (fun _ => c) a b.
Proof.
  intros c a b eps Heps. exists 1. split; [ lra | ].
  intros x y _ _ _. simpl.
  assert (E : c - c == 0) by ring.
  rewrite (Qabs_wd _ _ E). rewrite Qabs_pos; lra.
Qed.

(** The identity is 1-Lipschitz, hence uniformly continuous. *)
Theorem identity_lipschitz : forall a b, Lipschitz_on (fun x => x) a b 1.
Proof.
  intros a b. split; [ lra | ].
  intros x y _ _. simpl. rewrite Qmult_1_l. apply Qle_refl.
Qed.

Theorem identity_uniformly_continuous : forall a b,
  uniformly_continuous_on (fun x => x) a b.
Proof. intros a b. apply (lipschitz_uniform _ _ _ 1), identity_lipschitz. Qed.

(** Sum of uniformly continuous functions is uniformly continuous. *)
Theorem uniformly_continuous_sum : forall f g a b,
  uniformly_continuous_on f a b -> uniformly_continuous_on g a b ->
  uniformly_continuous_on (fun x => f x + g x) a b.
Proof.
  intros f g a b Hf Hg eps Heps.
  assert (He2 : eps * (1#2) > 0) by lra.
  destruct (Hf _ He2) as [df [Hdf Hf']].
  destruct (Hg _ He2) as [dg [Hdg Hg']].
  exists (Qmin df dg). split.
  - apply Q.min_glb_lt; assumption.
  - intros x y Hx Hy Hxy. simpl.
    assert (Ha : Qabs (x - y) < df) by (eapply Qlt_le_trans; [ exact Hxy | apply Q.le_min_l ]).
    assert (Hb : Qabs (x - y) < dg) by (eapply Qlt_le_trans; [ exact Hxy | apply Q.le_min_r ]).
    pose proof (Hf' x y Hx Hy Ha) as A.
    pose proof (Hg' x y Hx Hy Hb) as B.
    apply Qle_lt_trans with (Qabs (f x - f y) + Qabs (g x - g y)).
    + assert (E : (f x + g x) - (f y + g y) == (f x - f y) + (g x - g y)) by ring.
      rewrite (Qabs_wd _ _ E). apply Qabs_triangle.
    + lra.
Qed.

(* ===================================================================== *)
(*  Honest limitation (no Heine–Cantor over Q)                            *)
(* ===================================================================== *)

(** Over ℚ there is NO theorem  continuous_on f a b -> uniformly_continuous_on f a b
    (Heine–Cantor fails without compactness). The only provable route to
    uniform continuity here is via Lipschitz_on (lipschitz_uniform) or by
    assuming a modulus. This absence is deliberate; see Глава 5.3. *)

Print Assumptions lipschitz_uniform.
Print Assumptions uniformly_continuous_sum.
