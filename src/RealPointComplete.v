(** * RealPointComplete.v — Completeness of the space of RealPoint classes

    Elements: rational approximations of the given points; one rational per diagonal stage
    Roles:    "limit of a sequence of points" = the diagonal process;
              "threshold" idx k = witness of convergence of the k-th point
    Rules:    class_cauchy (points come together in the class metric rp_dist);
              the diagonal rule: read the k-th point at its own threshold
    Status:   metric completeness of the classes, in two prices

    ================= E/R/R разбор: полнота пространства точек =================
    Система — НЕ «множество ℝ без дыр», а ПРАВИЛО построения предела.
    Генеративный порядок Rules -> Roles -> Elements:

      Rules (L5)    : class_cauchy — условие сближения последовательности точек:
                      расстояние между точками (оно само точка, rp_dist) в конце
                      концов не больше любого eps; правило диагонали — у k-й точки
                      взять приближение на её собственном рубеже idx k, после
                      которого её хвост уходит не дальше r k, а r k -> 0.
      Roles (L4)    : «предел последовательности точек» = роль, которую занимает
                      диагональный процесс k |-> s k (idx k); «рубеж» idx k =
                      свидетель сходимости k-й точки.
      Elements      : рациональные приближения cs_seq (s k) n; на каждом шаге
                      диагонали — одно рациональное число (L1 + P4).

    ДИАГНОСТИКА (P4): предел — процесс, собранный по правилу из стадий данных
    процессов; готового объекта «в конце» нет. Полнота — свойство ПРАВИЛА
    (предел всегда можно построить), а не свойство завершённого множества.

    ЦЕНА — два случая, и различие содержательно:
      * regular_class_complete — представители регулярны (is_Regular_Cauchy:
        скорость сходимости известна заранее), рубеж idx k = k + 1 ВЫЧИСЛЯЕТСЯ:
        допущений нет;
      * class_complete_L4 — представители произвольны: рубеж каждой точки
        ИЗВЛЕКАЕТСЯ из доказательства «существует N» (свойство Коши лежит в
        Prop) — это L4_witness (ex -> sig), применённый к счётному семейству
        точек; classic не нужен.
    Это различие «логическое свойство Коши / свойство, несущее вычислимые
    данные» том проводит словами в Главе 5.1, § «Доказательство Коши и
    вычислимый модуль»; здесь у него точная цена.

    ЧЕСТНАЯ ГРАНИЦА: расстояние rp_dist имеет значения в RealPoint, а не в Q,
    поэтому абстрактный предикат is_complete_metric (stdlib/MetricSpace.v, для
    d : X -> X -> Q) к паре (RealPoint, rp_dist) буквально не применяется;
    полнота доказана в собственной записи class_cauchy / class_limit, и обе
    записи корректны на классах (class_cauchy_compat, class_limit_compat).
    Частный случай с общим рубежом у всех точек уже был: Completeness.v,
    diagonal_converges при условии meta_cauchy.

    STATUS: 11 Qed, 0 Admitted; axioms: none, except L4_witness in class_complete_L4
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs Lqa Lia ZArith.
From ToS Require Import CauchyReal.
From ToS Require Import RealPointSetoid.
From ToS Require Import RealPointMetric.
From ToS Require Import RealPointTopology.   (* cauchy_le_compat *)
From ToS Require process.ProcessCore.         (* is_Regular_Cauchy, inv_le_of_le *)
From ToS Require ToS_Axioms.                  (* L4_witness -- used in class_complete_L4 only *)

Open Scope Q_scope.
Local Open Scope cauchy_scope.

(* ===================================================================== *)
(*  Cauchy sequence of points and its limit, through rp_dist              *)
(* ===================================================================== *)

(** A sequence of points is Cauchy in the metric of classes: the distance
    rp_dist (s k) (s l) -- itself a point -- is eventually <= eps. *)
Definition class_cauchy (s : nat -> RealPoint) : Prop :=
  forall eps : Q, 0 < eps -> exists K : nat, forall k l : nat,
    (K <= k)%nat -> (K <= l)%nat ->
    cauchy_le (rp_dist (s k) (s l)) (cauchy_const eps).

(** A point L is the limit of the sequence of points s. *)
Definition class_limit (s : nat -> RealPoint) (L : RealPoint) : Prop :=
  forall eps : Q, 0 < eps -> exists K : nat, forall k : nat,
    (K <= k)%nat -> cauchy_le (rp_dist (s k) L) (cauchy_const eps).

(** Both notions live on classes: representatives may be replaced. *)
Lemma class_limit_compat : forall (s s' : nat -> RealPoint) (L L' : RealPoint),
  (forall k, s k ~~ s' k) -> L ~~ L' -> class_limit s L -> class_limit s' L'.
Proof.
  intros s s' L L' Hs HL H eps Heps. destruct (H eps Heps) as [K HK].
  exists K. intros k Hk.
  eapply cauchy_le_compat;
    [ apply rp_dist_compat; [ apply Hs | apply HL ]
    | apply cauchy_equiv_refl
    | apply HK; exact Hk ].
Qed.

Lemma class_cauchy_compat : forall (s s' : nat -> RealPoint),
  (forall k, s k ~~ s' k) -> class_cauchy s -> class_cauchy s'.
Proof.
  intros s s' Hs H eps Heps. destruct (H eps Heps) as [K HK].
  exists K. intros k l Hk Hl.
  eapply cauchy_le_compat;
    [ apply rp_dist_compat; [ apply Hs | apply Hs ]
    | apply cauchy_equiv_refl
    | apply HK; assumption ].
Qed.

(* ===================================================================== *)
(*  Helpers                                                               *)
(* ===================================================================== *)

Lemma rp_le_const_unfold : forall (a b : CauchySeq) (e : Q),
  cauchy_le (rp_dist a b) (cauchy_const e) ->
  forall delta, 0 < delta -> exists P : nat, forall p, (P <= p)%nat ->
    Qabs (cs_seq a p - cs_seq b p) < e + delta.
Proof.
  intros a b e H delta Hd. destruct (H delta Hd) as [P HP]. exists P. intros p Hp.
  specialize (HP p Hp). rewrite cs_rp_dist, cs_const in HP. exact HP.
Qed.

Lemma Qabs_tri3 : forall x a b z : Q,
  Qabs (x - z) <= Qabs (x - a) + Qabs (a - b) + Qabs (b - z).
Proof.
  intros x a b z.
  assert (E : x - z == (x - a) + (a - b) + (b - z)) by ring.
  rewrite (Qabs_wd _ _ E).
  eapply Qle_trans; [ apply Qabs_triangle | ].
  apply Qplus_le_compat; [ apply Qabs_triangle | apply Qle_refl ].
Qed.

Lemma inv_nat_small : forall eps : Q, 0 < eps ->
  exists N : nat, (1 <= N)%nat /\ 1 / inject_Z (Z.of_nat N) < eps.
Proof.
  intros [p q] Heps. unfold Qlt in Heps. simpl in Heps.
  exists (Pos.to_nat (q + 1)). split; [ lia | ].
  rewrite positive_nat_Z.
  unfold Qlt, Qdiv, Qmult, Qinv, inject_Z. simpl.
  nia.
Qed.

(* ===================================================================== *)
(*  The diagonal core                                                     *)
(* ===================================================================== *)

Section DiagonalCore.

Variable s : nat -> RealPoint.
Variable idx : nat -> nat.          (* where to read the k-th point: its threshold *)
Variable r : nat -> Q.              (* how far its tail can still move *)

Hypothesis Hidx : forall k p, (idx k <= p)%nat ->
  Qabs (cs_seq (s k) (idx k) - cs_seq (s k) p) <= r k.
Hypothesis Hr : forall eps, 0 < eps -> exists K, forall k, (K <= k)%nat -> r k < eps.
Hypothesis Hs : class_cauchy s.

(** The diagonal process k |-> s k (idx k) is a Cauchy process. *)
Lemma diag_idx_is_cauchy : is_cauchy (fun k => cs_seq (s k) (idx k)).
Proof.
  intros eps Heps.
  assert (H4 : 0 < eps * (1#4)) by lra.
  destruct (Hr _ H4) as [K1 HK1].
  destruct (Hs _ H4) as [K2 HK2].
  exists (Nat.max K1 K2). intros m n Hm Hn. cbv beta.
  assert (Hmn : cauchy_le (rp_dist (s m) (s n)) (cauchy_const (eps * (1#4))))
    by (apply HK2; lia).
  destruct (rp_le_const_unfold _ _ _ Hmn _ H4) as [P HP].
  set (p := Nat.max P (Nat.max (idx m) (idx n))).
  assert (B1 : Qabs (cs_seq (s m) (idx m) - cs_seq (s m) p) <= r m)
    by (apply Hidx; unfold p; lia).
  assert (B2 : Qabs (cs_seq (s m) p - cs_seq (s n) p) < eps * (1#4) + eps * (1#4))
    by (apply HP; unfold p; lia).
  assert (B3 : Qabs (cs_seq (s n) (idx n) - cs_seq (s n) p) <= r n)
    by (apply Hidx; unfold p; lia).
  rewrite (Qabs_Qminus (cs_seq (s n) (idx n)) (cs_seq (s n) p)) in B3.
  assert (R1 : r m < eps * (1#4)) by (apply HK1; lia).
  assert (R2 : r n < eps * (1#4)) by (apply HK1; lia).
  eapply Qle_lt_trans;
    [ apply (Qabs_tri3 _ (cs_seq (s m) p) (cs_seq (s n) p)) | ].
  lra.
Qed.

(** The limit point: the diagonal process with its proof of the Cauchy property. *)
Definition diag_idx_limit : RealPoint := mkCauchy _ diag_idx_is_cauchy.

(** The sequence of points converges to the diagonal point. *)
Lemma diag_idx_converges : class_limit s diag_idx_limit.
Proof.
  intros eps Heps.
  assert (H2 : 0 < eps * (1#2)) by lra.
  destruct (Hs _ H2) as [K2 HK2].
  exists K2. intros k Hk delta Hdelta.
  assert (D4 : 0 < delta * (1#4)) by lra.
  destruct (Hr _ D4) as [K1 HK1].
  destruct (cs_cauchy (s k) _ D4) as [M HM].
  exists (Nat.max K1 (Nat.max K2 M)). intros p Hp.
  rewrite cs_rp_dist, cs_const.
  change (cs_seq diag_idx_limit p) with (cs_seq (s p) (idx p)).
  assert (Hkp : cauchy_le (rp_dist (s k) (s p)) (cauchy_const (eps * (1#2))))
    by (apply HK2; lia).
  destruct (rp_le_const_unfold _ _ _ Hkp _ D4) as [Q0 HQ0].
  set (q := Nat.max Q0 (Nat.max (idx p) p)).
  assert (B1 : Qabs (cs_seq (s k) p - cs_seq (s k) q) < delta * (1#4))
    by (apply HM; unfold q; lia).
  assert (B2 : Qabs (cs_seq (s k) q - cs_seq (s p) q) < eps * (1#2) + delta * (1#4))
    by (apply HQ0; unfold q; lia).
  assert (B3 : Qabs (cs_seq (s p) (idx p) - cs_seq (s p) q) <= r p)
    by (apply Hidx; unfold q; lia).
  rewrite (Qabs_Qminus (cs_seq (s p) (idx p)) (cs_seq (s p) q)) in B3.
  assert (R : r p < delta * (1#4)) by (apply HK1; lia).
  eapply Qle_lt_trans;
    [ apply (Qabs_tri3 _ (cs_seq (s k) q) (cs_seq (s p) q)) | ].
  lra.
Qed.

End DiagonalCore.

(* ===================================================================== *)
(*  The modulus 1/(k+1) tends to zero                                     *)
(* ===================================================================== *)

Definition inv_S (k : nat) : Q := 1 / inject_Z (Z.of_nat (S k)).

Lemma inv_S_pos : forall k, 0 < inv_S k.
Proof.
  intro k. unfold inv_S, Qdiv. rewrite Qmult_1_l.
  apply Qinv_lt_0_compat. apply ProcessCore.inject_nat_pos. lia.
Qed.

Lemma inv_S_small : forall eps, 0 < eps ->
  exists K, forall k, (K <= k)%nat -> inv_S k < eps.
Proof.
  intros eps Heps. destruct (inv_nat_small eps Heps) as [N [HN1 HN]].
  exists N. intros k Hk. unfold inv_S.
  eapply Qle_lt_trans; [ apply (ProcessCore.inv_le_of_le (S k) N); lia | exact HN ].
Qed.

(* ===================================================================== *)
(*  1. Regular representatives: no axioms                                 *)
(* ===================================================================== *)

(** If every point of the sequence is given by a REGULAR representative
    (its rate of convergence is known in advance), the threshold idx k = k + 1
    is computed, and the limit point exists with no assumption at all. *)
Theorem regular_class_complete : forall s : nat -> RealPoint,
  (forall k, ProcessCore.is_Regular_Cauchy (cs_seq (s k))) ->
  class_cauchy s ->
  exists L : RealPoint, class_limit s L.
Proof.
  intros s Hreg Hs.
  assert (Hidx : forall k p, (S k <= p)%nat ->
    Qabs (cs_seq (s k) (S k) - cs_seq (s k) p) <= inv_S k + inv_S k).
  { intros k p Hp.
    eapply Qle_trans; [ apply (Hreg k (S k) p); lia | ].
    assert (Hle := ProcessCore.inv_le_of_le p (S k) ltac:(lia) Hp).
    unfold inv_S. lra. }
  assert (Hr : forall eps, 0 < eps ->
    exists K, forall k, (K <= k)%nat -> inv_S k + inv_S k < eps).
  { intros eps Heps.
    destruct (inv_S_small (eps * (1#2)) ltac:(lra)) as [K HK].
    exists K. intros k Hk. specialize (HK k Hk). lra. }
  exists (diag_idx_limit s S (fun k => inv_S k + inv_S k) Hidx Hr Hs).
  apply diag_idx_converges.
Qed.

(* ===================================================================== *)
(*  2. Arbitrary representatives: L4_witness only                         *)
(* ===================================================================== *)

(** For arbitrary representatives the threshold of each point is EXTRACTED
    from the proof of its Cauchy property ("there exists N"): this is
    L4_witness (ex -> sig) applied to a countable family of points.
    classic is not used. *)
Theorem class_complete_L4 : forall s : nat -> RealPoint,
  class_cauchy s ->
  exists L : RealPoint, class_limit s L.
Proof.
  intros s Hs.
  pose (W := fun k : nat =>
    ToS_Axioms.L4_witness
      (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
         Qabs (cs_seq (s k) m - cs_seq (s k) n) < inv_S k)
      (cs_cauchy (s k) (inv_S k) (inv_S_pos k))).
  pose (idx := fun k : nat => proj1_sig (W k)).
  assert (Hidx : forall k p, (idx k <= p)%nat ->
    Qabs (cs_seq (s k) (idx k) - cs_seq (s k) p) <= inv_S k).
  { intros k p Hp. apply Qlt_le_weak.
    apply (proj2_sig (W k)); [ apply Nat.le_refl | exact Hp ]. }
  exists (diag_idx_limit s idx inv_S Hidx inv_S_small Hs).
  apply diag_idx_converges.
Qed.

Print Assumptions regular_class_complete.
Print Assumptions class_complete_L4.
