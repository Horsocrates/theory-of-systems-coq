(** * EVT_ArgmaxNotCauchy.v — The process of maximum POSITIONS need not be Cauchy

    Elements: grid nodes k/(n+1) of [0,1]; the two peaks 1/3 and 1/2
    Roles:    "position of the maximum at stage n" (argmax_process) and
              "value of the maximum at stage n" (sup_process)
    Rules:    stage n takes the grid of n+1 cells; the position is the node
              that the L5 order of the grid singles out among the maximal ones
    Status:   counterexample; complements EVT_idx.v

    ================= E/R/R разбор: позиция максимума =================
    Система — НЕ «точка максимума», а ПРАВИЛО «позиция максимума на сетке».
    Генеративный порядок Rules -> Roles -> Elements:

      Rules (L5)    : стадия n берёт сетку из n+1 ячейки; среди узлов с
                      наибольшим значением порядок L5 выделяет один.
      Roles (L4)    : «позиция максимума стадии» и «значение максимума стадии» —
                      две РАЗНЫЕ роли. У функции с двумя равными пиками роль
                      позиции занимают попеременно два узла.
      Elements      : узлы сетки k/(n+1); пики 1/3 и 1/2 (оба рациональны).

    ДИАГНОСТИКА (P4): «точка максимума» как один завершённый объект — роль-предел,
    которого у этой функции нет. На сетке из 6N+2 ячеек есть узел 1/2 и нет узла
    1/3 — позиция равна 1/2; на сетке из 6N+3 ячеек наоборот — позиция равна 1/3.
    Разность 1/6 не убывает, сколько бы стадий ни прошло. Процесс ЗНАЧЕНИЙ на этих
    стадиях равен 1 и сходится (EVT_idx.sup_process_is_Cauchy).
    Иррациональность предела тут ни при чём: обе точки рациональны; процесс,
    идущий к иррациональной точке, был бы процессом Коши.

    Main results:
      two_peaks_uniformly_continuous    : the function is uniformly continuous
      argmax_two_peaks_not_Cauchy       : ~ is_Cauchy (argmax_process two_peaks 0 1)
      argmax_process_need_not_be_Cauchy : exists such f on [0,1]

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Qminmax.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From ToS Require Import EVT_idx.
Import ListNotations.

Open Scope Q_scope.

Definition tent (c x : Q) : Q := 1 - 6 * Qabs (x - c).
Definition two_peaks (x : Q) : Q := Qmax 0 (Qmax (tent (1#3) x) (tent (1#2) x)).

Lemma tent_at : forall c x, x == c -> tent c x == 1.
Proof.
  intros c x H. unfold tent.
  assert (E : x - c == 0) by (rewrite H; ring).
  rewrite (Qabs_wd _ _ E). reflexivity.
Qed.

Lemma tent_ge_1 : forall c x, 1 <= tent c x -> x == c.
Proof.
  intros c x H. unfold tent in H.
  pose proof (Qabs_nonneg (x - c)) as Hn.
  assert (Hz : Qabs (x - c) <= 0) by lra.
  apply Qabs_Qle_condition in Hz. lra.
Qed.

Lemma two_peaks_ge_1_at_half : forall x, x == 1#2 -> 1 <= two_peaks x.
Proof.
  intros x H. unfold two_peaks.
  apply Qle_trans with (Qmax (tent (1#3) x) (tent (1#2) x)); [| apply Q.le_max_r].
  apply Qle_trans with (tent (1#2) x); [| apply Q.le_max_r].
  rewrite (tent_at _ _ H). apply Qle_refl.
Qed.

Lemma two_peaks_ge_1_at_third : forall x, x == 1#3 -> 1 <= two_peaks x.
Proof.
  intros x H. unfold two_peaks.
  apply Qle_trans with (Qmax (tent (1#3) x) (tent (1#2) x)); [| apply Q.le_max_r].
  apply Qle_trans with (tent (1#3) x); [| apply Q.le_max_l].
  rewrite (tent_at _ _ H). apply Qle_refl.
Qed.

Lemma two_peaks_ge_1 : forall x, 1 <= two_peaks x -> x == 1#3 \/ x == 1#2.
Proof.
  intros x H. unfold two_peaks in H.
  apply Q.max_le_iff in H. destruct H as [H | H].
  - exfalso. revert H. unfold Qle; simpl; lia.
  - apply Q.max_le_iff in H. destruct H as [H | H]; [left | right]; apply tent_ge_1; exact H.
Qed.

(* Узлы сетки. *)

Lemma grid_list_aux_elem : forall a b n k y,
  In y (grid_list_aux a b n k) -> exists j, (j <= k)%nat /\ y = grid_point a b n j.
Proof.
  intros a b n k. induction k as [|k IH]; intros y Hin; cbn [grid_list_aux In] in Hin.
  - destruct Hin as [H | []]. exists O. split; [lia | symmetry; exact H].
  - destruct Hin as [H | H].
    + exists (S k). split; [lia | symmetry; exact H].
    + destruct (IH y H) as [j [Hj Hy]]. exists j. split; [lia | exact Hy].
Qed.

Lemma argmax_point : forall f a b n, (n > 0)%nat ->
  exists j, (j <= n)%nat /\ argmax_on_grid f a b n = grid_point a b n j.
Proof.
  intros f a b n Hn. unfold argmax_on_grid; cbv zeta.
  assert (Hne : grid_list a b n <> []).
  { unfold grid_list. destruct n; [lia | discriminate]. }
  pose proof (nth_In (grid_list a b n) a (argmax_idx_bound f (grid_list a b n) a Hne)) as Hin.
  set (y := nth (argmax_idx f (grid_list a b n) a) (grid_list a b n) a) in *.
  clearbody y.
  unfold grid_list in Hin. destruct n as [|n']; [lia |].
  apply grid_list_aux_elem in Hin. exact Hin.
Qed.

Lemma gp01_scale : forall M j, (M > 0)%nat ->
  grid_point 0 1 M j * inject_Z (Z.of_nat M) == inject_Z (Z.of_nat j).
Proof.
  intros M j HM. unfold grid_point.
  assert (Hne : ~ inject_Z (Z.of_nat M) == 0) by (unfold inject_Z, Qeq; simpl; lia).
  field. exact Hne.
Qed.

Lemma gp01_eq_iff_cross : forall M j (c : Q), (M > 0)%nat ->
  (grid_point 0 1 M j == c <-> inject_Z (Z.of_nat j) == c * inject_Z (Z.of_nat M)).
Proof.
  intros M j c HM.
  assert (Hne : ~ inject_Z (Z.of_nat M) == 0) by (unfold inject_Z, Qeq; simpl; lia).
  pose proof (gp01_scale M j HM) as Hs.
  split; intro H.
  - rewrite <- Hs. rewrite H. reflexivity.
  - apply (Qmult_inj_r _ _ (inject_Z (Z.of_nat M)) Hne). rewrite Hs. exact H.
Qed.

Lemma gp01_half_iff : forall M j, (M > 0)%nat ->
  (grid_point 0 1 M j == 1#2 <-> (2 * j = M)%nat).
Proof.
  intros M j HM. rewrite (gp01_eq_iff_cross M j (1#2) HM).
  unfold Qeq, Qmult, inject_Z. cbn [Qnum Qden]. lia.
Qed.

Lemma gp01_third_iff : forall M j, (M > 0)%nat ->
  (grid_point 0 1 M j == 1#3 <-> (3 * j = M)%nat).
Proof.
  intros M j HM. rewrite (gp01_eq_iff_cross M j (1#3) HM).
  unfold Qeq, Qmult, inject_Z. cbn [Qnum Qden]. lia.
Qed.

(* Значение в позиции максимума не меньше значения в любом узле. *)
Lemma argmax_value_ge : forall f a b n j, (n > 0)%nat -> (j <= n)%nat ->
  f (grid_point a b n j) <= f (argmax_on_grid f a b n).
Proof.
  intros f a b n j Hn Hj.
  rewrite <- max_is_f_of_argmax.
  apply grid_value_le_max; [exact Hn |].
  apply grid_point_in_list; [exact Hn | exact Hj].
Qed.

Lemma argmax_at_half : forall N : nat,
  argmax_on_grid two_peaks 0 1 (S (6 * N + 1)) == 1#2.
Proof.
  intro N.
  destruct (argmax_point two_peaks 0 1 (S (6 * N + 1)) ltac:(lia)) as [j [Hj E]].
  assert (Hv : 1 <= two_peaks (argmax_on_grid two_peaks 0 1 (S (6 * N + 1)))).
  { apply Qle_trans with (two_peaks (grid_point 0 1 (S (6 * N + 1)) (S (3 * N)))).
    - apply two_peaks_ge_1_at_half. apply gp01_half_iff; lia.
    - apply argmax_value_ge; lia. }
  destruct (two_peaks_ge_1 _ Hv) as [H3 | H2]; [| exact H2].
  exfalso. rewrite E in H3. apply gp01_third_iff in H3; lia.
Qed.

Lemma argmax_at_third : forall N : nat,
  argmax_on_grid two_peaks 0 1 (S (6 * N + 2)) == 1#3.
Proof.
  intro N.
  destruct (argmax_point two_peaks 0 1 (S (6 * N + 2)) ltac:(lia)) as [j [Hj E]].
  assert (Hv : 1 <= two_peaks (argmax_on_grid two_peaks 0 1 (S (6 * N + 2)))).
  { apply Qle_trans with (two_peaks (grid_point 0 1 (S (6 * N + 2)) (S (2 * N)))).
    - apply two_peaks_ge_1_at_third. apply gp01_third_iff; lia.
    - apply argmax_value_ge; lia. }
  destruct (two_peaks_ge_1 _ Hv) as [H3 | H2]; [exact H3 |].
  exfalso. rewrite E in H2. apply gp01_half_iff in H2; lia.
Qed.

(* Главное: процесс позиций не Коши. *)
Theorem argmax_two_peaks_not_Cauchy :
  ~ is_Cauchy (argmax_process two_peaks 0 1).
Proof.
  intro HC.
  assert (Heps : (1#12) > 0) by reflexivity.
  destruct (HC (1#12) Heps) as [N HN].
  assert (Hm : (6 * N + 1 > N)%nat) by lia.
  assert (Hn : (6 * N + 2 > N)%nat) by lia.
  pose proof (HN (6 * N + 1)%nat (6 * N + 2)%nat Hm Hn) as H.
  unfold argmax_process in H.
  rewrite (argmax_at_half N) in H.
  rewrite (argmax_at_third N) in H.
  vm_compute in H. discriminate.
Qed.

(* Функция при этом липшицева с константой 6, а значит равномерно непрерывна;
   здесь проверяется только, что процесс значений на тех же шагах равен 1. *)
Lemma sup_two_peaks_ge_1_half : forall N : nat,
  1 <= sup_process two_peaks 0 1 (6 * N + 1)%nat.
Proof.
  intro N. unfold sup_process. rewrite max_is_f_of_argmax.
  apply Qle_trans with (two_peaks (grid_point 0 1 (S (6 * N + 1)) (S (3 * N)))).
  - apply two_peaks_ge_1_at_half. apply gp01_half_iff; lia.
  - apply argmax_value_ge; lia.
Qed.

(* Равномерная непрерывность: функция липшицева с константой 6. *)

Lemma tent_lip : forall c x y, tent c x <= tent c y + 6 * Qabs (x - y).
Proof.
  intros c x y. unfold tent.
  assert (Htri : Qabs (y - c) <= Qabs (y - x) + Qabs (x - c)).
  { assert (E : y - c == (y - x) + (x - c)) by ring.
    rewrite (Qabs_wd _ _ E). apply Qabs_triangle. }
  assert (Hsym : Qabs (y - x) == Qabs (x - y)).
  { assert (E : y - x == - (x - y)) by ring. rewrite (Qabs_wd _ _ E). apply Qabs_opp. }
  lra.
Qed.

Lemma two_peaks_nonneg : forall x, 0 <= two_peaks x.
Proof. intro x. unfold two_peaks. apply Q.le_max_l. Qed.

Lemma two_peaks_lip_one : forall x y,
  two_peaks x <= two_peaks y + 6 * Qabs (x - y).
Proof.
  intros x y.
  pose proof (Qabs_nonneg (x - y)) as Hd.
  pose proof (two_peaks_nonneg y) as Hy0.
  assert (H3 : tent (1#3) y <= two_peaks y).
  { unfold two_peaks.
    apply Qle_trans with (Qmax (tent (1#3) y) (tent (1#2) y)); [apply Q.le_max_l | apply Q.le_max_r]. }
  assert (H2 : tent (1#2) y <= two_peaks y).
  { unfold two_peaks.
    apply Qle_trans with (Qmax (tent (1#3) y) (tent (1#2) y)); [apply Q.le_max_r | apply Q.le_max_r]. }
  pose proof (tent_lip (1#3) x y) as L3.
  pose proof (tent_lip (1#2) x y) as L2.
  unfold two_peaks at 1.
  apply Q.max_lub; [lra |].
  apply Q.max_lub; lra.
Qed.

Lemma two_peaks_lipschitz : forall x y,
  Qabs (two_peaks x - two_peaks y) <= 6 * Qabs (x - y).
Proof.
  intros x y.
  pose proof (two_peaks_lip_one x y) as H1.
  pose proof (two_peaks_lip_one y x) as H2.
  assert (Hsym : Qabs (y - x) == Qabs (x - y)).
  { assert (E : y - x == - (x - y)) by ring. rewrite (Qabs_wd _ _ E). apply Qabs_opp. }
  apply Qabs_Qle_condition. split; lra.
Qed.

Theorem two_peaks_uniformly_continuous : forall a b,
  uniformly_continuous_on two_peaks a b.
Proof.
  intros a b eps Heps.
  exists (eps / 6). split.
  - apply Qlt_shift_div_l; [reflexivity | lra].
  - intros x y _ _ Hxy.
    apply Qle_lt_trans with (6 * Qabs (x - y)); [apply two_peaks_lipschitz |].
    assert (E : 6 * (eps / 6) == eps) by field.
    lra.
Qed.

(* Итог: при посылках теоремы об экстремуме процесс позиций может не быть Коши. *)
Theorem argmax_process_need_not_be_Cauchy :
  exists f : Q -> Q,
    uniformly_continuous_on f 0 1 /\ ~ is_Cauchy (argmax_process f 0 1).
Proof.
  exists two_peaks. split.
  - apply two_peaks_uniformly_continuous.
  - exact argmax_two_peaks_not_Cauchy.
Qed.

Print Assumptions argmax_two_peaks_not_Cauchy.
Print Assumptions two_peaks_uniformly_continuous.
Print Assumptions argmax_process_need_not_be_Cauchy.
