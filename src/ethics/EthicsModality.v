(** * EthicsModality.v — Модальность полярности правильно/неправильно (Н-3, СТРУКТУРА)

    Elements: статус (Pravilno/Nepravilno); выбор с признаком «порядок на кону» (at_stake);
              «неправое» с двумя НЕЗАВИСИМЫМИ параметрами: вид (намерение) и магнитуда (глубина).
    Roles:    статус = резкое ядро (двузначно); at_stake = демаркация этической зоны;
              вид/магнитуда = две ортогональные градуальные шкалы по ярусам.
    Rules:    L3 (исключённое третье — здесь КОНСТРУКТИВНО на решаемом фрагменте, без classic);
              L2 (исключающее: Pravilno ≠ Nepravilno).
    Status:   формализована СТРУКТУРА модальности — двузначность + «нет нейтрального третьего»,
              демаркация (полярность ⟺ порядок на кону; незадействование ≠ третье значение),
              ортогональность вид ⊥ магнитуда. НЕ ценностное суждение.
    STATUS: 14 Qed, 0 Admitted, 0 axioms (Print Assumptions: Closed under the global context)
    Author: Horsocrates | Date: June 2026

    Прозаический грунт: Книги/Этика/00 Этика — рабочая запись.md — Р-42/43 (нет третьего; демаркация),
      Р-53/54 (вид⊥магнитуда; резкое ядро + семейство шкал).
    ЧЕСТНОСТЬ (стена): на РЕШАЕМОМ фрагменте «нет третьего» доказано КОНСТРУКТИВНО (сильнее, чем
      нужно L3-classic); общий L3 = classic (foundation/Distinction.v). Здесь 0 аксиом.
*)

From Stdlib Require Import Arith.
From ToS Require Import ethics.EthicsStatus.

(* ===================================================================== *)
(*  I. РЕЗКОЕ ЯДРО: статус ДВУЗНАЧЕН, нет нейтрального ТРЕТЬЕГО (L3)       *)
(* ===================================================================== *)

Inductive Status := Pravilno | Nepravilno.

Definition status_of (thr fit : nat) : Status :=
  if thr <=? fit then Pravilno else Nepravilno.

(** Двузначность: ровно два значения (L3 — exhaustive). *)
Theorem status_bivalent : forall s : Status, s = Pravilno \/ s = Nepravilno.
Proof. intros [|]; [left|right]; reflexivity. Qed.

(** Исключающее (L2): два значения различны. *)
Theorem status_exclusive : Pravilno <> Nepravilno.
Proof. discriminate. Qed.

Theorem status_pravilno_iff : forall thr fit,
  status_of thr fit = Pravilno <-> pravilno thr fit.
Proof.
  intros th f. unfold status_of, pravilno. destruct (th <=? f) eqn:E.
  - split; intro H.
    + exact (proj1 (Nat.leb_le th f) E).
    + reflexivity.
  - split; intro H.
    + discriminate H.
    + apply (proj2 (Nat.leb_le th f)) in H. rewrite H in E. discriminate.
Qed.

Theorem status_nepravilno_iff : forall thr fit,
  status_of thr fit = Nepravilno <-> ~ pravilno thr fit.
Proof.
  intros th f. unfold status_of, pravilno. destruct (th <=? f) eqn:E.
  - split; intro H.
    + discriminate H.
    + exfalso. apply H. exact (proj1 (Nat.leb_le th f) E).
  - split; intro H.
    + intro Hp. apply (proj2 (Nat.leb_le th f)) in Hp. rewrite Hp in E. discriminate.
    + reflexivity.
Qed.

(** НЕТ НЕЙТРАЛЬНОГО ТРЕТЬЕГО: всякий предикат, исключающий ОБА значения, пуст (Р-42). *)
Theorem no_neutral_third :
  forall (P : Status -> Prop),
    (forall s, P s -> s <> Pravilno) ->
    (forall s, P s -> s <> Nepravilno) ->
    (forall s, ~ P s).
Proof.
  intros P H1 H2 s HP. destruct s.
  - apply (H1 Pravilno HP); reflexivity.
  - apply (H2 Nepravilno HP); reflexivity.
Qed.

(* ===================================================================== *)
(*  II. ДЕМАРКАЦИЯ: полярность ⟺ порядок НА КОНУ (Р-43)                   *)
(*      незадействование = ОТСУТСТВИЕ вопроса, не третье ЗНАЧЕНИЕ          *)
(* ===================================================================== *)

Record Choice := mkChoice { at_stake : bool ; cthr : nat ; cfit : nat }.

Definition engaged (c : Choice) : Prop := at_stake c = true.

(** Этический статус определён ⟺ порядок на кону; иначе НЕТ статуса (None). *)
Definition eth_status (c : Choice) : option Status :=
  if at_stake c then Some (status_of (cthr c) (cfit c)) else None.

Theorem engaged_iff_status : forall c,
  engaged c <-> exists s, eth_status c = Some s.
Proof.
  intro c. unfold engaged, eth_status. destruct (at_stake c) eqn:E.
  - split; intro H.
    + exists (status_of (cthr c) (cfit c)). reflexivity.
    + reflexivity.
  - split; intro H.
    + discriminate H.
    + destruct H as [s Hs]. discriminate Hs.
Qed.

Theorem not_engaged_no_status : forall c, ~ engaged c -> eth_status c = None.
Proof.
  intros c H. unfold eth_status. destruct (at_stake c) eqn:E.
  - exfalso. apply H. unfold engaged. rewrite E. reflexivity.
  - reflexivity.
Qed.

(** Незадействование (None) — НЕ третье ЗНАЧЕНИЕ полярности (Р-42/43). *)
Theorem non_engagement_not_third_value : forall c,
  eth_status c = None -> ~ exists s : Status, eth_status c = Some s.
Proof. intros c H [s Hs]. rewrite H in Hs. discriminate. Qed.

(** Когда задействовано — статус РЕЗКО один из двух (ядро резко). *)
Theorem sharp_core : forall c,
  engaged c -> eth_status c = Some Pravilno \/ eth_status c = Some Nepravilno.
Proof.
  intros c H. unfold eth_status, engaged in *. rewrite H.
  destruct (status_of (cthr c) (cfit c)); [left|right]; reflexivity.
Qed.

(* ===================================================================== *)
(*  III. ГРАДУАЛЬНОЕ = семейство по ярусам; ВИД ⊥ МАГНИТУДА (Р-53)        *)
(* ===================================================================== *)

(** вид = намерение (true=правда / false=не-правда); магнитуда = глубина искажения. *)
Definition Vid := bool.
Definition Magnituda := nat.

Record Wrong := mkWrong { vid : Vid ; magn : Magnituda }.

(** ОРТОГОНАЛЬНОСТЬ: любая комбинация (вид, магнитуда) реализуема. *)
Theorem vid_magn_independent :
  forall (v : Vid) (m : Magnituda), exists w : Wrong, vid w = v /\ magn w = m.
Proof. intros v m. exists (mkWrong v m). split; reflexivity. Qed.

(** Глубокая ЧЕСТНАЯ ошибка: магнитуда велика, вид = правда (НЕ зло). *)
Example deep_honest_error : exists w, vid w = true /\ magn w = 100.
Proof. exists (mkWrong true 100). split; reflexivity. Qed.

(** Мелкая ЛОЖЬ: магнитуда мала, вид = не-правда (зло). *)
Example shallow_lie : exists w, vid w = false /\ magn w = 1.
Proof. exists (mkWrong false 1). split; reflexivity. Qed.

(** Магнитуда НЕ определяет вид: одна глубина при обоих видах (⊥). *)
Theorem magn_does_not_fix_vid :
  exists w1 w2, magn w1 = magn w2 /\ vid w1 <> vid w2.
Proof.
  exists (mkWrong true 5), (mkWrong false 5).
  split; [reflexivity | discriminate].
Qed.

(** Вид НЕ определяет магнитуду: один вид при разной глубине (⊥). *)
Theorem vid_does_not_fix_magn :
  exists w1 w2, vid w1 = vid w2 /\ magn w1 <> magn w2.
Proof.
  exists (mkWrong false 1), (mkWrong false 100).
  split; [reflexivity | discriminate].
Qed.
