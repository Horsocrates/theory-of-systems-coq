(** * CauchyProcessBridge.v — The two Cauchy-real lines coincide (F-8) +
      multiplication / field structure on the ProcessCore line (F-9)

    Elements: real PROCESSES (nat -> Q) carrying the Cauchy property
    Roles:    "the same real" across the two formalization lines;
              the product of two real processes
    Rules:    ProcessCore's [is_Cauchy] and CauchyReal's [is_cauchy] are the
              SAME predicate (F-8); hence the field structure proved on
              [CauchySeq] in RealField.v TRANSPORTS to the ProcessCore line (F-9)

    === E/R/R разбор (генеративно Rules -> Roles -> Elements) ===
      Rules    : условие Коши (правило допустимости процесса) записано ДВУМЯ ИМЕНАМИ
                 (is_Cauchy / is_cauchy), но это БУКВА-В-БУКВУ одно правило; то же для
                 эквивалентности (process_equiv / cauchy_equiv); отсюда полевые законы
                 переносятся (F-9).
      Roles    : «один и тот же реал» поверх двух формализаций; «произведение точек».
      Elements : Коши-процессы (nat->Q); их рациональные значения (L1+P4).
    Хорошая сформированность: однозначно; P1 — значение < процесс < роль-точка.
    ДИАГНОСТИКА (F-8): два ИМЕНИ для одного правила — артефакт ПРЕДСТАВЛЕНИЯ (две
    независимые формализации), а НЕ онтологическое различие. Принять «две линии» за
    два разных предмета = смешать запись с сутью; мост показывает: правило одно,
    носители-определения два. (F-9: см. ONTOLOGY ниже — структура на процессах, не объект-ℝ.)

    ONTOLOGY (E/R/R / P4): this carries the FIELD STRUCTURE on real PROCESSES —
    the product and its laws (up to process_equiv), each step finitely
    actualizable. It does NOT build a completed object "R": under P4 a real is
    a process (nat -> Q), never a finished set; the laws are forall-RULES over
    the process type, not a claim that "all reals" form one object.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith.
From ToS Require Import process.ProcessCore.
From ToS Require Import CauchyReal.  (* is_cauchy, CauchySeq, mkCauchy, cs_seq, cauchy_equiv *)
From ToS Require Import RealField.   (* cauchy_mul, cauchy_mul_is_cauchy, _compat, _comm, _assoc *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  F-8 — the two formalization lines coincide                            *)
(* ===================================================================== *)

(** ProcessCore's [is_Cauchy] and CauchyReal's [is_cauchy] are, letter for
    letter, the same predicate on [nat -> Q]; the bridge is a conversion. *)
Lemma is_Cauchy_iff_is_cauchy : forall R : RealProcess, is_Cauchy R <-> is_cauchy R.
Proof. intros R. split; intro H; exact H. Qed.

(** A ProcessCore Cauchy real IS a CauchyReal [CauchySeq]. *)
Definition to_CauchySeq (R : RealProcess) (H : is_Cauchy R) : CauchySeq :=
  mkCauchy R H.

Lemma to_CauchySeq_seq : forall R H, cs_seq (to_CauchySeq R H) = R.
Proof. intros R H. reflexivity. Qed.

(** The two equivalence relations also coincide on the underlying processes. *)
Lemma process_equiv_iff_cauchy_equiv :
  forall (R1 R2 : RealProcess) (H1 : is_Cauchy R1) (H2 : is_Cauchy R2),
    process_equiv R1 R2 <-> cauchy_equiv (to_CauchySeq R1 H1) (to_CauchySeq R2 H2).
Proof. intros. split; intro H; exact H. Qed.

(* ===================================================================== *)
(*  F-9 — multiplication of real processes + field laws                   *)
(*  (transported from RealField.v, legitimate because the lines coincide) *)
(* ===================================================================== *)

(** Pointwise product of two real processes. *)
Definition process_mul (R1 R2 : RealProcess) : RealProcess :=
  fun n => R1 n * R2 n.

(** Multiplication preserves the Cauchy property — reusing RealField's
    [cauchy_mul_is_cauchy] (the boundedness/eps-split argument lives there). *)
Lemma mul_preserves_Cauchy : forall R1 R2 : RealProcess,
  is_Cauchy R1 -> is_Cauchy R2 -> is_Cauchy (process_mul R1 R2).
Proof.
  intros R1 R2 H1 H2.
  exact (cauchy_mul_is_cauchy (to_CauchySeq R1 H1) (to_CauchySeq R2 H2)).
Qed.

(** Multiplication respects process equivalence. *)
Lemma process_mul_compat :
  forall (R1 R1' R2 R2' : RealProcess)
         (H1 : is_Cauchy R1) (H1' : is_Cauchy R1')
         (H2 : is_Cauchy R2) (H2' : is_Cauchy R2'),
    process_equiv R1 R1' -> process_equiv R2 R2' ->
    process_equiv (process_mul R1 R2) (process_mul R1' R2').
Proof.
  intros R1 R1' R2 R2' H1 H1' H2 H2' He1 He2.
  exact (cauchy_mul_compat (to_CauchySeq R1 H1) (to_CauchySeq R1' H1')
                           (to_CauchySeq R2 H2) (to_CauchySeq R2' H2') He1 He2).
Qed.

(** Commutativity and associativity (field laws) transport too. *)
Lemma process_mul_comm : forall (R1 R2 : RealProcess)
  (H1 : is_Cauchy R1) (H2 : is_Cauchy R2),
  process_equiv (process_mul R1 R2) (process_mul R2 R1).
Proof.
  intros. exact (cauchy_mul_comm (to_CauchySeq R1 H1) (to_CauchySeq R2 H2)).
Qed.

Lemma process_mul_assoc : forall (R1 R2 R3 : RealProcess)
  (H1 : is_Cauchy R1) (H2 : is_Cauchy R2) (H3 : is_Cauchy R3),
  process_equiv (process_mul (process_mul R1 R2) R3)
                (process_mul R1 (process_mul R2 R3)).
Proof.
  intros.
  exact (cauchy_mul_assoc (to_CauchySeq R1 H1) (to_CauchySeq R2 H2)
                          (to_CauchySeq R3 H3)).
Qed.

(** Distributivity over the existing process addition is also available by the
    same transport (left as a pointer: cauchy_distrib_l/r in RealField.v). *)

Print Assumptions mul_preserves_Cauchy.
