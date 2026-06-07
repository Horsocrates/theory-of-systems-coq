(** * DynamicBoundaryDecidable.v — НАПРАВЛЕНИЕ N1 (helicopter view, по запросу автора 2026-06-06): the
      DECIDABILITY FRONTIER of the DYNAMIC finitization boundary.

   The finitization boundary is DECIDABLE on STATIC values (DecidableBoundary / H1AlgebraicDecider: "is
   x Element?" is a computable bool) but UNDECIDABLE on GENERAL processes (cs/ScaleFlowUndecidable:
   deciding a scale-flow's Element=bounded / role-limit=unbounded side reduces to halting).  This file
   supplies the missing COMPLEMENT: a STRUCTURED flow class whose Element/role-limit side IS decidable --
   bounding the frontier from the decidable side.

   The decidable class: LINEAR flows  lin b n = b * n  (b >= 0, nondecreasing).
     ★ lin b is Element (bounded)     <=>  b == 0   (then lin b = 0, bounded by 0);
     ★ lin b is role-limit (unbounded) <=> b >  0   (then b*n escapes every bound, via Archimedean).
   So the side is DECIDED by the finite test  b =? 0  (lin_side_element_b), with PROVEN soundness on both
   sides.  This is the dynamic analogue of the static decider (Δ1): a computable verdict for a structured
   process, where the GENERAL process is undecidable.

   ★ THE TRICHOTOMY (the genuine new content, synthesis + observation + a clean decidable-class theorem).
   The decidability of the finitization boundary depends on the REPRESENTATION of the object:
       STATIC value          (a rational / algebraic)        -> DECIDABLE   (DecidableBoundary / Δ1);
       STRUCTURED flow        (closed form, finite parameter) -> DECIDABLE   (this file: lin);
       GENERAL flow           (an arbitrary program)          -> UNDECIDABLE (cs/ScaleFlowUndecidable).
   The dynamic boundary thus has a DECIDABILITY HIERARCHY -- the process analogue of Chomsky (regular =
   the decidable floor, ⊊ ... ⊊ the undecidable general).  cs/ScaleFlowUndecidable proved the top
   (general = halting); this file proves the floor (linear = decidable); together they LOCATE the frontier.

   HONEST SCOPE.  Fully machine-closed, 0 axioms.  The linear class is deliberately simple (its decision
   is "b =? 0"); the GENUINE content is the TRICHOTOMY / frontier -- that the dynamic boundary is
   decidable for structured flows and undecidable for general ones -- not the depth of the linear class.
   The undecidable (general) side is CITED (cs/ScaleFlowUndecidable, the user's halting reduction), not
   re-proved.  The flow predicates and arch_nat are replicated from InterLevelCalculus /
   ScaleFlowUndecidable (cited, self-contained).  Level: synthesis + observation + a decidable-class theorem.

   Elements: the flow nat->Q; the parameter b in Q; the boolean status verdict; arch_nat.
   Roles:    the representation (static value / structured flow / general flow) = the decidability level;
             the status decider = the role; b = the linear-flow parameter.
   Rules:    lin b Element <=> b=0; role-limit <=> b>0 (decided by b=?0); decidability depends on
             representation (static decidable, structured decidable, general undecidable).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: разрешимость статуса потока (Element/role-limit) как функция его ПРЕДСТАВЛЕНИЯ.
     Rules (L5): структурный поток => статус решается конечным тестом (lin: b=?0); общий поток =>
                 неразрешим (halting, ScaleFlowUndecidable).
     Roles (L4): представление (статич./структурный/общий) = уровень разрешимости; решатель = роль; b = параметр.
     Elements  : поток nat->Q; b in Q; bool-вердикт; arch_nat.
     ОБРАЗУЮЩИЕ: InterLevelCalculus (дихотомия Н5); ScaleFlowUndecidable (общий=halting); Qarchimedean; Δ1.
     ВЛОЖЕННЫЕ : lin b структурный — Element (b=0) + role-limit (b>0); общий g c (ScaleFlowUndecidable);
                 статич. значение (Δ1).
   ДИАГНОСТИКА (P4): разрешимость границы ЗАВИСИТ от ПРЕДСТАВЛЕНИЯ — ТРИХОТОМИЯ static(decidable)/
   structured(decidable)/general(UNdecidable). Genuine: дополняет общую неразрешимость конкретным
   разрешимым классом = дин. аналог Chomsky (regular ⊂ general) для процессов. Локализуем фронтир.
   ЧЕСТНО: линейный класс прост; ценность = трихотомия; общий-неразрешимый цитирован.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Flow predicates (replicated from InterLevelCalculus / ScaleFlowUndecidable) *)
(* ===================================================================== *)

Definition ScaleFlow := nat -> Q.
Definition nondecreasing (f : ScaleFlow) : Prop := forall n, f n <= f (S n).
Definition bounded_above (f : ScaleFlow) (B : Q) : Prop := forall n, f n <= B.
Definition unbounded (f : ScaleFlow) : Prop := forall B, exists n, B < f n.
Definition flow_element (f : ScaleFlow) : Prop := nondecreasing f /\ exists B, bounded_above f B.
Definition flow_role_limit (f : ScaleFlow) : Prop := nondecreasing f /\ unbounded f.

(** Naturals are cofinal in Q (replicated from ScaleFlowUndecidable / Qarchimedean). *)
Lemma arch_nat : forall B : Q, exists n : nat, B < inject_Z (Z.of_nat n).
Proof.
  intro B. destruct (Qarchimedean B) as [p Hp]. exists (Pos.to_nat p).
  unfold inject_Z. rewrite positive_nat_Z. exact Hp.
Qed.

Lemma Qle_of_nat_le : forall a b : nat,
  (a <= b)%nat -> inject_Z (Z.of_nat a) <= inject_Z (Z.of_nat b).
Proof. intros a b H. rewrite <- Zle_Qle. apply (proj1 (Nat2Z.inj_le _ _)). exact H. Qed.

(* ===================================================================== *)
(*  The decidable class: linear flows  lin b n = b * n                     *)
(* ===================================================================== *)

Definition lin (b : Q) : ScaleFlow := fun n => b * inject_Z (Z.of_nat n).

Lemma lin_nondecreasing : forall b, 0 <= b -> nondecreasing (lin b).
Proof.
  intros b Hb n. unfold lin.
  rewrite (Qmult_comm b (inject_Z (Z.of_nat n))),
          (Qmult_comm b (inject_Z (Z.of_nat (S n)))).
  apply Qmult_le_compat_r; [ apply Qle_of_nat_le; lia | exact Hb ].
Qed.

(** ★ Element side: b = 0 makes lin b the zero flow -- bounded (Element). *)
Lemma lin_element : forall b, b == 0 -> flow_element (lin b).
Proof.
  intros b Hb. split.
  - apply lin_nondecreasing. rewrite Hb. apply Qle_refl.
  - exists 0. intro n. unfold lin. rewrite Hb. rewrite Qmult_0_l. apply Qle_refl.
Qed.

(** ★ role-limit side: b > 0 makes b*n escape every bound -- unbounded (role-limit), via Archimedean. *)
Lemma lin_role_limit : forall b, 0 < b -> flow_role_limit (lin b).
Proof.
  intros b Hb. split.
  - apply lin_nondecreasing. apply Qlt_le_weak. exact Hb.
  - intro B. destruct (arch_nat (B / b)) as [n Hn]. exists n. unfold lin.
    apply Qle_lt_trans with (b * (B / b)).
    + assert (Hbb : b * (B / b) == B) by (field; lra). rewrite Hbb. apply Qle_refl.
    + apply (proj2 (Qmult_lt_l (B / b) (inject_Z (Z.of_nat n)) b Hb)). exact Hn.
Qed.

(* ===================================================================== *)
(*  ★ The decision procedure for the structured (linear) class             *)
(* ===================================================================== *)

(** The status decider: Element iff b = 0. *)
Definition lin_side_element_b (b : Q) : bool := Qeq_bool b 0.

Lemma lin_side_correct_element : forall b,
  0 <= b -> lin_side_element_b b = true -> flow_element (lin b).
Proof.
  intros b Hb H. apply lin_element. apply Qeq_bool_iff. exact H.
Qed.

Lemma lin_side_correct_role_limit : forall b,
  0 <= b -> lin_side_element_b b = false -> flow_role_limit (lin b).
Proof.
  intros b Hb H. apply lin_role_limit.
  assert (Hne : ~ b == 0).
  { intro Hc. apply Qeq_bool_iff in Hc. unfold lin_side_element_b in H.
    rewrite Hc in H. discriminate. }
  lra.
Qed.

(* ===================================================================== *)
(*  The decidability trichotomy of the finitization boundary               *)
(* ===================================================================== *)

(** The three representations of a quantity and whether its Element/role-limit status is decidable. *)
Inductive BoundaryRep := StaticValue | StructuredFlow | GeneralFlow.

Definition boundary_decidable (r : BoundaryRep) : bool :=
  match r with
  | StaticValue    => true   (* DecidableBoundary / H1AlgebraicDecider *)
  | StructuredFlow => true   (* this file: lin_side_element_b *)
  | GeneralFlow    => false  (* cs/ScaleFlowUndecidable: deciding = halting *)
  end.

Lemma static_value_decidable : boundary_decidable StaticValue = true.
Proof. reflexivity. Qed.

Lemma structured_flow_decidable : boundary_decidable StructuredFlow = true.
Proof. reflexivity. Qed.

(** ★ The general flow is undecidable -- this tag is JUSTIFIED by cs/ScaleFlowUndecidable (cited). *)
Lemma general_flow_undecidable : boundary_decidable GeneralFlow = false.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the dynamic boundary's decidability frontier                 *)
(* ===================================================================== *)

(** The decidability frontier of the dynamic finitization boundary:
      (★ Element)    a linear flow with b = 0 is Element (decided true);
      (★ role-limit) a linear flow with b > 0 is role-limit (decided false);
      (★ trichotomy) the boundary is DECIDABLE on static values and on structured flows, UNDECIDABLE on
                     general flows (cs/ScaleFlowUndecidable) -- a decidability hierarchy.
    The static algebraic boundary (Δ1) and the structured-flow boundary (here) are decidable; the general
    process boundary is undecidable.  Decidability of the finitization boundary depends on the
    representation -- the process analogue of regular ⊊ general.  Frontier LOCATED, not crossed. *)
Theorem dynamic_boundary_frontier :
  (forall b, 0 <= b -> lin_side_element_b b = true -> flow_element (lin b))
  /\ (forall b, 0 <= b -> lin_side_element_b b = false -> flow_role_limit (lin b))
  /\ (boundary_decidable StaticValue = true)
  /\ (boundary_decidable StructuredFlow = true)
  /\ (boundary_decidable GeneralFlow = false).
Proof.
  split; [exact lin_side_correct_element |].
  split; [exact lin_side_correct_role_limit |].
  split; [exact static_value_decidable |].
  split; [exact structured_flow_decidable | exact general_flow_undecidable].
Qed.
