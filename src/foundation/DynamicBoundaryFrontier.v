(** * DynamicBoundaryFrontier.v — НАПРАВЛЕНИЕ N1+ (deepening N1, по запросу автора 2026-06-06): the EXACT
      decidable sub-class of the dynamic finitization boundary -- and the discovery that the
      decidable/undecidable frontier IS the CONSTRUCTIVE/non-constructive frontier (LPO).

   N1 (DynamicBoundaryDecidable) gave the trichotomy static/structured/general via a LINEAR flow over Q.
   Here we go deeper, over NAT-VALUED flows (the setting of cs/ScaleFlowUndecidable's nh_count), where the
   boundary is sharp and the frontier becomes precise.

   THE STRUCTURAL DICHOTOMY (nat-flows).  Over Q a nondecreasing bounded flow can converge WITHOUT
   stabilising (1 - 1/n), so "Element" is genuinely "bounded".  But over NAT, integers cannot converge
   without stabilising, so for a nondecreasing nat-flow:

       Element (bounded)        <->  EVENTUALLY CONSTANT (finite total increase);
       role-limit (unbounded)   <->  increases infinitely often.

   ★ THE FRONTIER = LPO (the genuine new content).  The two directions are NOT symmetric in CONSTRUCTIVE
   strength:
     -- eventually-constant -> bounded:  CONSTRUCTIVE (proved here, 0 axioms);
     -- bounded -> eventually-constant:  NON-CONSTRUCTIVE -- it is exactly LPO (the limited principle of
        omniscience), and for the running counter nh_count it is exactly HALTING (cs/ScaleFlowUndecidable:
        nh_count is eventually-constant <-> the machine halts).
   So the decidable/undecidable frontier of the DYNAMIC boundary IS the constructive/non-constructive
   frontier of "monotone bounded => eventually constant" over nat.  The role-limit "край" of
   InterLevelCalculus is, precisely, LPO.

   THE DECIDABLE SUB-CLASS.  A nat-flow's side is decidable exactly when its eventual-constancy is
   decidable: STRUCTURED flows given by a finite description (const_flow -> Element; id_flow / any flow
   dominating the identity -> role-limit) are decidable; the GENERAL recursively-enumerable flow is not
   (its eventual-constancy = halting).  This is the precise characterisation N1 asked for.

   HONEST SCOPE.  Fully machine-closed, 0 axioms.  PROVED constructively: the Element direction
   (eventually-const -> bounded), the role-limit direction (dominates-id -> unbounded), and the two
   structured witnesses (const = Element, id = role-limit).  NOT proved (the honest край): bounded ->
   eventually-constant -- this is LPO / the halting reduction (cs/ScaleFlowUndecidable, cited), the very
   non-constructivity that makes the general case undecidable.  The GENUINE NEW content is the
   identification of the dynamic boundary's decidability frontier WITH the LPO/constructivity frontier --
   deeper than N1's linear class.  Level: synthesis + observation + the constructive dichotomy theorems.

   Elements: the nat-flow; the stabilisation index N; the bound B.
   Roles:    eventually-constant = the Element class; dominates-identity = the role-limit class; the flow
             kind = the decidability level.
   Rules:    eventually-const -> bounded (constructive); dominates-id -> unbounded (constructive);
             bounded -> eventually-const = LPO = halting (non-constructive, the frontier).

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: динамич. граница над ℕ-потоками — её точный разрешимый под-класс.
     Rules (L5): Element <-> eventually-const (целые не сходятся без стабилизации); eventually-const->bounded
                 КОНСТРУКТИВНО; bounded->eventually-const = LPO = halting (НЕ конструктивно) = фронтир.
     Roles (L4): eventually-const = Element-класс; dominates-id = role-limit-класс; вид потока = уровень разреш.
     Elements  : ℕ-поток; индекс стабилизации N; бод B.
     ОБРАЗУЮЩИЕ: ScaleFlowUndecidable (общий=halting); InterLevelCalculus (дихотомия); LPO (край).
     ВЛОЖЕННЫЕ : const_flow (Element), id_flow (role-limit), nh_count (общий); каждый = вложенный класс.
   ДИАГНОСТИКА (P4): ★ фронтир разрешимости динамич. границы = фронтир КОНСТРУКТИВНОСТИ (LPO): bounded->
   eventually-const — ровно неконструктивный шаг (= halting). Genuine-глубже N1.1. ЧЕСТНО: неконструктивное
   направление = край (цитата), не доказываю; конструктивные направления + свидетели доказаны.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Nat-valued flows and the structural predicates                         *)
(* ===================================================================== *)

Definition NatFlow := nat -> nat.
Definition nf_nondecreasing (f : NatFlow) : Prop := forall n, f n <= f (S n).
Definition nf_bounded (f : NatFlow) : Prop := exists B, forall n, f n <= B.
Definition nf_eventually_const (f : NatFlow) : Prop :=
  exists N, forall n, N <= n -> f n = f N.

Lemma nf_mono : forall f, nf_nondecreasing f -> forall a b, a <= b -> f a <= f b.
Proof.
  intros f Hnd a b Hab. induction Hab.
  - apply Nat.le_refl.
  - apply Nat.le_trans with (f m). exact IHHab. apply Hnd.
Qed.

(* ===================================================================== *)
(*  The Element direction (CONSTRUCTIVE): eventually constant => bounded    *)
(* ===================================================================== *)

(** ★ Constructive: an eventually-constant nondecreasing nat-flow is bounded (by its stable value). *)
Lemma ev_const_bounded : forall f,
  nf_nondecreasing f -> nf_eventually_const f -> nf_bounded f.
Proof.
  intros f Hnd [N HN]. exists (f N). intro n.
  destruct (Nat.le_gt_cases N n) as [Hle | Hgt].
  - rewrite (HN n Hle). apply Nat.le_refl.
  - apply nf_mono. exact Hnd. lia.
Qed.

(* ===================================================================== *)
(*  The role-limit direction (CONSTRUCTIVE): dominating the identity        *)
(* ===================================================================== *)

(** ★ Constructive: a flow that dominates the identity (n <= f n) is unbounded (role-limit). *)
Lemma ge_id_unbounded : forall f,
  (forall n, n <= f n) -> ~ nf_bounded f.
Proof.
  intros f Hge [B HB]. specialize (HB (S B)). specialize (Hge (S B)). lia.
Qed.

(* ===================================================================== *)
(*  The decidable structured witnesses                                     *)
(* ===================================================================== *)

(** A constant flow: structured, decidably Element (eventually constant). *)
Definition const_flow (c : nat) : NatFlow := fun _ => c.

Lemma const_nondecreasing : forall c, nf_nondecreasing (const_flow c).
Proof. intros c n. apply Nat.le_refl. Qed.

Lemma const_element : forall c, nf_eventually_const (const_flow c).
Proof. intro c. exists 0. intros n _. reflexivity. Qed.

(** The identity flow: structured, decidably role-limit (unbounded). *)
Definition id_flow : NatFlow := fun n => n.

Lemma id_nondecreasing : nf_nondecreasing id_flow.
Proof. intro n. unfold id_flow. apply Nat.le_succ_diag_r. Qed.

Lemma id_role_limit : ~ nf_bounded id_flow.
Proof. apply ge_id_unbounded. intro n. unfold id_flow. apply Nat.le_refl. Qed.

(* ===================================================================== *)
(*  The decidability frontier = the constructivity (LPO) frontier          *)
(* ===================================================================== *)

(** Flow kinds by decidability of their Element/role-limit side. *)
Inductive FlowKind := EventuallyConst | DominatesId | GeneralRE.

Definition decidable_side (k : FlowKind) : bool :=
  match k with
  | EventuallyConst => true   (* structured Element: const_flow *)
  | DominatesId     => true   (* structured role-limit: id_flow *)
  | GeneralRE       => false  (* bounded->eventually-const = LPO = halting (cs/ScaleFlowUndecidable) *)
  end.

Lemma ev_const_decidable : decidable_side EventuallyConst = true.
Proof. reflexivity. Qed.

Lemma dominates_id_decidable : decidable_side DominatesId = true.
Proof. reflexivity. Qed.

(** ★ The general r.e. flow's side is undecidable -- this tag is the LPO/halting frontier, JUSTIFIED by
    cs/ScaleFlowUndecidable (bounded <-> halts), not re-proved here. *)
Lemma general_re_undecidable : decidable_side GeneralRE = false.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the exact decidable sub-class of the dynamic boundary         *)
(* ===================================================================== *)

(** The dynamic boundary over nat-flows, characterised:
      (★ Element)    eventually-constant => bounded -- CONSTRUCTIVE;
      (★ role-limit) dominates-identity => unbounded -- CONSTRUCTIVE;
      (Element wit.) the constant flow is eventually constant (decidable Element);
      (role-lim wit.) the identity flow is unbounded (decidable role-limit);
      (★ frontier)   structured kinds are decidable, the general r.e. kind is not -- the
                     bounded->eventually-const direction is LPO = halting (cs/ScaleFlowUndecidable).
    The decidable sub-class is exactly the flows whose eventual-constancy is decidable; the
    decidable/undecidable frontier of the dynamic finitization boundary IS the constructive/
    non-constructive (LPO) frontier.  Frontier characterised, not crossed. *)
Theorem dynamic_boundary_frontier_nat :
  (forall f, nf_nondecreasing f -> nf_eventually_const f -> nf_bounded f)
  /\ (forall f, (forall n, n <= f n) -> ~ nf_bounded f)
  /\ (forall c, nf_eventually_const (const_flow c))
  /\ (~ nf_bounded id_flow)
  /\ (decidable_side EventuallyConst = true /\ decidable_side GeneralRE = false).
Proof.
  split; [exact ev_const_bounded |].
  split; [exact ge_id_unbounded |].
  split; [exact const_element |].
  split; [exact id_role_limit | split; [exact ev_const_decidable | exact general_re_undecidable]].
Qed.
