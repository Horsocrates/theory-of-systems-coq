(** * KnowledgeReasoningLaws.v — the second layer: which law governs each reasoning operation
      (turning "domain <-> principle" from a layout into a structural mapping)

    Builds on KnowledgeReasoning.v (the six operations as the срез-network's structural places).
    Each operation has a validity condition; the GOVERNING LAW is the law whose condition that
    validity is.  The assignment falls out of what the operation does:
      - fidelity operations (carry / read unchanged)  -> Identity      (Register out, Reflect in);
      - content-positing operations (produce new)      -> SufficientReason (Interpret/Frame/Synthesize);
      - the single free choice (axis not given)        -> NonContradiction (Frame);
      - the inference (bivalent forms, follows-from)   -> ExcludedMiddle + Order (Synthesize);
      - the between-operation joins the prior outputs  -> nodal: all converge (Relate).
    Flagship: the 2+1+2 structure of the LAWS maps onto the operations — load-bearing laws anchor
    the fidelity-ops and the choice, meta laws drive the movement (ground each posit / sequence the
    whole), the derived law appears only at the composite inference.

    STRUCTURAL CORE proved here (NOT the necessity that validity IS that law — that is the prose):
      - the exact fiber of each law (which operations it governs): fiber_*;
      - Identity brackets the process — entry (rank 0) and close (rank 5): identity_brackets;
      - the derived law (ExcludedMiddle) governs exactly one operation: fiber_ExcludedMiddle;
      - SufficientReason grounds every positing operation: sr_grounds_positing;
      - Order is the follows-from at Synthesize AND the whole dependency of layer 1: order_throughgoing;
      - Relate is nodal — governed by the four primary laws, the most of any op: relate_nodal/relate_max;
      - the law-classes are 2 load-bearing + 1 derived + 2 meta: law_classes_2_1_2;
      - domain <-> principle: each domain's governing laws = governs of its operation (principle lemmas).

    ============================== E/R/R разбор ==============================
    Elements: the six operations (layer 1); the five laws — two load-bearing (Identity,
              NonContradiction), one derived (ExcludedMiddle), two meta (SufficientReason = why,
              Order = how); each operation's validity condition.
    Roles:    a law governs the operation whose validity IS its condition — Identity = fidelity
              (entry/whole), SufficientReason = ground of each posit + gate of transitions,
              NonContradiction = honesty of the one free choice, Order = dependency of the whole +
              follows-from, ExcludedMiddle = bivalent inference forms; Relate = the nodal join.
    Rules:    (1) fidelity-ops -> Identity; (2) positing-ops -> SufficientReason; (3) the free
              choice -> NonContradiction; (4) the inference -> ExcludedMiddle + Order; (5) the
              between-op inherits the laws of what it joins (nodal).
    P4 diagnostic: the assignment is forced by each operation's validity condition, not chosen;
              multi-law principles (Objectivity, Rationalism, the nodal Comparison) are honest
              bundles; "forced" rests on "validity = a law's condition" (philosophical, in prose);
              the formalization VERIFIES the mapping's structure (the 2+1+2 correspondence, the
              bracket, the single derived law), not that reality "is governed thus".

    Honest scope: a governs-relation over finite enumerations + the layer-1 rank/dependency.  The
    value is the verified STRUCTURE of the derived mapping (bracket / recurrence / nodal join /
    2+1+2), exactly per the prose; the necessity itself is the prose argument.

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.
From ToS Require Import foundation.KnowledgeReasoning.

(* ===================================================================== *)
(*  The five laws (2 load-bearing + 1 derived + 2 meta) and their classes  *)
(* ===================================================================== *)

Inductive Law := Identity | NonContradiction | ExcludedMiddle | SufficientReason | Order.

Inductive LawClass := LoadBearing | Derived | Meta.

Definition law_class (l : Law) : LawClass :=
  match l with
  | Identity | NonContradiction => LoadBearing
  | ExcludedMiddle              => Derived
  | SufficientReason | Order    => Meta
  end.

(** The 2+1+2 architecture of the laws themselves. *)
Lemma law_classes_2_1_2 :
  map law_class [Identity; NonContradiction] = [LoadBearing; LoadBearing] /\
  map law_class [ExcludedMiddle] = [Derived] /\
  map law_class [SufficientReason; Order] = [Meta; Meta].
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  The governing relation: which laws each operation is held to            *)
(* ===================================================================== *)

Definition governs (o : Op) : list Law :=
  match o with
  | Register   => [Identity]                                          (* Присутствие: see A as A *)
  | Interpret  => [SufficientReason]                                  (* Корень: meaning needs a ground *)
  | Frame      => [NonContradiction; SufficientReason]                (* Объективность: honest, grounded choice *)
  | Relate     => [Identity; NonContradiction; SufficientReason; Order] (* nodal: joins the prior outputs *)
  | Synthesize => [SufficientReason; ExcludedMiddle; Order]           (* Рационализм: earned, valid, follows-from *)
  | Reflect    => [Identity]                                          (* Ограничение: see the срез as it is (mirror) *)
  end.

Definition law_governs (l : Law) (o : Op) : Prop := In l (governs o).

(* ===================================================================== *)
(*  PART I — the exact fiber of each law (which operations it governs)      *)
(* ===================================================================== *)

Lemma fiber_Identity :
  forall o, In Identity (governs o) <-> (o = Register \/ o = Relate \/ o = Reflect).
Proof. intro o; destruct o; simpl; intuition congruence. Qed.

Lemma fiber_NonContradiction :
  forall o, In NonContradiction (governs o) <-> (o = Frame \/ o = Relate).
Proof. intro o; destruct o; simpl; intuition congruence. Qed.

Lemma fiber_SufficientReason :
  forall o, In SufficientReason (governs o)
            <-> (o = Interpret \/ o = Frame \/ o = Synthesize \/ o = Relate).
Proof. intro o; destruct o; simpl; intuition congruence. Qed.

(** ★ The DERIVED law governs exactly one operation — the composite inference. *)
Lemma fiber_ExcludedMiddle :
  forall o, In ExcludedMiddle (governs o) <-> o = Synthesize.
Proof. intro o; destruct o; simpl; intuition congruence. Qed.

Lemma fiber_Order :
  forall o, In Order (governs o) <-> (o = Synthesize \/ o = Relate).
Proof. intro o; destruct o; simpl; intuition congruence. Qed.

(* ===================================================================== *)
(*  PART II — the structure: bracket, recurrence, nodal join               *)
(* ===================================================================== *)

(** ★★ Identity BRACKETS the process: it governs the entry (rank 0) and the close (rank 5) —
    the two pure-fidelity operations, the same law turned outward (to the object) and inward
    (to the knowing). *)
Lemma identity_brackets :
  In Identity (governs Register) /\ rank Register = 0 /\
  In Identity (governs Reflect)  /\ rank Reflect = 5.
Proof. repeat split; simpl; intuition congruence. Qed.

(** ★ SufficientReason RECURS at every content-positing operation (the pervasive "ground" demand). *)
Lemma sr_grounds_positing :
  In SufficientReason (governs Interpret) /\
  In SufficientReason (governs Frame) /\
  In SufficientReason (governs Synthesize).
Proof. repeat split; simpl; intuition congruence. Qed.

(** ★ Order is the follows-from at the inference AND the dependency of the whole traversal
    (layer 1): the сквозной Law of Order. *)
Lemma order_throughgoing :
  In Order (governs Synthesize) /\ depends_before Register Reflect.
Proof.
  split.
  - simpl; intuition congruence.
  - unfold depends_before; simpl; lia.
Qed.

(** ★★ Relate is NODAL: governed by the four primary laws (load-bearing + meta), and by the most
    laws of any operation — it is the join of the prior outputs. *)
Lemma relate_nodal :
  In Identity (governs Relate) /\ In NonContradiction (governs Relate) /\
  In SufficientReason (governs Relate) /\ In Order (governs Relate).
Proof. repeat split; simpl; intuition congruence. Qed.

Lemma relate_max : forall o, length (governs o) <= length (governs Relate).
Proof. intro o; destruct o; simpl; lia. Qed.

(* ===================================================================== *)
(*  PART III — domain <-> principle (the book's principles, derived)        *)
(* ===================================================================== *)

(** The laws governing a domain = governs of its operation. *)
Definition dom_law (d : Domain) : list Law := governs (op_of d).

Lemma principle_Recognition   : dom_law Recognition   = [Identity].
Proof. reflexivity. Qed.
Lemma principle_Clarification : dom_law Clarification  = [SufficientReason].
Proof. reflexivity. Qed.
Lemma principle_FrameChoice   : dom_law FrameChoice    = [NonContradiction; SufficientReason].
Proof. reflexivity. Qed.
Lemma principle_Comparison    : dom_law Comparison     = [Identity; NonContradiction; SufficientReason; Order].
Proof. reflexivity. Qed.
Lemma principle_Inference     : dom_law Inference      = [SufficientReason; ExcludedMiddle; Order].
Proof. reflexivity. Qed.
Lemma principle_Reflection    : dom_law Reflection     = [Identity].
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE — the 2+1+2 correspondence made concrete                      *)
(* ===================================================================== *)

(** ★★★ The architecture of the laws maps onto the operations: the derived law governs the single
    composite inference; load-bearing Identity brackets the process (entry rank 0 / close rank 5);
    load-bearing NonContradiction governs the choice (and the nodal join); meta SufficientReason
    grounds every positing operation; meta Order is the follows-from plus the whole dependency; and
    the nodal operation carries the most laws. *)
Theorem laws_capstone :
  (forall o, In ExcludedMiddle (governs o) <-> o = Synthesize) /\
  (In Identity (governs Register) /\ rank Register = 0 /\ In Identity (governs Reflect) /\ rank Reflect = 5) /\
  (forall o, In NonContradiction (governs o) <-> (o = Frame \/ o = Relate)) /\
  (In SufficientReason (governs Interpret) /\ In SufficientReason (governs Frame) /\ In SufficientReason (governs Synthesize)) /\
  (In Order (governs Synthesize) /\ depends_before Register Reflect) /\
  (forall o, length (governs o) <= length (governs Relate)).
Proof.
  split. { exact fiber_ExcludedMiddle. }
  split. { exact identity_brackets. }
  split. { exact fiber_NonContradiction. }
  split. { exact sr_grounds_positing. }
  split. { exact order_throughgoing. }
  exact relate_max.
Qed.

Print Assumptions laws_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  18 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Each operation of the срез-network is held to the law whose condition its *)
(*  validity is.  Fidelity-ops -> Identity (Register out / Reflect in, the    *)
(*  bracket: identity_brackets, ranks 0 and 5).  Positing-ops -> Sufficient   *)
(*  Reason (sr_grounds_positing).  The free choice -> NonContradiction        *)
(*  (Frame).  The inference -> ExcludedMiddle (fiber_ExcludedMiddle: the       *)
(*  DERIVED law at exactly one op) + Order (order_throughgoing: follows-from   *)
(*  + the whole dependency of layer 1).  Relate is nodal (relate_nodal/max).  *)
(*  The 2+1+2 of the laws (law_classes_2_1_2) maps onto the operations        *)
(*  (laws_capstone).  domain <-> principle is the book's assignment, derived  *)
(*  (principle lemmas).  The necessity (validity = a law's condition) is the prose *)
(*  derivation «Размышление» §«Второй слой».  Second layer over               *)
(*  KnowledgeReasoning.v.                                                      *)
(* ========================================================================= *)
