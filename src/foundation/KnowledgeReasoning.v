(** * KnowledgeReasoning.v — reasoning's six operations as the strata of the срез-network
      (deriving the Architecture-of-Reasoning domains as functions of knowledge-movement)

    Formalizes the derivation "Размышление" (Книги/Теория Знания/Размышление.md): the срез is a
    BOUNDED, GROWING NETWORK of meant records; an operation of the knower touches exactly one of
    its five structural places (membership-from-outside / node-meaning / edge / derived-node /
    whole); the EDGE place SPLITS because the relation-axis is not given with the data — five
    places, six operations.  Reasoning (discursion) is the full ordered traversal; the six domains
    are the operation-places, their order is the dependency of outputs.

    STRUCTURAL CORE proved here (NOT the philosophical necessity — that is the prose):
      - place() sends the 6 operations onto 5 places; the edge place has exactly two preimages
        (Frame, Relate), every other place exactly one (edge_split / fiber lemmas); place is onto;
      - domain <-> operation is a bijection (dom_op_left / dom_op_right);
      - the dependency (consume the prior's output) is a STRICT TOTAL ORDER on the six
        (dep_irrefl / dep_trans / dep_total) — a linear chain (chain_order), the horizontal Order;
      - the two node-adders (Register, Synthesize) differ only by SOURCE (External vs Derived);
      - membership is monotone: no operation shrinks the срез (size_mono / run_mono) — no delete.

    ============================== E/R/R разбор ==============================
    Elements: the knower (difference-resolution / threshold / >=1 channel / finite attention);
              objective data (external presented differences); the срез = a bounded growing network
              of meant records (nodes / edges / boundary / whole); the relation-axis.
    Roles:    six operations = the structural places an operation can touch — Register (membership
              from outside), Interpret (a node's meaning), Frame + Relate (an edge: axis, then
              relating), Synthesize (a node from structure), Reflect (the whole, a tier up); the
              question = the driver (aims the channel), not an operation; return = repetition.
    Rules:    (1) data are external — enter only by Register across the threshold; (2) data != info
              — Interpret is separate; (3) knowledge is relational => the edge place is obligatory;
              (4) the axis is not given => the edge splits into Frame + Relate; (5) membership only
              grows (no correction) => one entry, from outside; node-adding is two-sourced (data
              from outside / inference from within); (6) reading the whole is a tier up (R4);
              (7) each operation consumes the prior's output — dependency, not a clock.
    P4 diagnostic: "exactly six" is EARNED (five places + the edge split), not posited; the weak
              link is the exhaustiveness of the five places (the batch / n-ary objection reduces to
              repeated edges — flagged open in prose); "reasoning/discursion" is DEFINED as the full
              traversal, assumed nowhere; the five governing laws (Metaphysics applied per
              operation) are a second layer, not introduced here.

    Honest scope: finite enumeration + elementary arithmetic (lia).  The value is the structural
    skeleton of the derivation — the place-map and its edge-split, the domain bijection, the
    dependency-as-linear-order, the single growing membership — exactly per the prose, with no claim
    that reality "has exactly six" (that is the prose argument, not a theorem here).

    STATUS: 22 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

(* ===================================================================== *)
(*  The five structural places + the six operations + the six domains      *)
(* ===================================================================== *)

(** The five places an operation can touch in the срез-network. *)
Inductive Place :=
  | MembershipIn   (* bring a node across the boundary, from outside *)
  | NodeMeaning    (* a node's content: raw -> meant (data -> information) *)
  | EdgeRelation   (* a relation between nodes — needs an axis not given *)
  | DerivedNode    (* a node produced from existing structure *)
  | Whole.         (* the срез as a whole: extent / boundary (a tier up) *)

(** The six operations (the edge place splits into two of them). *)
Inductive Op := Register | Interpret | Frame | Relate | Synthesize | Reflect.

(** The six reasoning domains. *)
Inductive Domain :=
  Recognition | Clarification | FrameChoice | Comparison | Inference | Reflection.

(* ===================================================================== *)
(*  PART I — place(): six operations onto five places, the edge splits      *)
(* ===================================================================== *)

Definition place (o : Op) : Place :=
  match o with
  | Register   => MembershipIn
  | Interpret  => NodeMeaning
  | Frame      => EdgeRelation
  | Relate     => EdgeRelation
  | Synthesize => DerivedNode
  | Reflect    => Whole
  end.

(** ★★ The edge place is the only one that splits: place o = EdgeRelation iff o is Frame or Relate. *)
Lemma edge_split : forall o, place o = EdgeRelation <-> (o = Frame \/ o = Relate).
Proof. intro o; destruct o; simpl; split; intro H; try discriminate; intuition congruence. Qed.

(** Every other place has exactly one operation (the fiber is a singleton). *)
Lemma fiber_MembershipIn : forall o, place o = MembershipIn <-> o = Register.
Proof. intro o; destruct o; simpl; split; intro H; congruence. Qed.
Lemma fiber_NodeMeaning : forall o, place o = NodeMeaning <-> o = Interpret.
Proof. intro o; destruct o; simpl; split; intro H; congruence. Qed.
Lemma fiber_DerivedNode : forall o, place o = DerivedNode <-> o = Synthesize.
Proof. intro o; destruct o; simpl; split; intro H; congruence. Qed.
Lemma fiber_Whole : forall o, place o = Whole <-> o = Reflect.
Proof. intro o; destruct o; simpl; split; intro H; congruence. Qed.

(** place is onto: every structural place is touched by some operation. *)
Lemma place_surjective : forall p, exists o, place o = p.
Proof.
  intro p; destruct p;
  [ exists Register | exists Interpret | exists Frame | exists Synthesize | exists Reflect ];
  reflexivity.
Qed.

Definition all_ops : list Op := [Register; Interpret; Frame; Relate; Synthesize; Reflect].
Definition all_places : list Place := [MembershipIn; NodeMeaning; EdgeRelation; DerivedNode; Whole].

Lemma ops_complete : forall o, In o all_ops.
Proof. intro o; destruct o; simpl; repeat (first [ left; reflexivity | right ]). Qed.
Lemma places_complete : forall p, In p all_places.
Proof. intro p; destruct p; simpl; repeat (first [ left; reflexivity | right ]). Qed.

(** Five places, six operations — the count behind the edge split. *)
Lemma count_places : length all_places = 5. Proof. reflexivity. Qed.
Lemma count_ops : length all_ops = 6. Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART II — domain <-> operation is a bijection                          *)
(* ===================================================================== *)

Definition op_of (d : Domain) : Op :=
  match d with
  | Recognition => Register | Clarification => Interpret | FrameChoice => Frame
  | Comparison  => Relate   | Inference     => Synthesize | Reflection  => Reflect
  end.

Definition dom_of (o : Op) : Domain :=
  match o with
  | Register => Recognition | Interpret => Clarification | Frame => FrameChoice
  | Relate   => Comparison  | Synthesize => Inference     | Reflect => Reflection
  end.

Lemma dom_op_left  : forall d, dom_of (op_of d) = d.
Proof. intro d; destruct d; reflexivity. Qed.
Lemma dom_op_right : forall o, op_of (dom_of o) = o.
Proof. intro o; destruct o; reflexivity. Qed.

(* ===================================================================== *)
(*  PART III — the dependency is a strict total order (a linear chain)      *)
(* ===================================================================== *)

(** Rank along the dependency: each operation consumes the output of lower rank. *)
Definition rank (o : Op) : nat :=
  match o with
  | Register => 0 | Interpret => 1 | Frame => 2 | Relate => 3 | Synthesize => 4 | Reflect => 5
  end.

(** o1 must precede o2 — o2 consumes o1's output. *)
Definition depends_before (o1 o2 : Op) : Prop := rank o1 < rank o2.

Lemma rank_inj : forall o1 o2, rank o1 = rank o2 -> o1 = o2.
Proof. intros o1 o2; destruct o1; destruct o2; simpl; intro H; try reflexivity; discriminate. Qed.

Lemma dep_irrefl : forall o, ~ depends_before o o.
Proof. intro o; unfold depends_before; lia. Qed.
Lemma dep_trans : forall a b c, depends_before a b -> depends_before b c -> depends_before a c.
Proof. unfold depends_before; intros a b c H1 H2; lia. Qed.
Lemma dep_total : forall o1 o2, o1 = o2 \/ depends_before o1 o2 \/ depends_before o2 o1.
Proof.
  intros o1 o2; unfold depends_before.
  destruct (Nat.lt_trichotomy (rank o1) (rank o2)) as [H | [H | H]].
  - right; left; exact H.
  - left; apply rank_inj; exact H.
  - right; right; exact H.
Qed.

(** The canonical dependency chain — the order of the six domains. *)
Lemma chain_order :
  depends_before Register Interpret /\ depends_before Interpret Frame /\
  depends_before Frame Relate /\ depends_before Relate Synthesize /\
  depends_before Synthesize Reflect.
Proof. unfold depends_before; simpl; repeat split; lia. Qed.

(* ===================================================================== *)
(*  PART IV — two node-sources; membership only grows (no delete)          *)
(* ===================================================================== *)

Inductive Source := External | Derived.

Definition adds_node (o : Op) : bool :=
  match o with Register | Synthesize => true | _ => false end.

Definition node_source (o : Op) : option Source :=
  match o with Register => Some External | Synthesize => Some Derived | _ => None end.

Lemma node_adders : forall o, adds_node o = true <-> (o = Register \/ o = Synthesize).
Proof. intro o; destruct o; simpl; split; intro H; try discriminate; intuition congruence. Qed.

(** The two node-adders differ exactly in source: one external (given data), one derived (inferred). *)
Lemma two_sources :
  node_source Register = Some External /\ node_source Synthesize = Some Derived /\ External <> Derived.
Proof. repeat split; discriminate. Qed.

(** Membership only grows: a node-adder raises the size by one, every other operation keeps it. *)
Definition step_size (o : Op) (n : nat) : nat := if adds_node o then S n else n.

Lemma size_mono : forall o n, n <= step_size o n.
Proof. intros o n; unfold step_size; destruct (adds_node o); lia. Qed.

Definition run (os : list Op) (n0 : nat) : nat := fold_left (fun n o => step_size o n) os n0.

Lemma run_mono : forall os n, n <= run os n.
Proof.
  unfold run; intro os; induction os as [| o os IH]; intro n; simpl.
  - lia.
  - apply Nat.le_trans with (step_size o n); [ apply size_mono | apply IH ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ The skeleton of the derivation, as one statement: five places / six operations with only
    the edge split; domain <-> operation a bijection; the dependency a strict total order; the two
    node-adders distinguished by source; membership monotone. *)
Theorem reasoning_capstone :
  (length all_places = 5 /\ length all_ops = 6) /\
  (forall o, place o = EdgeRelation <-> (o = Frame \/ o = Relate)) /\
  (forall d, dom_of (op_of d) = d) /\
  (forall o, op_of (dom_of o) = o) /\
  (forall o, ~ depends_before o o) /\
  (forall a b c, depends_before a b -> depends_before b c -> depends_before a c) /\
  (forall o1 o2, o1 = o2 \/ depends_before o1 o2 \/ depends_before o2 o1) /\
  (node_source Register = Some External /\ node_source Synthesize = Some Derived) /\
  (forall os n, n <= run os n).
Proof.
  split. { split; reflexivity. }
  split. { exact edge_split. }
  split. { exact dom_op_left. }
  split. { exact dom_op_right. }
  split. { exact dep_irrefl. }
  split. { exact dep_trans. }
  split. { exact dep_total. }
  split. { split; reflexivity. }
  exact run_mono.
Qed.

Print Assumptions reasoning_capstone.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  22 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The срез is a bounded, growing network of meant records.  An operation    *)
(*  touches one of FIVE structural places (membership-from-outside /          *)
(*  node-meaning / edge / derived-node / whole); the EDGE place splits into   *)
(*  Frame+Relate (the axis is not given) — five places, SIX operations        *)
(*  (edge_split, count_places=5, count_ops=6).  domain <-> operation is a     *)
(*  bijection (dom_op_left/right).  The dependency — consume the prior's       *)
(*  output — is a strict total order — a linear chain (dep_irrefl/trans/total, *)
(*  chain_order): the horizontal Law of Order, derived not posited.  The two  *)
(*  node-adders differ only by source (External given data / Derived         *)
(*  inference; two_sources); membership only grows, no delete (run_mono).     *)
(*  Reasoning/discursion = the full ordered traversal; the six domains = the  *)
(*  operation-places.  The governing laws (Metaphysics per operation) are a   *)
(*  second layer, not formalized here.  Anchors the prose derivation          *)
(*  «Размышление» (branch «Теория Знания»).                                   *)
(* ========================================================================= *)
