(** * KnowledgeCollective.v — COLLECTIVE knowledge held by NO single member: distributed parts,
      composition across connections, and tradition persisting across turnover — structural, no
      group consciousness

    Direction (4), the honest STRUCTURAL route (author's choice 2026-06-13).  How can a collective
    hold knowledge K that no individual member holds?  Three structural mechanisms, each shown
    concretely, all requiring CONNECTIVITY (no group-field needed):

      (A) JIGSAW: K = the union of proper parts; each member holds a proper part; the collective
          (the union) holds K; no member does.
      (B) COMPOSITION (the gem): collective knowledge = the transitive CLOSURE of the union of
          members' facts.  Member 1 holds A->B, member 2 holds B->C; the collective knows A->C (by
          composing across the connection), and NEITHER member holds A->C.  Strictly: closure > union
          > any member.
      (C) TRADITION across time (Koshima): knowledge transmitted along a founded chain PERSISTS in
          the collective for all time though the holders turn over — so the knowledge is present at
          every generation while NO individual holds it throughout.

    CONNECTIVITY is load-bearing: disconnected members (no shared node) bridge nothing — the closure
    adds no cross-fact (disconnected_no_bridge).  Without connection it is scattered ignorance, not
    collective knowledge.

    Empirical anchor (honest): the Koshima macaques (Imo's sweet-potato washing, 1953-; Kawai 1965)
    spread GRADUALLY along kin/social links by observational learning — confirming the connectivity
    account; the troop's washing TRADITION is collective knowledge no single (now-living) monkey
    founded or holds throughout (mechanism C).  The "hundredth monkey effect" (acausal cross-island
    jump; Watson 1979, used for morphic resonance) is DEBUNKED (Watson extrapolated from anecdote;
    Amundson 1985) and is NOT modeled here — it would require a non-connective channel, a posit the
    data refute.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      R-composition (L5): collective knowledge = the transitive closure of the union of members'
                 facts (compose along connections).
      R-connectivity: composition needs shared nodes (links); disconnected members bridge nothing.
      R-transmission/time: knowledge passes along a founded chain (= knowledge_that_transfers), so a
                 TRADITION persists across generations though holders turn over.
      R-level (P1): the collective is a higher-level system; its knowledge is a role ABSENT from any
                 element (emergence) — no group consciousness needed.
    Roles (L4): member = local holder of a part / a fact; collective = holder of the closure / the
      tradition; links = the composition channels; tradition = the persistence across time.
    Elements (L1+P4): items / facts (edges); members; the holding relation; time (generations).
    P4 diagnostic (could it be otherwise?):
      The collective holds what no member holds — FORCED when knowledge is distributed (proper parts),
      composed (closure > members), or traditional (persists while holders turn over).  All three
      require CONNECTIVITY / transmission; without it, scattered, no collective knowledge.  This is
      P1-level emergence (whole vs part), structural — NOT a group mind.
    Honesty wall:
      STRUCTURAL only — the collective holds K via assembly / transmission; no "group consciousness" /
      group-qualia.  The acausal group-field (the Koshima myth) is NOT modeled — it would be a
      non-connective channel, a flagged posit the data refute.  Bridges (transmission ->
      KnowledgeProcess.knowledge_that_transfers, collective-as-subject -> KnowledgeSubject, holder
      turnover -> KnowledgeMutability variant) are in prose.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Relations.

(* ===================================================================== *)
(*  Helper — a forward-closed set traps the transitive closure            *)
(* ===================================================================== *)

(** If S is closed under R and holds at a, it holds at every R-closure-reachable b. *)
Lemma reach_closed :
  forall (A : Type) (R : A -> A -> Prop) (S : A -> Prop),
    (forall x y, R x y -> S x -> S y) ->
    forall a b, clos_trans A R a b -> S a -> S b.
Proof.
  intros A R S Hstep a b H. induction H as [x y Hxy | x y z H1 IH1 H2 IH2].
  - intro Hx. exact (Hstep x y Hxy Hx).
  - intro Hx. apply IH2. apply IH1. exact Hx.
Qed.

(* ===================================================================== *)
(*  (A) JIGSAW — the collective (union) holds K; no member's part does     *)
(*  K = {0,1}; member 1 holds {0}, member 2 holds {1}                       *)
(* ===================================================================== *)

Definition K      (n : nat) : Prop := n = 0 \/ n = 1.
Definition part1  (n : nat) : Prop := n = 0.
Definition part2  (n : nat) : Prop := n = 1.
Definition union2 (n : nat) : Prop := part1 n \/ part2 n.

(** ★★ The collective (the union of parts) holds the whole K, yet each member holds only a proper
    part — neither holds all of K. *)
Theorem jigsaw_collective_holds_none_does :
  (forall n, K n <-> union2 n)
  /\ (exists n, K n /\ ~ part1 n)
  /\ (exists n, K n /\ ~ part2 n).
Proof.
  split; [ | split ].
  - intro n. unfold K, union2, part1, part2. tauto.
  - exists 1. unfold K, part1. split; [ right; reflexivity | intro E; discriminate E ].
  - exists 0. unfold K, part2. split; [ left; reflexivity | intro E; discriminate E ].
Qed.

(* ===================================================================== *)
(*  (B) COMPOSITION — the collective knows a composed fact NO member holds *)
(*  member 1 holds 0->1, member 2 holds 1->2; collective knows 0->2         *)
(* ===================================================================== *)

Definition c_holds1   (x y : nat) : Prop := x = 0 /\ y = 1.   (* member 1: A -> B *)
Definition c_holds2   (x y : nat) : Prop := x = 1 /\ y = 2.   (* member 2: B -> C *)
Definition conn_union (x y : nat) : Prop := c_holds1 x y \/ c_holds2 x y.

(** Collective knowledge = the transitive closure of the union of members' facts. *)
Definition collective_knows := clos_trans nat conn_union.

(** ★★★ The collective knows the COMPOSED fact 0->2 (A->C), which NEITHER member holds — knowledge
    held by no single one, residing in the composition across the connection. *)
Theorem connected_new_fact :
  collective_knows 0 2 /\ ~ c_holds1 0 2 /\ ~ c_holds2 0 2.
Proof.
  split; [ | split ].
  - apply t_trans with (y := 1).
    + apply t_step. left. split; reflexivity.
    + apply t_step. right. split; reflexivity.
  - intros [E1 E2]. discriminate E2.
  - intros [E1 E2]. discriminate E1.
Qed.

(** ★★ The punchline existential: there IS knowledge the collective holds that no member holds. *)
Theorem collective_knows_what_no_member_knows :
  exists x y, collective_knows x y /\ ~ c_holds1 x y /\ ~ c_holds2 x y.
Proof. exists 0, 2. exact connected_new_fact. Qed.

(* ===================================================================== *)
(*  CONNECTIVITY is load-bearing — disconnected members bridge nothing     *)
(*  member 1 holds 0->1, member 2 holds 2->3 (no shared node)               *)
(* ===================================================================== *)

Definition disc_R (x y : nat) : Prop := (x = 0 /\ y = 1) \/ (x = 2 /\ y = 3).
Definition comp0  (x : nat) : Prop := x = 0 \/ x = 1.   (* the component reachable from 0 *)

(** ★★ Without connection the collective knows NO bridging fact: disconnected members (0->1 and
    2->3, no shared node) do not compose to 0->3.  Connectivity is what makes collective knowledge,
    not scattered ignorance. *)
Theorem disconnected_no_bridge_03 : ~ clos_trans nat disc_R 0 3.
Proof.
  intro H.
  assert (Hc : comp0 3).
  { refine (reach_closed nat disc_R comp0 _ 0 3 H _).
    - intros x y Hxy Hx. destruct Hxy as [[Hx0 Hy1] | [Hx2 Hy3]]; subst.
      + right; reflexivity.
      + destruct Hx as [E | E]; discriminate E.
    - left; reflexivity. }
  destruct Hc as [E | E]; discriminate E.
Qed.

(* ===================================================================== *)
(*  (C) TRADITION across time — persists though holders turn over (Koshima)*)
(* ===================================================================== *)

Section Tradition.
Variable held_at : nat -> nat -> Prop.   (* member m holds the knowledge at generation t *)
Hypothesis present_at_0 : exists m, held_at 0 m.                                   (* the innovator *)
Hypothesis transmits : forall t, (exists m, held_at t m) -> (exists m, held_at (S t) m). (* passed on *)
Hypothesis turnover : forall m, exists T, forall t, (T <= t)%nat -> ~ held_at t m. (* each member is finite *)

(** ★★ The TRADITION persists: the collective holds the knowledge at EVERY generation, by
    transmission along the chain. *)
Theorem tradition_persists : forall t, exists m, held_at t m.
Proof. induction t as [|t IH]; [ exact present_at_0 | apply transmits; exact IH ]. Qed.

(** ★★★ Yet NO individual holds it throughout: every member is present only finitely (turnover), so
    no single member holds the knowledge at all times — the tradition (collective, across time) holds
    what no individual holds throughout.  (Koshima: the troop knows potato-washing across
    generations; no monkey does throughout.) *)
Theorem no_individual_holds_throughout : forall m, ~ (forall t, held_at t m).
Proof.
  intros m Hall. destruct (turnover m) as [T HT].
  apply (HT T (Nat.le_refl T)). apply Hall.
Qed.

End Tradition.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Collective knowledge held by no single member: (B) the collective knows a composed fact no
    member holds, and (connectivity) disconnected members bridge nothing — so the surplus is exactly
    the composition across connections. *)
Theorem collective_capstone :
  (exists x y, collective_knows x y /\ ~ c_holds1 x y /\ ~ c_holds2 x y)
  /\ (~ clos_trans nat disc_R 0 3).
Proof.
  split.
  - exact collective_knows_what_no_member_knows.
  - exact disconnected_no_bridge_03.
Qed.

Print Assumptions collective_capstone.
Print Assumptions connected_new_fact.
Print Assumptions no_individual_holds_throughout.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Collective knowledge held by NO single member, three structural ways:     *)
(*  (A) jigsaw_collective_holds_none_does - the union holds K, each member a   *)
(*  proper part; (B) connected_new_fact / collective_knows_what_no_member_     *)
(*  knows - the collective knows a COMPOSED fact (0->2) neither member holds,  *)
(*  the closure exceeding the union; (C) tradition_persists +                  *)
(*  no_individual_holds_throughout - the tradition persists across time though *)
(*  holders turn over, so no individual holds it throughout (Koshima).         *)
(*  CONNECTIVITY is load-bearing: disconnected_no_bridge_03 - disconnected     *)
(*  members compose nothing.  Structural, P1-level emergence; NO group         *)
(*  consciousness.  The acausal group-field (Koshima "hundredth monkey" myth)  *)
(*  is excluded, not modeled.  Direction (4); bridges in prose.              *)
(* ========================================================================= *)
