(** * ERRLink.v — The LINK: the rule of interaction of systems — the named capstone of the canon

    Canon (TS-9/TS-10, working journal Knigi/Teoriya Sistem/00, 2026-07-21):
    systems do not "sum" — they INTERACT, or form a NEW system in which both
    are represented; the LINK is the rule of interaction; without a link
    systems stand side by side; boundaries are taken by the operator; one
    element can occupy roles of many systems (the simul); record-systems
    stand on top of the STATUSES of other systems (the table over results).
    This file gives the canon its named machine carrier, closing the three
    correspondence gaps of the audit (TS-11): (a) the link by name, (b) the
    shared element, (c) the record-system over statuses.

    Elements: carriers of two systems; the sum and pair carriers; boards of
              a simul; games with interiors; results (statuses); points.
    Roles:    links_across = the LINK (relates across the boundary);
              the shared element (one master on many boards); the table as
              the record-system reading statuses.
    Rules:    the no-link poles are theorems (the sum never relates across;
              the separable pair is exactly a product); a link EXCEEDS both
              poles — a linked composite is not any sum, the parity-linked
              pair is not any product; a linked whole IS a system
              (equivalence): interaction births a system; the table is a
              function of statuses alone and conserves total points.
    Status:   all proved; self-contained (sum_rel/separability replicated
              locally per the stale-.vo house convention; canonical twins:
              ERRCoproduct.sum_rel, ERREntanglement.separable).
    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. The link: relating across the boundary                     *)
(* ================================================================ *)

(** Replicated from ERRCoproduct.v (self-contained): the sum baseline —
    relate only within a summand, never across. *)
Definition sum_rel {A B : Type} (R1 : A -> A -> Prop) (R2 : B -> B -> Prop)
  (x y : A + B) : Prop :=
  match x, y with
  | inl a, inl a' => R1 a a'
  | inr b, inr b' => R2 b b'
  | _, _ => False
  end.

Definition sum_decomposable {A B : Type}
  (R : A + B -> A + B -> Prop) : Prop :=
  exists R1 R2, forall x y, R x y <-> sum_rel R1 R2 x y.

(** THE LINK: the rule relates something across the boundary of the
    two systems. *)
Definition links_across {A B : Type}
  (R : A + B -> A + B -> Prop) : Prop :=
  exists a b, R (inl a) (inr b) \/ R (inr b) (inl a).

(** Without a link — side by side: the sum baseline never links. *)
Theorem sum_never_links : forall (A B : Type) R1 R2,
  ~ links_across (@sum_rel A B R1 R2).
Proof. intros A B R1 R2 [a [b [H | H]]]; exact H. Qed.

(** A link exceeds every sum: a linked composite is not decomposable
    into a "side by side". *)
Theorem linked_not_sum : forall (A B : Type) (R : A + B -> A + B -> Prop),
  links_across R -> ~ sum_decomposable R.
Proof.
  intros A B R [a [b [H | H]]] [R1 [R2 HR]].
  - exact (proj1 (HR _ _) H).
  - exact (proj1 (HR _ _) H).
Qed.

(** Interaction births a system: a linked whole that IS an equivalence —
    rule-governed through and through, hence a system, and reducible to
    no sum of its sides. *)
Definition whole : unit + unit -> unit + unit -> Prop := fun _ _ => True.

Theorem whole_is_system :
  (forall x, whole x x) /\
  (forall x y, whole x y -> whole y x) /\
  (forall x y z, whole x y -> whole y z -> whole x z).
Proof.
  split; [intros x; exact I |
  split; [intros x y _; exact I | intros x y z _ _; exact I]].
Qed.

Theorem whole_links : links_across whole.
Proof. exists tt, tt. left. exact I. Qed.

Theorem interaction_births_system :
  links_across whole /\ ~ sum_decomposable whole.
Proof.
  split; [exact whole_links | exact (linked_not_sum _ _ _ whole_links)].
Qed.

(* ================================================================ *)
(** ** 2. The linked pair is not a product (the parity witness)      *)
(* ================================================================ *)

(** Replicated in spirit from ERREntanglement.v: separability = being a
    product, componentwise. *)
Definition prod_sep {A B : Type} (R : A * B -> A * B -> Prop) : Prop :=
  exists (R1 : A -> A -> Prop) (R2 : B -> B -> Prop),
    forall a b c d, R (a, b) (c, d) <-> (R1 a c /\ R2 b d).

(** The cross-constraint: the joint parity — "the music answers the
    board": the sides are correlated, not independent. *)
Definition parity : bool * bool -> bool * bool -> Prop :=
  fun p q => xorb (fst p) (snd p) = xorb (fst q) (snd q).

Lemma parity_tf_ft : parity (true, false) (false, true).
Proof. reflexivity. Qed.

Lemma parity_tt_ff : parity (true, true) (false, false).
Proof. reflexivity. Qed.

Lemma parity_refl_tf : parity (true, false) (true, false).
Proof. reflexivity. Qed.

Lemma not_parity_tf_ff : ~ parity (true, false) (false, false).
Proof. intros H. discriminate H. Qed.

(** The linked pair factors into no product: the whole with a
    cross-constraint is neither a sum nor a pair of independents. *)
Theorem parity_not_separable : ~ prod_sep parity.
Proof.
  intros [R1 [R2 HR]].
  assert (H1 := proj1 (HR true false false true) parity_tf_ft).
  assert (H2 := proj1 (HR true true false false) parity_tt_ff).
  assert (H3 := proj1 (HR true false true false) parity_refl_tf).
  apply not_parity_tf_ff.
  apply (proj2 (HR true false false false)).
  split; [exact (proj1 H2) | exact (proj2 H3)].
Qed.

(* ================================================================ *)
(** ** 3. One element on the roles of many systems (the simul)       *)
(* ================================================================ *)

Definition master : nat := 7.

(** Every board's operator role is filled by the SAME element. *)
Definition board_operator (k : nat) : nat := master.

Theorem one_element_many_boards : forall k1 k2,
  board_operator k1 = board_operator k2.
Proof. intros k1 k2. reflexivity. Qed.

(** The boards stay distinct systems: states differ, the filler is
    shared — systems intersect by an element without merging. *)
Definition board_state (k : nat) : nat := k.

Theorem boards_not_merged : exists k1 k2,
  k1 <> k2 /\ board_state k1 <> board_state k2 /\
  board_operator k1 = board_operator k2.
Proof.
  exists 0, 1. split; [lia | split; [unfold board_state; lia | reflexivity]].
Qed.

(* ================================================================ *)
(** ** 4. A record-system on top of statuses (the table)             *)
(* ================================================================ *)

Inductive Result : Type := WinA | WinB | Draw.

Record Game : Type := mkGame {
  interior : nat;   (** the game's own inner course — invisible to the table *)
  result   : Result (** the STATUS the rules assigned *)
}.

Fixpoint pointsA (rs : list Result) : nat :=
  match rs with
  | []          => 0
  | WinA :: t   => 2 + pointsA t
  | Draw :: t   => 1 + pointsA t
  | WinB :: t   => pointsA t
  end.

Fixpoint pointsB (rs : list Result) : nat :=
  match rs with
  | []          => 0
  | WinB :: t   => 2 + pointsB t
  | Draw :: t   => 1 + pointsB t
  | WinA :: t   => pointsB t
  end.

(** The table system: its input is the list of statuses alone. *)
Definition table (gs : list Game) : nat * nat :=
  (pointsA (map result gs), pointsB (map result gs)).

(** The table reads statuses only: identical results — identical
    table, whatever the games' interiors were. *)
Theorem table_reads_status_only : forall gs1 gs2,
  map result gs1 = map result gs2 -> table gs1 = table gs2.
Proof. intros gs1 gs2 H. unfold table. rewrite H. reflexivity. Qed.

(** Interiors are invisible to the record-system. *)
Theorem interiors_invisible : exists gs1 gs2,
  map interior gs1 <> map interior gs2 /\ table gs1 = table gs2.
Proof.
  exists [mkGame 0 WinA], [mkGame 1 WinA]. split.
  - intros H. injection H. intros H01. lia.
  - reflexivity.
Qed.

Lemma map_len : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof. intros A B f l. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.

Lemma points_sum : forall rs, pointsA rs + pointsB rs = 2 * length rs.
Proof. induction rs as [| r t IH]; [reflexivity | destruct r; simpl; lia]. Qed.

(** The table is a lawful system of its own: every game distributes
    exactly two points — the total is conserved. *)
Theorem points_conserved : forall gs,
  fst (table gs) + snd (table gs) = 2 * length gs.
Proof.
  intros gs. unfold table. simpl. rewrite points_sum. rewrite map_len. reflexivity.
Qed.

(* ================================================================ *)
(** ** 5. Capstone: the canon of interaction in one statement        *)
(* ================================================================ *)

Theorem interaction_canon :
  (links_across whole /\ ~ sum_decomposable whole) /\
  (~ prod_sep parity) /\
  (exists k1 k2 : nat, k1 <> k2 /\ board_operator k1 = board_operator k2) /\
  (forall gs1 gs2, map result gs1 = map result gs2 -> table gs1 = table gs2).
Proof.
  split; [exact interaction_births_system |
  split; [exact parity_not_separable |
  split; [exists 0, 1; split; [lia | reflexivity] |
  exact table_reads_status_only]]].
Qed.
