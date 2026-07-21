(** * KnowledgeTruthLadder.v — Ladder of Representation and the Two Paths of Untruth as ToS System

    Formalizes the adjudicated deepening of Epistemology Ch. 1 (working journal
    PI-1..PI-9, 2026-07-21): the two axes of representation (link kind x
    correspondence), knowledge titles as success terms (wrong "knowledge" is an
    illusion of knowledge, not knowledge), Gettier and Meno in ladder terms,
    the two faces of truth about the potential layer, and the two paths that
    create one untruth (distortion with prior knowledge vs substitution
    without it) together with their distinct maintenance efforts.

    Elements: representations (mental constructions) of a witness: opinion /
              know-that / understanding; claims about the potential layer;
              untruth constructions; moments of time; encounters (meetings)
              of a witness with the field of what is.
    Roles:    correctness (pravota) = correspondence status of a
              representation (binary, Law of Non-Contradiction); knowledge
              titles = success roles, earned only with correspondence;
              tuning of an act = what occupies the center of attention
              (binary, Law of Excluded Middle); paths of untruth = roles of
              the creating act (distort / substitute).
    Rules:    a knowledge link without correspondence is an illusion of
              knowledge; knowledge = correctness + one's own path (Meno 98a);
              correctness without a chain is not knowledge (Gettier);
              structure truth opens to reasoning, filling truth requires a
              meeting — without it only projection; distortion requires prior
              knowledge of truth, substitution does not (hence its mass
              availability); distortion falls at the first uncovered foreign
              encounter, substitution at the first own one; truth stands free.
    Status:   all proved; self-contained (no ToS imports).
    STATUS: 29 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. Two axes of representation                                *)
(* ================================================================ *)

(** Link axis: what the witness can show for the content held. *)
Inductive LinkKind : Type :=
  | LNone       (** opinion: no chain, held by belief "it is so" *)
  | LInfo       (** know-that: chain to information about the phenomenon *)
  | LStructure. (** understanding: chain to the structure (logic) itself *)

(** Status axis: correctness = correspondence of the representation.
    The witness never manipulates the field of what is — he overlays his
    own and receives a representation; that representation either
    corresponds or does not. *)
Record Representation : Type := mkRep {
  r_link    : LinkKind;
  r_matches : bool
}.

(** Law of Non-Contradiction anchors the status axis. *)
Lemma matches_binary : forall r : Representation,
  r_matches r = true \/ r_matches r = false.
Proof. intros r. destruct (r_matches r); auto. Qed.

(* ---------------- titles as success terms ---------------- *)

Inductive Title : Type := TOpinion | TKnowThat | TUnderstanding.

(** A title is EARNED: opinion is the honest name for "held without a
    chain" (any status); the knowledge titles require their link AND
    correspondence. *)
Definition earns (r : Representation) (t : Title) : bool :=
  match t, r_link r, r_matches r with
  | TOpinion,       LNone,      _    => true
  | TKnowThat,      LInfo,      true => true
  | TUnderstanding, LStructure, true => true
  | _, _, _ => false
  end.

(** Wrong "knowledge" is the illusion of knowledge, not knowledge. *)
Definition illusion_of_knowledge (r : Representation) : bool :=
  match r_link r, r_matches r with
  | LInfo,      false => true
  | LStructure, false => true
  | _, _ => false
  end.

(** Know-that never is wrong: if the title is earned, it corresponds. *)
Theorem know_that_never_wrong : forall r,
  earns r TKnowThat = true -> r_matches r = true.
Proof.
  intros [l m] H. destruct l, m; simpl in *; try discriminate; reflexivity.
Qed.

Theorem understanding_never_wrong : forall r,
  earns r TUnderstanding = true -> r_matches r = true.
Proof.
  intros [l m] H. destruct l, m; simpl in *; try discriminate; reflexivity.
Qed.

(** Only opinion lives on both sides of the status axis. *)
Theorem opinion_right_exists :
  exists r, earns r TOpinion = true /\ r_matches r = true.
Proof. exists (mkRep LNone true). split; reflexivity. Qed.

Theorem opinion_wrong_exists :
  exists r, earns r TOpinion = true /\ r_matches r = false.
Proof. exists (mkRep LNone false). split; reflexivity. Qed.

(** A knowledge link without correspondence earns no knowledge title:
    it is exactly the illusion of knowledge. *)
Theorem wrong_link_is_illusion : forall r,
  (r_link r = LInfo \/ r_link r = LStructure) ->
  r_matches r = false ->
  illusion_of_knowledge r = true /\
  earns r TKnowThat = false /\ earns r TUnderstanding = false.
Proof.
  intros [l m] H Hm. simpl in *. subst m.
  destruct H as [H|H]; subst l; repeat split; reflexivity.
Qed.

(* ---------------- Meno and Gettier ---------------- *)

(** Knowledge = correctness + one's own path (the Meno binding, 98a:
    right opinion becomes knowledge when tied by reasoning of the cause). *)
Definition is_knowledge (r : Representation) : bool :=
  match r_link r with
  | LNone => false
  | _     => r_matches r
  end.

(** Gettier dissolved: correctness without a chain (orthe doxa) is not
    knowledge. *)
Theorem gettier_dissolved : forall r,
  r_link r = LNone -> r_matches r = true -> is_knowledge r = false.
Proof. intros r H _. unfold is_knowledge. rewrite H. reflexivity. Qed.

Theorem meno_binding : forall r,
  is_knowledge r = true -> r_link r <> LNone /\ r_matches r = true.
Proof.
  intros [l m] H. destruct l; simpl in H.
  - discriminate.
  - split; [simpl; discriminate | simpl; exact H].
  - split; [simpl; discriminate | simpl; exact H].
Qed.

(** True knowledge is understanding: the deepest link, corresponding. *)
Definition link_depth (l : LinkKind) : nat :=
  match l with LNone => 0 | LInfo => 1 | LStructure => 2 end.

Theorem understanding_deepest : forall l,
  link_depth l <= link_depth LStructure.
Proof. intros [ | | ]; simpl; lia. Qed.

Theorem true_knowledge_is_understanding : forall r,
  earns r TUnderstanding = true ->
  is_knowledge r = true /\ link_depth (r_link r) = 2.
Proof.
  intros [l m] H. destruct l, m; simpl in *; try discriminate.
  split; reflexivity.
Qed.

(* ================================================================ *)
(** ** 2. Tuning of the act: binary by Excluded Middle              *)
(* ================================================================ *)

(** Every act HAS a tuning: the center of attention is always occupied.
    The lie's tuning exists too — its goal is personal interest, not
    truth. Law of Excluded Middle: no third tuning. *)
Inductive Tuning : Type := TuTruth | TuOther.

Theorem tuning_no_third : forall t : Tuning, t = TuTruth \/ t = TuOther.
Proof. intros [ | ]; auto. Qed.

Theorem tuning_decidable : forall t : Tuning, t <> TuTruth -> t = TuOther.
Proof.
  intros t H. destruct t; [exfalso; apply H; reflexivity | reflexivity].
Qed.

(* ================================================================ *)
(** ** 3. Truth about the potential: two faces                      *)
(* ================================================================ *)

Inductive Face : Type := FStructure | FFilling.

(** A claim about the potential layer: its face, and whether a meeting
    of the witness with what is has taken place. *)
Record Claim : Type := mkClaim { c_face : Face; c_met : bool }.

(** Structure presents itself: the reasoning path is always open.
    Filling opens only through a meeting. *)
Definition truth_open (c : Claim) : bool :=
  match c_face c with
  | FStructure => true
  | FFilling   => c_met c
  end.

Theorem structure_always_open : forall b,
  truth_open (mkClaim FStructure b) = true.
Proof. intros b. reflexivity. Qed.

(** Without a meeting, work on filling is projection: modeling the
    unknown from the limited known. *)
Definition is_projection (c : Claim) : bool := negb (truth_open c).

Theorem no_meeting_only_projection : forall c,
  c_face c = FFilling -> c_met c = false -> is_projection c = true.
Proof. intros [f m] Hf Hm. simpl in *. subst. reflexivity. Qed.

Theorem meeting_ends_projection : forall c,
  c_met c = true -> is_projection c = false.
Proof. intros [f m] H. simpl in H. subst. destruct f; reflexivity. Qed.

(** Consistency admits, correspondence decides: inside a true system one
    can build constructions that obey the rules yet fail the real. *)
Record Construction : Type := mkCon {
  obeys_rules : bool;
  corresponds : bool
}.

Theorem consistency_not_truth :
  exists c, obeys_rules c = true /\ corresponds c = false.
Proof. exists (mkCon true false). split; reflexivity. Qed.

(** Work inside a true system gives the possibility of a true result,
    not a guarantee. *)
Theorem possibility_not_guarantee :
  (exists c, obeys_rules c = true /\ corresponds c = true) /\
  (exists c, obeys_rules c = true /\ corresponds c = false).
Proof.
  split; [exists (mkCon true true) | exists (mkCon true false)];
    split; reflexivity.
Qed.

(* ================================================================ *)
(** ** 4. Two paths of one untruth                                  *)
(* ================================================================ *)

(** The witness: does he know how it is; does he intend to find out. *)
Record Witness : Type := mkWit {
  knows_truth     : bool;
  intends_to_know : bool
}.

Inductive UntruthPath : Type :=
  | PDistort     (** path a: learn how it is, then replace — stitchable
                     with parts of truth, hence firmer, but requires the
                     path of learning first *)
  | PSubstitute. (** path b: create a projection of one's own knowledge —
                     requires no truth, only one's own projection *)

(** Availability: distortion is open only to one who knows the truth;
    substitution is open to anyone. *)
Definition available (w : Witness) (p : UntruthPath) : bool :=
  match p with
  | PDistort    => knows_truth w
  | PSubstitute => true
  end.

Theorem substitution_always_available : forall w,
  available w PSubstitute = true.
Proof. intros w. reflexivity. Qed.

Theorem distortion_needs_knowledge : forall w,
  available w PDistort = true -> knows_truth w = true.
Proof. intros w H. exact H. Qed.

(** Why substitution is the mass case: the ignorant witness has one path
    only — he does not know, he substitutes. *)
Theorem ignorant_only_substitutes : forall w p,
  knows_truth w = false -> available w p = true -> p = PSubstitute.
Proof.
  intros w p Hk H. destruct p; [simpl in H; congruence | reflexivity].
Qed.

(** Creation cost: distortion = the path of learning first, then the
    act; substitution = the act alone. *)
Definition creation_steps (p : UntruthPath) (learn_path : nat) : nat :=
  match p with
  | PDistort    => S learn_path
  | PSubstitute => 1
  end.

Theorem substitution_no_dearer : forall n,
  creation_steps PSubstitute n <= creation_steps PDistort n.
Proof. intros n. simpl. lia. Qed.

(** One meaning: either path yields the same result — an untruth
    construction laid over truth (distortion, substitution, illusion,
    projection are one in essence, two in process). *)
Inductive Result : Type := ROverlay.

Definition result_of (p : UntruthPath) : Result := ROverlay.

Theorem one_meaning : forall p q : UntruthPath, result_of p = result_of q.
Proof. intros p q. reflexivity. Qed.

(* ================================================================ *)
(** ** 5. Maintenance effort: two kinds, two falls                  *)
(* ================================================================ *)

(** Distortion holds a DOUBLE record (what is / what is declared) and
    must quench every foreign encounter with the field: it stands
    through moment t iff every moment up to t is covered by a patch. *)
Definition distortion_stands (covered : nat -> bool) (t : nat) : bool :=
  forallb covered (seq 0 (S t)).

(** Substitution holds ONE record (the projection standing in the place
    of "how it is") and lives by turning away: it stands through moment
    t iff no own meeting has happened up to t. *)
Definition substitution_stands (met : nat -> bool) (t : nat) : bool :=
  forallb (fun i => negb (met i)) (seq 0 (S t)).

Theorem distortion_needs_every_moment : forall covered t,
  distortion_stands covered t = true ->
  forall k, k <= t -> covered k = true.
Proof.
  intros covered t H k Hk.
  unfold distortion_stands in H. rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Theorem distortion_falls_at_first_gap : forall covered t k,
  k <= t -> covered k = false -> distortion_stands covered t = false.
Proof.
  intros covered t k Hk Hc.
  destruct (distortion_stands covered t) eqn:E; [ | reflexivity].
  exfalso.
  assert (Hc' : covered k = true)
    by (apply distortion_needs_every_moment with (t := t); assumption).
  congruence.
Qed.

Theorem substitution_falls_at_own_meeting : forall met t k,
  k <= t -> met k = true -> substitution_stands met t = false.
Proof.
  intros met t k Hk Hm.
  destruct (substitution_stands met t) eqn:E; [ | reflexivity].
  exfalso. unfold substitution_stands in E. rewrite forallb_forall in E.
  assert (Hin : In k (seq 0 (S t))) by (apply in_seq; lia).
  specialize (E k Hin). rewrite Hm in E. simpl in E. discriminate.
Qed.

(** While the question stays unasked, substitution stands —
    indefinitely long: the meeting can be postponed. *)
Theorem substitution_stands_unasked : forall met,
  (forall i, met i = false) ->
  forall t, substitution_stands met t = true.
Proof.
  intros met H t. unfold substitution_stands. rewrite forallb_forall.
  intros i _. rewrite H. reflexivity.
Qed.

(** The burden of distortion grows with every moment. *)
Lemma seq_len : forall len start, length (seq start len) = len.
Proof.
  induction len; intros start; simpl; [reflexivity | rewrite IHlen; reflexivity].
Qed.

Theorem distortion_burden_grows : forall t,
  length (seq 0 (S t)) < length (seq 0 (S (S t))).
Proof. intros t. do 2 rewrite seq_len. lia. Qed.

(** Truth needs none of this: correspondence is held by what is itself.
    Truth stands by itself; illusion is held by effort. *)
Definition truth_stands (t : nat) : bool := true.

Theorem truth_stands_free : forall t, truth_stands t = true.
Proof. intros t. reflexivity. Qed.
