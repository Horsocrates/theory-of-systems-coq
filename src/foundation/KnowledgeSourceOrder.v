(** * KnowledgeSourceOrder.v — Теория Знания: the SOURCE-GROUNDING ORDER of знание-о (the content)
      — знание-О (KThat) is a LOSSY DISTILLATE, sourced from знание-ПРИСУТСТВИЯ (KPresence) AND
      знание-КАК (KHow); the direct meeting is NECESSARY, and the proposition is thinner than the
      lived encounter.

    The branch already has these tags (KnowledgeInformation.v: KnowType = KPresence | KThat |
    KHow, §5) and their access modes (KnowledgeInsight.v: presence = the Meeting, not a channel;
    знание-о via the channels усмотрение/дискурсия; знание-как via прохождение).  KnowledgeInformation
    even states the seed in prose: "KPresence is the base both rest on".  This file makes the AUTHOR'S
    THESIS a theorem: знание-о depends IN ITS SOURCE on присутствие + как — every знание-о is already
    a distillate of the direct encounter.

    The thesis, decomposed into three machine-checked claims (over the existing ladder):
      (1) SOURCE ORDER — both POSITIONS of присутствие are first-hand ROOTS: KPresence (присутствие-
          извне, observing) and KHow (присутствие-изнутри = знание-как); KThat (знание-о) is the SINK,
          grounded in both — neither position grounds the other.
      (2) NECESSITY OF THE MEETING — no encounter (no presented data) => no знание-о; equivalently,
          any знание-о implies a meeting happened.  («необходима прямая встреча».)
      (3) LOSSY DISTILLATE — знание-о (read_content) is drawn from the encounter (subset) and is
          generically STRICTLY thinner than it: the proposition loses the rest of the lived encounter.
          («любое знание-о уже дистиллят этого опыта».)

    The model (reusing KnowledgeInformation): the ENCOUNTER / presence = the presented data `data`
    (the manifested distinctions, met directly — «суть познания»); the HOW = the depth-bounded
    reading/resolving process (applied know-how); знание-О = `read_content w data`, the distillate the
    how draws from the presence.  ACCESS to знание-о is via channels (усмотрение/дискурсия), but its
    SOURCE is the meeting — access != source.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) a SOURCE order on знание-о's sources: both positions of присутствие are first-hand roots —
          KPresence (извне) and KHow (изнутри = знание-как), coordinate; KThat is the SINK, distilled
          from both;
      (2) the distillation is NECESSARY-CONDITIONED on the meeting (no encounter => no знание-о);
      (3) and LOSSY (the proposition is thinner than the lived encounter).
    Roles (L4): grounds (the source order); read_content/inform = the distillation map (presence-data
      + how-process -> that-content); Meeting/fulfills (presence = the direct meeting, not a channel);
      the channels усмотрение/дискурсия = ACCESS to знание-о (downstream of the source).
    Elements (L1+P4): the encounter-data (manifested Distinctions = «суть познания»); the witness
      (depth = know-how capacity); the distillate (read_content); the three KnowType.
    P4 diagnostic (could it be otherwise?):
      знание-о cannot SOURCE ITSELF — its content is forced to come from the presented data via the
      reading-process; with no data the distillate is forced empty (no знание-о without a meeting).
      The proposition is forced ⊆ the encounter and generically ⊊ (it loses the rest), so знание-о is
      NECESSARILY a distillate, not the experience itself.  KPresence, by contrast, is the direct
      meeting (root, sourced from nothing).  The order is forced, not chosen.
    Honesty wall:
      a structural / type-theoretic encoding of the grounding thesis on the EXISTING ladder
      (KnowledgeInformation / KnowledgeInsight).  "Суть познания met directly" = the presented data of
      the encounter; "distillate" = the depth-resolved subset; "how" = the resolving process (reading
      at depth = applied know-how).  It does NOT model the phenomenology of acquaintance; it proves the
      DEPENDENCY (source ⊆, necessity, loss) and the ACCESS != SOURCE distinction.  Builds on the
      branch; 0 axioms.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.
From ToS Require Import foundation.KnowledgeInformation.  (* KnowType, Distinction, Data, Witness, read_content, read_subset_data, deeper_reads_more *)
From ToS Require Import foundation.KnowledgeInsight.       (* Mode, Meeting, is_channel, fulfills *)

(* ===================================================================== *)
(*  PART I — the SOURCE-GROUNDING ORDER: присутствие/как -> знание-о         *)
(* ===================================================================== *)

(** A type is GROUNDED IN another if it draws its source from it.  присутствие is the observer's
    POSITION relative to the observed (inside/outside): KPresence = присутствие-Outside (observing),
    KHow = присутствие-Inside (= знание-как, passing through).  BOTH positions are first-hand ROOTS,
    and знание-о (KThat) is the SINK grounded in both.  Neither position grounds the other — they are
    coordinate (corrects the earlier «присутствие grounds знание-как»). *)
Definition grounds (src tgt : KnowType) : Prop :=
  match src, tgt with
  | KPresence, KThat => True   (* присутствие-извне (наблюдение)  grounds знание-о *)
  | KHow,      KThat => True   (* присутствие-изнутри (знание-как) grounds знание-о *)
  | _, _ => False
  end.

(** ★★ THE AUTHOR'S THESIS, type level: знание-о (KThat) is grounded in BOTH positions of присутствие
    — outside (KPresence) and inside (KHow = знание-как). *)
Lemma that_grounded_in_both : grounds KPresence KThat /\ grounds KHow KThat.
Proof. split; exact I. Qed.

(** ★ присутствие-извне (KPresence) is a ROOT: nothing grounds it — it is direct contact. *)
Lemma presence_is_root : forall t, ~ grounds t KPresence.
Proof. intro t. destruct t; simpl; intro H; exact H. Qed.

(** ★ Знание-о is the SINK: it grounds nothing further — it is the terminal distillate. *)
Lemma that_is_sink : forall t, ~ grounds KThat t.
Proof. intro t. destruct t; simpl; intro H; exact H. Qed.

(** ★ The order is irreflexive (acyclic at depth 1): no type grounds itself. *)
Lemma grounds_irrefl : forall t, ~ grounds t t.
Proof. intro t. destruct t; simpl; intro H; exact H. Qed.

(** ★ The two positions of присутствие are COORDINATE: neither grounds the other (KPresence is
    присутствие-извне, KHow = присутствие-изнутри = знание-как), and знание-как is itself a ROOT —
    both rest directly on contact; знание-о (the sink) is grounded in both.  (Corrects the earlier
    «присутствие grounds знание-как».) *)
Lemma positions_coordinate :
  ~ grounds KPresence KHow /\ ~ grounds KHow KPresence /\ (forall t, ~ grounds t KHow).
Proof.
  split; [ simpl; intro H; exact H
         | split; [ simpl; intro H; exact H
                  | intro t; destruct t; simpl; intro H; exact H ] ].
Qed.

(* ===================================================================== *)
(*  PART II — the grounding REALIZED in the ladder: знание-о = the distillate *)
(* ===================================================================== *)

(** ★★ KThat is DRAWN FROM PRESENCE: the distillate (read_content) is a subset of the presented
    encounter-data.  Realizes grounds KPresence KThat. *)
Lemma that_drawn_from_presence : forall w data, incl (read_content w data) data.
Proof. intros w data d Hd. exact (read_subset_data w data d Hd). Qed.

(** ★ KThat is DRAWN VIA THE HOW: the distillation is the depth-bounded reading-process; more
    know-how (greater depth) distills more.  Realizes grounds KHow KThat. *)
Lemma that_via_how : forall w1 w2 data, w_depth w1 <= w_depth w2 ->
  incl (read_content w1 data) (read_content w2 data).
Proof. intros w1 w2 data Hle. apply deeper_reads_more. exact Hle. Qed.

(** ★ No meeting (no presented data) => no знание-о: the distillate of nothing is nothing. *)
Lemma no_meeting_no_that : forall w, read_content w [] = [].
Proof. intro w. reflexivity. Qed.

(** ★★ THE MEETING IS NECESSARY: any знание-о implies an encounter happened — you cannot distill a
    proposition from no meeting.  («необходима прямая встреча с сутью познания».) *)
Lemma that_needs_meeting : forall w data, read_content w data <> [] -> data <> [].
Proof. intros w data H Hd. apply H. rewrite Hd. reflexivity. Qed.

(** ★★ ЗНАНИЕ-О IS A LOSSY DISTILLATE: the proposition is generically STRICTLY thinner than the lived
    encounter — a witness of depth 0 meets a depth-1 distinction yet distills nothing from it.
    («любое знание-о уже дистиллят этого опыта».) *)
Lemma that_is_distillate :
  exists (data : Data) (w : Witness), length (read_content w data) < length data.
Proof.
  exists [ mkDist 0 1 0 ], (mkWit 0 0).
  unfold read_content. simpl. lia.
Qed.

(* ===================================================================== *)
(*  PART III — ACCESS != SOURCE: знание-о is reached by channels, sourced in the meeting *)
(* ===================================================================== *)

(** ★ ПРИСУТСТВИЕ is the direct MEETING, not a channel (the прямая встреча). *)
Lemma presence_is_direct_meeting : fulfills KPresence Meeting /\ is_channel Meeting = false.
Proof. split; [ exact I | reflexivity ]. Qed.

(** ★ ЗНАНИЕ-О is ACCESSED through a channel (усмотрение) — yet (Part II) its SOURCE is the meeting.
    Access is via channels; the source is the encounter.  Access != source. *)
Lemma that_accessed_by_channel : fulfills KThat Usmotrenie /\ is_channel Usmotrenie = true.
Proof. split; [ exact I | reflexivity ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ ЗНАНИЕ-О IS A DISTILLATE OF THE DIRECT ENCOUNTER, sourced from присутствие + как:
      (source order)   KThat is grounded in BOTH KPresence and KHow;
      (root / sink)    nothing grounds присутствие (the direct meeting); KThat grounds nothing (sink);
      (drawn from)     the distillate is a subset of the presented encounter-data;
      (necessity)      no meeting => no знание-о (the direct встреча is necessary);
      (lossy)          and it is generically STRICTLY thinner than the encounter — a distillate;
      (access!=source) присутствие is the direct meeting, not a channel.
    Any знание-о is already a distillate of the lived presence — machine-checked, 0 axioms. *)
Theorem knowledge_that_is_distilled :
  (grounds KPresence KThat /\ grounds KHow KThat)
  /\ (forall t, ~ grounds t KPresence)
  /\ (forall t, ~ grounds KThat t)
  /\ (forall w data, incl (read_content w data) data)
  /\ (forall w data, read_content w data <> [] -> data <> [])
  /\ (exists data w, length (read_content w data) < length data)
  /\ (fulfills KPresence Meeting /\ is_channel Meeting = false).
Proof.
  split; [ exact that_grounded_in_both | ].
  split; [ exact presence_is_root | ].
  split; [ exact that_is_sink | ].
  split; [ exact that_drawn_from_presence | ].
  split; [ exact that_needs_meeting | ].
  split; [ exact that_is_distillate | exact presence_is_direct_meeting ].
Qed.

Print Assumptions knowledge_that_is_distilled.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  13 Qed, 0 Admitted, 0 axioms.                                            *)
(*  The author's thesis as a theorem: знание-О (KThat) is a LOSSY DISTILLATE,  *)
(*  sourced from знание-ПРИСУТСТВИЯ (KPresence) AND знание-КАК (KHow).  PART I  *)
(*  the SOURCE order `grounds`: that_grounded_in_both (KThat grounded in both); *)
(*  presence_is_root (the direct meeting, sourced from nothing); that_is_sink   *)
(*  (the terminal distillate); grounds_irrefl; positions_coordinate.  PART II  *)
(*  realized in the ladder: that_drawn_from_presence (distillate ⊆ encounter),  *)
(*  that_via_how (more know-how distills more), no_meeting_no_that +            *)
(*  that_needs_meeting (the direct встреча is NECESSARY), that_is_distillate    *)
(*  (generically STRICTLY thinner — a distillate).  PART III access != source:  *)
(*  presence_is_direct_meeting (the meeting, not a channel) vs                   *)
(*  that_accessed_by_channel (знание-о reached by усмотрение, sourced in the     *)
(*  meeting).  Capstone knowledge_that_is_distilled.  Builds on                 *)
(*  KnowledgeInformation + KnowledgeInsight.  HONEST: structural encoding of    *)
(*  the grounding thesis (source ⊆, necessity, loss; access != source), not the *)
(*  phenomenology of acquaintance.                                            *)
(* ========================================================================= *)
