(** * KnowledgeInformation.v — F-39 base: the ladder данные -> информация -> знание, and the
      witness watershed where INFORMATION enters

    A formal base for the "Теория Знания" branch (derivation "Знание", §2 the ladder, §3 the E/R/R
    system, §4 the field, §5 знание-о and its first-hand positions).  It pins the rung that connects knowledge to
    INFORMATION: information = data become meaning FOR A WITNESS, and one resolved binary
    distinction = 1 bit.  It unifies the two existing F-39 files:
      - KnowledgeProcess.v  (qualitative anti-omniscience: the witnessed record),
      - KnowledgeGap.v      (quantitative race / phase transition: the зазор §8),
    by reading their field/known as |presented distinctions| / |resolved distinctions|.

    THE LADDER (§2):
      Data         = the distinctions PRESENTED by the knowable — objective, manifested BY a
                     SOURCE (the knowable itself), before any particular witness.
      read_content = the witness reads them up to its depth threshold (R3 width/depth limit).
      Information  = read content TAGGED with its WITNESS (the knower).  THE WATERSHED: data are
                     SOURCE-borne but witness-neutral ("предъявлены всем и никому"); information
                     ADDS the witness-bearer — it is always someone's.
      Knowledge    = retained information = a record.
    The rungs do not permute and cannot be skipped (horizontal Law of Order): no information
    without presented data; no record without information (R2).

    THE TWO BEARERS (corrected 2026-06-12 after author's note): data are NOT bearerless.  Their
    bearer is the SOURCE — the knowable that manifests them (data = the manifestation of the
    knowable FOR the knower's consciousness, the medium through which the knowable is known).
    What data lack is a WITNESS-bearer (the derivation's precise phrase: "нет носителя-СВИДЕТЕЛЯ",
    not "нет носителя").  So the watershed is TWO bearers on two ontological levels —
    SOURCE-borne data (objective, witness-neutral) vs WITNESS-borne information (someone's) — and
    information is DOUBLY borne: by the witness who reads AND the source it inherits from the data.

    THE INFORMATION CONNECTION:
      info_bits i = the number of distinctions resolved = the information content (in bits, one
      binary distinction = 1 bit; cf. DyadicBits.v).  info_bits <= |data| always (you resolve no
      more than was presented); the UNRESOLVED distinctions are the зазор, and the
      data-vs-resolution race is exactly KnowledgeGap's phase transition over distinctions.

    ============================== E/R/R разбор ==============================
    Elements: Distinction (a difference, with a depth/tier AND a source — the knowable that
              manifests it); Data (presented differences, source-borne, objective); Witness (a
              depth threshold); read_content (what is read at depth); Info (read content + the
              witness-bearer); Knowledge (a retained record).
    Roles:    Data = manifestation of the source (the knowable presents them, to all and none).
              Reading = depth/width-limited intake (R3).  Information = data-become-meaning,
              ADDING a witness-bearer (the watershed).  Knowledge = the retained record.  ЗДО =
              gatekeeper of every rung.
    Rules:    the ladder is ORDERED (data -> information -> record, no skipping = horizontal Law
              of Order); info_content ⊆ data (cannot read the un-presented); reading ≤ depth
              threshold; R5 retention.
    P4 diagnostic — THE WATERSHED (where information enters): data have a SOURCE-bearer (the
              knowable that manifests them) but no WITNESS-bearer; information adds the
              witness-bearer.  TWO bearers, two ontological levels — NOT borne vs unborne.
              Machine form: the same source-data yield the same CONTENT but DIFFERENT information
              (different witness) — same_data_different_information; and the information is doubly
              borne (witness + inherited source) — manifestation_chain.  "Information =
              distinctions resolved FOR a witness"; one binary distinction = 1 bit (L2/L3
              side_binarity; DyadicBits).  info_bits = count of resolved distinctions ≤ field;
              unresolved = the зазор -> KnowledgeGap's race over distinctions.
    знание-о and its sources (§5): знание-о (KThat) is the CONTENT.  присутствие is the observer's
              POSITION relative to the observed: KPresence = извне (observing), KHow = изнутри
              (= знание-как) — both deliver знание-о (not «three kinds»).  Completability by source:
              KThat (bounded fact) completes; KHow (inside an unbounded process) diverges; KPresence
              (a single observation) completes.

    Honest scope: the ladder is a clean type-theoretic encoding of §2–§5 + the watershed; the
    theorems are elementary (filter/list facts + the KnowledgeGap bridges).  The value is a
    coherent FORMAL BASE for the Теория Знания branch that unifies KnowledgeProcess + KnowledgeGap,
    makes the data->information->knowledge ladder and its source/witness watershed precise,
    connects to information (bit = a resolved distinction), and leaves hooks for the
    «Взаимодействие» / «Глубина» branches.

    STATUS: 19 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.
From ToS Require Import foundation.KnowledgeGap.   (* the data-vs-resolution race / phase transition *)

(* ===================================================================== *)
(*  THE LADDER, AS TYPES                                                   *)
(* ===================================================================== *)

(** A distinction = a difference, living on some tier (depth, §4) and MANIFESTED BY a source
    (d_source = the knowable that presents it).  A datum is never bearerless: it is borne by its
    source. *)
Record Distinction := mkDist { d_id : nat ; d_depth : nat ; d_source : nat }.

(** DATA: the distinctions PRESENTED by the knowable — objective, SOURCE-borne, witness-neutral. *)
Definition Data := list Distinction.

(** A WITNESS: carries a depth threshold (how deep it can read, §4). *)
Record Witness := mkWit { w_id : nat ; w_depth : nat }.

(** A distinction is readable by a witness iff it lies within the witness's depth. *)
Definition readable (w : Witness) (d : Distinction) : bool := Nat.leb (d_depth d) (w_depth w).

(** READING at depth: keep only the presented distinctions within the threshold (R3). *)
Definition read_content (w : Witness) (data : Data) : list Distinction := filter (readable w) data.

(** INFORMATION: read content TAGGED with its WITNESS-bearer.  The watershed — Info adds a
    Witness on top of the source-borne data. *)
Record Info := mkInfo { i_witness : Witness ; i_content : list Distinction }.
Definition inform (w : Witness) (data : Data) : Info := mkInfo w (read_content w data).

(** KNOWLEDGE: retained information — a record. *)
Definition Knowledge := list Info.

(** INFORMATION CONTENT in bits = the number of distinctions resolved (one binary distinction
    = 1 bit; cf. DyadicBits.v). *)
Definition info_bits (i : Info) : nat := length (i_content i).

(** d is manifested by the knowable k (k is the source that presents d). *)
Definition manifested_by (d : Distinction) (k : nat) : Prop := d_source d = k.

(* ===================================================================== *)
(*  PART I — reading is grounded and bounded (R2 + R3)                     *)
(* ===================================================================== *)

Lemma filter_le : forall (f : Distinction -> bool) (l : list Distinction),
  length (filter f l) <= length l.
Proof. intros f l. induction l as [|x l IH]; simpl; [ lia | destruct (f x); simpl; lia ]. Qed.

(** info needs data (R2): a read distinction was presented — cannot read the un-presented. *)
Lemma read_subset_data : forall w data d, In d (read_content w data) -> In d data.
Proof.
  intros w data d H. unfold read_content in H. apply filter_In in H.
  destruct H as [Hin _]. exact Hin.
Qed.

(** reading is depth-bounded (R3): nothing is read beyond the witness's threshold. *)
Lemma read_within_depth : forall w data d, In d (read_content w data) -> d_depth d <= w_depth w.
Proof.
  intros w data d H. unfold read_content in H. apply filter_In in H.
  destruct H as [_ Hb]. unfold readable in Hb. apply Nat.leb_le in Hb. exact Hb.
Qed.

(** a deeper witness reads at least as much — the depth ladder (§4). *)
Lemma deeper_reads_more : forall w1 w2 data, w_depth w1 <= w_depth w2 ->
  incl (read_content w1 data) (read_content w2 data).
Proof.
  intros w1 w2 data Hle. unfold incl. intros d Hd.
  unfold read_content in *. apply filter_In in Hd. destruct Hd as [Hin Hb].
  apply filter_In. split.
  - exact Hin.
  - unfold readable in *. apply Nat.leb_le. apply Nat.leb_le in Hb. lia.
Qed.

(* ===================================================================== *)
(*  PART II — the watershed: TWO bearers (source for data, witness for info) *)
(* ===================================================================== *)

(** ★ Data ARE borne — by their SOURCE (the knowable that manifests them).  Not bearerless;
    what they lack is a WITNESS-bearer.  (Corrects the earlier "data have no bearer".) *)
Lemma datum_borne_by_source : forall d, manifested_by d (d_source d).
Proof. intro d. reflexivity. Qed.

(** reading depends only on the witness's DEPTH (witnesses of equal depth read the same). *)
Lemma filter_depth_ext : forall (data : Data) (w1 w2 : Witness),
  w_depth w1 = w_depth w2 -> filter (readable w1) data = filter (readable w2) data.
Proof.
  induction data as [|d ds IH]; intros w1 w2 Hdep.
  - reflexivity.
  - simpl. destruct (readable w1 d) eqn:E1; destruct (readable w2 d) eqn:E2.
    + f_equal. apply IH. exact Hdep.
    + exfalso. unfold readable in E1, E2. rewrite Hdep in E1. rewrite E1 in E2. discriminate.
    + exfalso. unfold readable in E1, E2. rewrite Hdep in E1. rewrite E1 in E2. discriminate.
    + apply IH. exact Hdep.
Qed.

Lemma read_content_depth_only : forall data w1 w2,
  w_depth w1 = w_depth w2 -> read_content w1 data = read_content w2 data.
Proof. intros data w1 w2 Hdep. unfold read_content. apply filter_depth_ext. exact Hdep. Qed.

(** Information carries its WITNESS-bearer intrinsically. *)
Lemma information_has_bearer : forall w data, i_witness (inform w data) = w.
Proof. reflexivity. Qed.

(** ★ THE WATERSHED: the same SOURCE-data, even with the SAME read content, yield DIFFERENT
    information when the witness differs.  The source side is invariant (data are objective,
    "presented to all and none"); the WITNESS-bearer is what distinguishes — information is
    always someone's.  This is exactly where information theory enters the ladder. *)
Lemma same_data_different_information :
  forall w1 w2 data, w1 <> w2 -> w_depth w1 = w_depth w2 ->
    read_content w1 data = read_content w2 data   (* same source-content *)
    /\ inform w1 data <> inform w2 data.           (* different information (the witness-bearer) *)
Proof.
  intros w1 w2 data Hne Hdep. split.
  - apply read_content_depth_only. exact Hdep.
  - intro H. apply Hne.
    change w1 with (i_witness (inform w1 data)). rewrite H. reflexivity.
Qed.

(** ★★ THE MANIFESTATION CHAIN (the corrected watershed): познаваемое(k) -> данные -> свидетель(w)
    -> информация.  If a knowable k manifests all the presented data, then the information a
    witness w forms is BORNE BY w (the witness-bearer) yet every distinction in it is SOURCED IN
    k (the source-bearer, inherited from the data).  Information is DOUBLY borne — by the source
    (what manifests) and the witness (who reads); data are the MEDIUM through which the knowable
    k becomes known to the knower w. *)
Theorem manifestation_chain : forall k w data,
  (forall d, In d data -> manifested_by d k) ->
  i_witness (inform w data) = w                                          (* borne by the witness *)
  /\ (forall d, In d (i_content (inform w data)) -> manifested_by d k).  (* sourced in the knowable *)
Proof.
  intros k w data Hsrc. split.
  - reflexivity.
  - intros d Hd. apply Hsrc. exact (read_subset_data w data d Hd).
Qed.

(* ===================================================================== *)
(*  PART III — information measure: bits = resolved distinctions           *)
(* ===================================================================== *)

Lemma info_bits_read : forall w data, info_bits (inform w data) = length (read_content w data).
Proof. reflexivity. Qed.

(** ★ Knowledge resolves no more distinctions than were presented: info_bits ≤ |field|. *)
Lemma info_le_data : forall w data, info_bits (inform w data) <= length data.
Proof. intros w data. rewrite info_bits_read. unfold read_content. apply filter_le. Qed.

(** R2 base / KPresence: no presented data => no co-presence => no information => no knowledge. *)
Lemma no_presence_no_knowledge : forall w,
  read_content w [] = [] /\ info_bits (inform w []) = 0.
Proof. intro w. split; reflexivity. Qed.

(* ===================================================================== *)
(*  PART IV — the bridge to KnowledgeGap: the race over DISTINCTIONS       *)
(* ===================================================================== *)

(** ★ Anti-omniscience in information terms: if presentation outruns resolution (g > r), the
    UNRESOLVED distinctions diverge — the information gap never closes (знание-как, §7). *)
Theorem unresolved_distinctions_diverge :
  forall (present : nat -> Data) (resolve : nat -> list Distinction) (r g : nat),
    (forall n, length (resolve (S n)) <= length (resolve n) + r) ->   (* R3: bounded resolution/step *)
    (forall n, length (present n) + g <= length (present (S n))) ->    (* R4: growing presentation *)
    r < g -> length (resolve 0) <= length (present 0) ->
    forall B, exists n, length (resolve n) + B < length (present n).
Proof.
  intros present resolve r g Hr Hg Hrg H0.
  exact (deficit_diverges (fun n => length (present n)) (fun n => length (resolve n)) r g Hr Hg Hrg H0).
Qed.

(** ★ Knowledge-THAT: a finite fact (bounded presented distinctions) with steady resolution is
    fully resolved — знание-о absolute by its fact (§5).  The race is won. *)
Theorem finite_fact_fully_resolved :
  forall (present : nat -> Data) (resolve : nat -> list Distinction) (cap : nat),
    (forall n, length (present n) <= cap) ->     (* a finite fact: bounded distinctions *)
    (forall n, n <= length (resolve n)) ->        (* steady resolution: >= 1 new per step *)
    exists N, length (present N) <= length (resolve N).
Proof.
  intros present resolve cap Hb Hs.
  exact (knowledge_completes_when_bounded (fun n => length (present n)) (fun n => length (resolve n)) cap Hb Hs).
Qed.

(* ===================================================================== *)
(*  PART V — знание-о (the CONTENT) and its two first-hand POSITIONS        *)
(* ===================================================================== *)

(** Author's correction 2026-06-16: знание-о is NOT one of «three kinds».  знание-о (KThat) is the
    CONTENT — the сводка of all that is knowable about a system (across its E/R/R sides:
    element / role / rule — the OBJECT's structure).  присутствие is the observer's POSITION relative
    to the observed (inside/outside): KPresence = присутствие-извне (observing), KHow = присутствие-
    изнутри (= знание-как, passing through) — the two POSITIONS, BOTH delivering знание-о
    (KnowledgeInsight §8, both_positions_yield_that); передача is the second-hand source (the
    distillate).  These tags name ONE content and the positions of присутствие — NOT three parallel
    kinds. *)
Inductive KnowType := KPresence | KThat | KHow.

(** знание-о (KThat) is the CONTENT; присутствие (KPresence) and знание-как (KHow) are POSITIONS. *)
Definition is_position (t : KnowType) : bool :=
  match t with KPresence => true | KThat => false | KHow => true end.

(** ★ ONE content, two first-hand positions: знание-о (KThat) is the content (not a position);
    присутствие and знание-как are the positions.  (Counters the old «three parallel kinds».) *)
Theorem that_is_content_others_positions :
  is_position KThat = false /\ is_position KPresence = true /\ is_position KHow = true.
Proof. repeat split; reflexivity. Qed.

(** Completability of знание-о by its SOURCE: знание-о of a bounded fact completes; знание-о gathered
    by ongoing прохождение (inside an unbounded process) does not; присутствие (a single meeting) is
    the minimal base. *)
Definition completable (t : KnowType) : Prop :=
  match t with
  | KPresence => True     (* присутствие: a single meeting completes *)
  | KThat     => True     (* знание-о of a bounded fact; realized by finite_fact_fully_resolved *)
  | KHow      => False    (* знание-о via inside-process (знание-как); diverges, unresolved_distinctions_diverge *)
  end.

(** ★★ знание-о completes or diverges BY ITS SOURCE — the two regimes of the distinction-race:
    знание-о of a bounded fact (KThat) completes; знание-о gathered by ongoing прохождение inside an
    unbounded process (the знание-как position, KHow) leaves an ever-growing residue. *)
Theorem types_follow_the_race :
  (* знание-о of a bounded knowable is fully resolved *)
  (forall (present : nat -> Data) (resolve : nat -> list Distinction) (cap : nat),
     (forall n, length (present n) <= cap) -> (forall n, n <= length (resolve n)) ->
     exists N, length (present N) <= length (resolve N))
  /\ (* знание-о via an outrunning inside-process leaves divergent residue *)
  (forall (present : nat -> Data) (resolve : nat -> list Distinction) (r g : nat),
     (forall n, length (resolve (S n)) <= length (resolve n) + r) ->
     (forall n, length (present n) + g <= length (present (S n))) ->
     r < g -> length (resolve 0) <= length (present 0) ->
     forall B, exists n, length (resolve n) + B < length (present n)).
Proof.
  split; [ exact finite_fact_fully_resolved | exact unresolved_distinctions_diverge ].
Qed.

(* ===================================================================== *)
(*  CAPSTONES                                                              *)
(* ===================================================================== *)

(** ★★★ The watershed, bundled: data are borne by their SOURCE (the knowable), information by its
    WITNESS (the knower), and information is DOUBLY borne — witness + the source inherited from
    the data.  Two bearers on two levels; data are the medium source -> knower. *)
Theorem watershed :
  (forall d, manifested_by d (d_source d))                                  (* data: source-borne *)
  /\ (forall w data, i_witness (inform w data) = w)                          (* information: witness-borne *)
  /\ (forall k w data, (forall d, In d data -> manifested_by d k) ->
        forall d, In d (i_content (inform w data)) -> manifested_by d k).    (* doubly borne (source inherited) *)
Proof.
  split; [ exact datum_borne_by_source | split ].
  - exact information_has_bearer.
  - intros k w data Hsrc d Hd. apply Hsrc. exact (read_subset_data w data d Hd).
Qed.

(** ★★★ The data -> information -> knowledge ladder: reading is grounded (subset) and
    depth-bounded (R2+R3); information carries a bearer (the watershed); a record resolves no
    more than was presented; and no presented data means no knowledge (R2 base). *)
Theorem knowledge_ladder :
  (forall w data d, In d (read_content w data) -> In d data /\ d_depth d <= w_depth w)
  /\ (forall w data, i_witness (inform w data) = w)
  /\ (forall w data, info_bits (inform w data) <= length data)
  /\ (forall w, info_bits (inform w []) = 0).
Proof.
  split; [ | split; [ | split ] ].
  - intros w data d Hd. split; [ apply (read_subset_data w data d Hd) | apply (read_within_depth w data d Hd) ].
  - exact information_has_bearer.
  - exact info_le_data.
  - intro w. exact (proj2 (no_presence_no_knowledge w)).
Qed.

Print Assumptions knowledge_ladder.
Print Assumptions watershed.
Print Assumptions types_follow_the_race.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  19 Qed, 0 Admitted, 0 axioms.                                            *)
(*  A formal base for the Теория Знания branch: the ladder данные ->          *)
(*  информация -> знание as types, with the WATERSHED as TWO BEARERS — data   *)
(*  are SOURCE-borne (manifested by the knowable, objective), information      *)
(*  ADDS the WITNESS-bearer (someone's) and is doubly borne (manifestation_   *)
(*  chain) — where information theory enters (info_bits = resolved            *)
(*  distinctions, 1 binary distinction = 1 bit).  Reading is grounded (R2)    *)
(*  and depth-bounded (R3); knowledge resolves <= what was presented; the     *)
(*  знание-о completes/diverges by SOURCE (KThat bounded completes, KHow      *)
(*  inside-process diverges); присутствие/знание-как = positions, передача    *)
(*  second-hand (§8).  Unifies KnowledgeProcess.v +                            *)
(*  KnowledgeGap.v under one ladder. *)
(* ========================================================================= *)
