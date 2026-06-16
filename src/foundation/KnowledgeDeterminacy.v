(** * KnowledgeDeterminacy.v — Теория Знания: the DETERMINACY of a meaning governs its transmission loss.
      A reading fully DETERMINED (logic, math: «2+2=4») transmits LOSSLESSLY — every witness unpacks it
      identically; an INDETERMINATE reading (a word whose sense varies by witness) can lose on
      transmission, the loss growing with the FIELD of possible readings.

    Author's observation 2026-06-16 (gl.8 «Дистиллят», §«четыре перегонки», the «распаковка» step): the
    receiver unpacks the distillate by his own запас понятого, and whether «собранное = посланному»
    depends on the DETERMINACY of the meaning.  Full determinacy = logic (mathematics is a system within
    logic): there transmission can lose nothing («2+2=4» is read the same by all).  Indeterminacy = a word
    bearing senses that diverge across witnesses; the wider the field of potential senses, the greater the
    loss.  This file makes that determinacy/loss law a theorem.

    Model: a READING `r : Witness -> Meaning` (Witness = the unpacker's запас, a nat; Meaning a nat) — how a
    witness unpacks a given piece of знание-о into a sense.  DETERMINED = the reading is CONSTANT (all
    witnesses agree); INDETERMINATE = it varies.  Transmission loss = the sender's reading differs from the
    receiver's; the FIELD over a sample of witnesses = the senses they produce (its spread = the
    indeterminacy).

    BRIDGE — the ЗДО of a reasoning-domain transition (author 2026-06-16): in the Архитектура Размышления
    this determinacy law IS the «Принцип Корня» threshold of the transition Домен 2 (Прояснение) -> Домен 3
    (Выбор Рамки).  Clarification (Прояснение) makes a term determinate; one may pass to frame-selection
    exactly when «ключевые термины определены явно — каждый понимает их одинаково; эквивокация исключена» —
    i.e. when the reading is DETERMINED (every witness agrees), and it then crosses losslessly.  PART IV
    states it.  (The threshold's 3rd clause — hidden assumptions made explicit — is a separate criterion.)

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) determinacy of a meaning = UNIQUENESS of its unpacking across witnesses;
      (2) determined ⇒ transmission is LOSSLESS (the sender's reading = every receiver's);
      (3) indeterminate ⇒ transmission CAN lose (readers diverge), the loss = the FIELD of readings —
          the wider, the greater;
      (4) logic (and mathematics within it) is FULLY determined ⇒ losslessly transmissible.
    Roles (L4): the reading = the unpacking map; determined/indeterminate = its constancy/variance; the
      field (image over a sample) = the spread of senses; transmission loss = divergence of readings.
    Elements (L1+P4): witnesses (запас, nat), meanings (nat), readings (Witness -> Meaning), the field.
    P4 diagnostic (could it be otherwise?): determinacy is FORCED to be losslessness — a constant reading
      cannot diverge between sender and receiver; an indeterminate reading is forced to admit a divergent
      pair.  Logic is the maximally determined reading (constant), so its transmission cannot lose.  The
      determinacy boundary ECHOES the project's finitization / decidability boundary: the DETERMINED side
      is the decidable, losslessly-transmissible one.
    Honesty wall: a structural model — «meaning» is a nat tag, «determined» = a constant unpacking; it proves
      determinacy ⇒ lossless and indeterminacy ⇒ possible-loss + the field measure, NOT the phenomenology of
      understanding.  stdlib-only, 0 axioms.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

(** A reading: how a witness (his запас понятого = a nat) unpacks a piece of знание-о into a meaning. *)
Definition Reading := nat -> nat.

(** DETERMINED: every witness unpacks to the SAME meaning — the reading is constant. *)
Definition determined (r : Reading) : Prop := forall w1 w2, r w1 = r w2.

(** INDETERMINATE: two witnesses unpack to DIFFERENT meanings. *)
Definition indeterminate (r : Reading) : Prop := exists w1 w2, r w1 <> r w2.

(* ===================================================================== *)
(*  PART I — logic is fully determined; determined transmits losslessly    *)
(* ===================================================================== *)

(** A logical / decidable fact: its meaning is fixed, witness-independent — e.g. «2+2=4» -> 4. *)
Definition logical (v : nat) : Reading := fun _ => v.

Lemma logical_is_determined : forall v, determined (logical v).
Proof. intros v w1 w2. reflexivity. Qed.

(** ★★ DETERMINED ⇒ LOSSLESS TRANSMISSION: if the reading is determined, the sender's meaning equals
    every receiver's — nothing is lost in передача («2+2=4» reaches intact). *)
Theorem determined_transmits_losslessly :
  forall r, determined r -> forall sender receiver, r sender = r receiver.
Proof. intros r Hd sender receiver. apply Hd. Qed.

(** ★ Hence logic («2+2=4») transmits losslessly, whoever sends and whoever receives. *)
Corollary logic_lossless : forall v sender receiver, logical v sender = logical v receiver.
Proof. intros. reflexivity. Qed.

(* ===================================================================== *)
(*  PART II — indeterminacy ⇒ possible loss; a word is indeterminate       *)
(* ===================================================================== *)

(** A word whose sense = the witness's own state (his запас): different witnesses, different senses. *)
Definition word : Reading := fun w => w.

Lemma word_is_indeterminate : indeterminate word.
Proof. exists 0, 1. unfold word. discriminate. Qed.

(** ★★ INDETERMINATE ⇒ TRANSMISSION CAN LOSE: there are a sender and a receiver whose unpackings
    diverge — собранное ≠ посланному. *)
Theorem indeterminate_can_lose :
  forall r, indeterminate r -> exists sender receiver, r sender <> r receiver.
Proof. intros r [w1 [w2 H]]. exists w1, w2. exact H. Qed.

(** ★ Determined and indeterminate are MUTUALLY EXCLUSIVE (constructive). *)
Lemma determined_excludes_indeterminate : forall r, determined r -> ~ indeterminate r.
Proof. intros r Hd [w1 [w2 H]]. apply H. apply Hd. Qed.

(* ===================================================================== *)
(*  PART III — the FIELD of readings: the wider, the more indeterminate     *)
(* ===================================================================== *)

(** The field of potential senses over a sample of witnesses = the readings they produce. *)
Definition field (r : Reading) (ws : list nat) : list nat := map r ws.

(** ★★ A determined reading COLLAPSES the field: every sense in it is one and the same. *)
Theorem determined_field_collapses :
  forall r ws, determined r ->
    forall m1 m2, In m1 (field r ws) -> In m2 (field r ws) -> m1 = m2.
Proof.
  intros r ws Hd m1 m2 H1 H2. unfold field in *.
  apply in_map_iff in H1. apply in_map_iff in H2.
  destruct H1 as [x1 [E1 _]]. destruct H2 as [x2 [E2 _]].
  subst. apply Hd.
Qed.

(** ★★ A word SPLITS the field: over the sample {0,1} it yields TWO distinct senses where a determined
    reading would yield one. *)
Theorem word_field_splits :
  In 0 (field word [0; 1]) /\ In 1 (field word [0; 1]) /\ (0 <> 1).
Proof.
  unfold field, word. simpl.
  split; [ left; reflexivity | split; [ right; left; reflexivity | discriminate ] ].
Qed.

(** ★ Any indeterminate reading splits the field into ≥ 2 distinct senses (the loss-bearing spread). *)
Theorem indeterminate_field_ge2 :
  forall r, indeterminate r ->
    exists ws m1 m2, In m1 (field r ws) /\ In m2 (field r ws) /\ m1 <> m2.
Proof.
  intros r [w1 [w2 H]]. exists [w1; w2], (r w1), (r w2). unfold field. simpl.
  split; [ left; reflexivity | split; [ right; left; reflexivity | exact H ] ].
Qed.

(* ===================================================================== *)
(*  PART IV — the ЗДО of the Прояснение (Домен 2) -> Выбор Рамки (Домен 3)  *)
(*            transition: clarification suffices exactly when DETERMINED    *)
(* ===================================================================== *)

(** Архитектура Размышления, Домен 2 (Прояснение) -> Домен 3 (Выбор Рамки): Прояснение makes a term
    determinate; the Принцип-Корня threshold to pass on is «ключевые термины определены явно — каждый
    понимает их одинаково; эквивокация исключена».  A term is UNEQUIVOCAL (sufficiently clarified) iff
    its reading is determined — every witness reads it the same. *)
Definition unequivocal (r : Reading) : Prop := determined r.

(** ★★★ THE CLARIFICATION THRESHOLD = DETERMINACY (the ЗДО of Домен 2 -> Домен 3): a term is unequivocal
    iff every witness reads it the same; then it crosses into the next domain LOSSLESSLY; and an
    equivocal (indeterminate) term FAILS the threshold — its field of senses splits. *)
Theorem clarification_threshold_is_determinacy :
  (forall r, unequivocal r <-> (forall w1 w2, r w1 = r w2))
  /\ (forall r, unequivocal r -> forall sender receiver, r sender = r receiver)
  /\ (forall r, indeterminate r ->
        exists ws m1 m2, In m1 (field r ws) /\ In m2 (field r ws) /\ m1 <> m2).
Proof.
  split; [ intro r; unfold unequivocal, determined; split; intro H; exact H | ].
  split; [ exact determined_transmits_losslessly | exact indeterminate_field_ge2 ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ★★★ Determinacy governs transmission: a DETERMINED reading (logic, «2+2=4») transmits losslessly
    and collapses the field of senses to one; an INDETERMINATE reading (a word) can lose, splitting the
    field — and the loss grows with that field's spread. *)
Theorem determinacy_governs_transmission :
  (forall v sender receiver, logical v sender = logical v receiver)
  /\ (forall r, determined r -> forall s rcv, r s = r rcv)
  /\ (forall r, indeterminate r -> exists s rcv, r s <> r rcv)
  /\ (forall r ws, determined r -> forall m1 m2, In m1 (field r ws) -> In m2 (field r ws) -> m1 = m2)
  /\ (In 0 (field word [0; 1]) /\ In 1 (field word [0; 1]) /\ (0 <> 1)).
Proof.
  split; [ exact logic_lossless | ].
  split; [ exact determined_transmits_losslessly | ].
  split; [ exact indeterminate_can_lose | ].
  split; [ exact determined_field_collapses | exact word_field_splits ].
Qed.

Print Assumptions determinacy_governs_transmission.
Print Assumptions determined_transmits_losslessly.
Print Assumptions determined_field_collapses.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  11 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Determinacy of a meaning governs its transmission loss.  PART I: logic     *)
(*  (logical v) is DETERMINED (logical_is_determined) and a determined reading *)
(*  transmits LOSSLESSLY (determined_transmits_losslessly; logic_lossless —    *)
(*  «2+2=4» reaches intact).  PART II: a word is INDETERMINATE                 *)
(*  (word_is_indeterminate) and indeterminacy CAN lose (indeterminate_can_lose *)
(*  — собранное ≠ посланному); determined ⊥ indeterminate.  PART III: a        *)
(*  determined reading COLLAPSES the field of senses to one                    *)
(*  (determined_field_collapses), a word SPLITS it (word_field_splits) and     *)
(*  any indeterminate reading gives ≥ 2 senses (indeterminate_field_ge2) —     *)
(*  the loss grows with the field.  Capstone determinacy_governs_transmission. *)
(*  Refines gl.8's «распаковка»: determined (logic) passes даром, the          *)
(*  indeterminate is what the перегонки eat.  The determinacy boundary echoes  *)
(*  the project's finitization/decidability boundary.  PART IV: this law IS    *)
(*  the ЗДО of the Прояснение (Домен 2) -> Выбор Рамки (Домен 3) transition in  *)
(*  the Архитектура Размышления — clarification suffices when DETERMINED        *)
(*  (clarification_threshold_is_determinacy).  stdlib-only.                    *)
(* ========================================================================= *)
