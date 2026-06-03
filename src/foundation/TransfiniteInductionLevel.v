(** * TransfiniteInductionLevel.v — well-founded induction over the Level hierarchy
    Elements: Level (L1 | LS), level_lt, level_depth
    Roles:    level_lt = the foundation order; level_depth = its nat rank
    Rules:    level_lt strictly decreases depth => well-founded => strong
              induction; the successor LS always escapes => no top level
    STATUS:   6 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Complements foundation/TransfiniteInduction.v (which is about the ordinal
    notations Ord): HERE the well-founded induction is over the ToS membership
    hierarchy Level (L1 | LS) itself — the order that structurally blocks
    self-membership (P1).

    G2: well-founded / strong induction over Level (level_lt_wf,
        level_strong_induction).
    G3: no level lies above all levels — the "set of all ordinals" /
        Burali-Forti paradox dissolves structurally: the successor LS of any
        candidate top escapes it (level_no_top, no_universal_level).

    E/R/R reading: the hierarchy is a RULE (the foundation order), not a
    completed Element-object "the level of all levels"; the very attempt to
    name a top is refuted by one more step LS.
*)

From ToS Require Import TheoryOfSystems_Core_ERR.
From Stdlib Require Import Wf_nat Lia.

(* ===================== G2: well-founded induction over Level ============= *)

(* level_lt is well-founded because it strictly decreases the nat rank
   level_depth (level_lt_depth, proved in Core_ERR). 0 axioms. *)
Lemma level_lt_wf : well_founded level_lt.
Proof.
  apply (Wf_nat.well_founded_lt_compat Level level_depth).
  exact level_lt_depth.
Qed.

(* Strong (course-of-values) induction over the Level hierarchy *)
Theorem level_strong_induction :
  forall P : Level -> Prop,
    (forall L, (forall L', L' << L -> P L') -> P L) ->
    forall L, P L.
Proof.
  intros P H. apply (well_founded_ind level_lt_wf). exact H.
Qed.

(* ===================== G3: no top level (Burali-Forti analogue) ========= *)

(* Every level is strictly below its own successor *)
Lemma level_lt_succ : forall L, L << LS L.
Proof. intros L. simpl. left. reflexivity. Qed.

(* The successor of L is neither below L nor equal to L *)
Lemma succ_not_le : forall L, ~ (LS L << L \/ LS L = L).
Proof.
  intros L [Hlt | Heq].
  - apply level_lt_depth in Hlt. simpl in Hlt. lia.
  - assert (Hd : level_depth (LS L) = level_depth L) by (rewrite Heq; reflexivity).
    simpl in Hd. lia.
Qed.

(* For any candidate top M, some level (its successor) escapes it:
   it is neither below M nor equal to M. *)
Theorem level_no_top :
  forall M : Level, exists L : Level, ~ (L << M \/ L = M).
Proof.
  intros M. exists (LS M). apply succ_not_le.
Qed.

(* Hence there is NO universal level above-or-equal to every level.
   The "level of all levels" cannot exist (Burali-Forti, dissolved). *)
Theorem no_universal_level :
  ~ exists Top : Level, forall L : Level, L << Top \/ L = Top.
Proof.
  intros [Top Hall].
  exact (succ_not_le Top (Hall (LS Top))).
Qed.
