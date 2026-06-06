(** * PumpingPigeonhole.v — discharging the finite-memory hypothesis (Phase 3b tightening)
      Makes PumpingRoleLimit.no_dfa_for_anbn UNCONDITIONAL by PROVING the prefix collision from
      an explicit finite state enumeration (the pigeonhole), instead of assuming it.

      A DFA is given by a finite state type: an enumeration `enum : list Q` covering all states
      (`enum_complete`) and decidable equality (`eqdecQ`).  The S·|enum| prefix-states
      gpref 0 … gpref (|enum|) cannot all be distinct (they live in a set of size |enum|), so two
      collide — `gpref_collision`.  Feeding that to no_dfa_for_anbn closes a^n b^n unconditionally.

    Reuses cs/RegularElementFloor.v (run, accepts) and cs/PumpingRoleLimit.v (word_a, In_L,
    no_dfa_for_anbn).  Honest level: methods (standard finite pigeonhole), 0 axioms.

    Elements: automaton states (the finite list enum), prefix indices
    Roles:    "the visited state" gpref n; enum = the carrier of finite memory
    Rules:    pigeonhole — mapping S·|enum| indices into |enum| states must collide (NoDup + length)

    ============ E/R/R разбор ============
      Rules (L5): pigeonhole — отображение S·|enum| индексов в |enum| состояний ОБЯЗАНО
                  столкнуться (NoDup + длина).
      Roles (L4): «посещённое состояние» gpref n; enum = носитель конечной памяти.
      Elements  : состояния Q (конечный список enum), индексы-префиксы.
    ДИАГНОСТИКА (P4): это РАЗРЯДКА finite-memory-гипотезы из PumpingRoleLimit.v — конечность
      АКТУАЛЬНОЙ памяти (enum, P4) ДОКАЗУЕМО форсирует коллизию префиксов → a^n b^n безусловно не
      распознаётся.  role-limit-стена для языков теперь стоит на 0 гипотез сверх «конечный enum +
      разрешимое равенство» (= собственно конечный автомат).

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Lia.
Import ListNotations.
From ToS Require Import cs.RegularElementFloor.
From ToS Require Import cs.PumpingRoleLimit.

Section Pigeonhole.

  Variable Q : Type.
  Variable eqdecQ : forall x y : Q, {x = y} + {x <> y}.
  Variable delta : Q -> bool -> Q.
  Variable acc : Q -> bool.
  Variable q0 : Q.
  Variable enum : list Q.
  Hypothesis enum_complete : forall q, In q enum.

  (** The state reached after reading the a-prefix of length n. *)
  Definition gpref (n : nat) : Q := run delta q0 (word_a n).

  (** seq has no duplicates (replicated locally, cf. Core_ERR.NoDup_seq_local). *)
  Lemma seq_nodup_local : forall len start, NoDup (seq start len).
  Proof.
    induction len as [|n IH]; intro start; simpl.
    - constructor.
    - constructor; [rewrite in_seq; lia | apply IH].
  Qed.

  (** If [gpref] maps a duplicate-free index list to a list WITH a duplicate, it is not
      injective there: two distinct indices share a prefix-state. *)
  Lemma map_collision : forall (l : list nat),
    NoDup l -> ~ NoDup (map gpref l) ->
    exists x y, x <> y /\ gpref x = gpref y.
  Proof.
    induction l as [|x l' IH]; intros Hnd Hmap.
    - simpl in Hmap. exfalso. apply Hmap. constructor.
    - simpl in Hmap. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hxnotin Hndl'].
      destruct (in_dec eqdecQ (gpref x) (map gpref l')) as [Hin | Hnin].
      + apply in_map_iff in Hin. destruct Hin as [y [Hgy Hyin]].
        exists x, y. split.
        * intro Heq. subst y. contradiction.
        * symmetry. exact Hgy.
      + apply IH; [exact Hndl' |].
        intro Hndmap'. apply Hmap. constructor; [exact Hnin | exact Hndmap'].
  Qed.

  (** ★ PIGEONHOLE: two distinct a-prefixes reach the same state. *)
  Lemma gpref_collision : exists i j, i <> j /\ gpref i = gpref j.
  Proof.
    set (idxs := seq 0 (S (length enum))).
    assert (Hincl : incl (map gpref idxs) enum).
    { intros q Hq. apply in_map_iff in Hq. destruct Hq as [n [Hn _]].
      rewrite <- Hn. apply enum_complete. }
    assert (Hnotnd : ~ NoDup (map gpref idxs)).
    { intro Hnd. pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
      rewrite length_map in Hlen. unfold idxs in Hlen. rewrite length_seq in Hlen. lia. }
    apply (map_collision idxs); [ unfold idxs; apply seq_nodup_local | exact Hnotnd ].
  Qed.

  (** ★ NO DFA recognises a^n b^n — UNCONDITIONALLY (the pigeonhole is now proven, not assumed). *)
  Theorem no_dfa_for_anbn_unconditional :
    (forall w, accepts delta acc q0 w = true <-> In_L w) -> False.
  Proof.
    intro Hdfa.
    destruct gpref_collision as [i [j [Hij Hcol]]].
    apply (no_dfa_for_anbn Q delta acc q0 Hdfa).
    exists i, j. split; [exact Hij | exact Hcol].
  Qed.

End Pigeonhole.

(** Phase 3b is now complete with NO finite-memory hypothesis: regular = the Element floor that
    PROVABLY cannot count — a^n b^n is its role-limit, forced by the finiteness of the state set
    (P4) alone.  The whole language picture (Element floor + role-limit) is axiom-free. *)

Print Assumptions no_dfa_for_anbn_unconditional.
