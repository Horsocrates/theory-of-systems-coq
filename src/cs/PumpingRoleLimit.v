(** * PumpingRoleLimit.v — the role-limit step for languages: finite memory cannot count
      Phase 3b of the Computer-Science branch.  The role-limit complement of RegularElementFloor.v.

      The Element floor (regular languages) cannot count without bound.  Two fully-proven halves:
        (A) PUMPING CORE: a loop in the run can be repeated freely without changing the end state
            (`loop_pump`, `pump_preserves`) — the engine of "finite memory pumps".
        (B) NON-REGULARITY of a^n b^n: a collision of two distinct a-prefixes (same state after
            reading a^i and a^j, i<>j) forces a^j b^i to be accepted too, but a^j b^i is unbalanced
            ⟹ contradiction (`collision_contradicts`, `no_dfa_for_anbn`).  Proven by COUNTING.

    Honest scope (project ethos, cf. HeineBorel_ERR.v's Lebesgue-number hypothesis): the prefix
    COLLISION is the standard pigeonhole (a run of length > |Q| revisits a state).  Here it is
    taken as the explicit FINITE-MEMORY hypothesis; the counting consequence is fully proven.
    Discharging the pigeonhole from an explicit state enumeration is a tightening (backlog).

    Reuses cs/RegularElementFloor.v (run / accepts / run_app).

    Elements: words over {a=false, b=true}, automaton states, the loop word
    Roles:    "the loop" (a state re-entered) = a role-position of re-entry; "accepted" = status
    Rules:    pumping (repeating the loop) preserves the status; finite memory (P4) forces a collision

    ============ E/R/R разбор ============
      Rules (L5): накачка (повторение петли) СОХРАНЯЕТ статус (loop_pump/pump_preserves); конечная
                  память ⟹ коллизия префиксов (pigeonhole) — role-limit-обструкция.
      Roles (L4): «петля» — состояние повторного входа (роль-позиция); «принято» — статус.
      Elements  : слова над {a,b}, состояния, слово-петля.
    ДИАГНОСТИКА (P4): Element-пол (Ф3a) НЕ умеет неограниченно считать — конечная АКТУАЛЬНАЯ память
      (P4) форсирует коллизию префиксов, и a^n b^n (нужен неограниченный счёт) — role-limit для
      регулярных.  Pumping-ядро (петля→накачка) и следствие (коллизия ⟹ не-a^n b^n, через счёт)
      доказаны ПОЛНОСТЬЮ; pigeonhole (конечность ⟹ коллизия) взята как finite-memory-гипотеза
      (паттерн числа Лебега, HeineBorel_ERR.v).  Честно: methods; вклад — рамка «role-limit =
      предел конечной памяти» + связь с Element-полом.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Bool Lia.
Import ListNotations.
From ToS Require Import cs.RegularElementFloor.

(* ===================================================================== *)
(*  PART A — THE PUMPING CORE (a loop repeats freely)                      *)
(* ===================================================================== *)

Section PumpCore.

  Context {Sigma : Type}.
  Variable Q : Type.
  Variable delta : Q -> Sigma -> Q.

  (** [y] repeated [k] times. *)
  Fixpoint repeat_word (y : list Sigma) (k : nat) : list Sigma :=
    match k with O => [] | S k' => y ++ repeat_word y k' end.

  (** A loop at [p] (reading [y] returns to [p]) survives any number of repetitions. *)
  Lemma loop_pump : forall y p k,
    run delta p y = p -> run delta p (repeat_word y k) = p.
  Proof.
    intros y p k Hloop. induction k as [|k IH].
    - reflexivity.
    - change (repeat_word y (S k)) with (y ++ repeat_word y k).
      rewrite run_app, Hloop. exact IH.
  Qed.

  (** Pumping preserves the end state: x ++ y^k ++ z and x ++ z end in the same state,
      when y loops at the state reached after x. *)
  Lemma pump_preserves : forall q0 x y z p k,
    run delta q0 x = p ->
    run delta p y = p ->
    run delta q0 (x ++ repeat_word y k ++ z) = run delta q0 (x ++ z).
  Proof.
    intros q0 x y z p k Hx Hloop.
    rewrite !run_app. rewrite Hx. rewrite (loop_pump y p k Hloop). reflexivity.
  Qed.

End PumpCore.

(* ===================================================================== *)
(*  PART B — NON-REGULARITY of a^n b^n (a=false, b=true)                   *)
(* ===================================================================== *)

Section NonRegular.

  Variable Q : Type.
  Variable delta : Q -> bool -> Q.
  Variable acc : Q -> bool.
  Variable q0 : Q.

  Definition word_a (n : nat) : list bool := repeat false n.
  Definition word_b (n : nat) : list bool := repeat true n.
  Definition In_L (w : list bool) : Prop := exists n, w = word_a n ++ word_b n.

  (* ---- counting a's and b's ---- *)
  Definition cF (w : list bool) : nat := length (filter negb w).
  Definition cT (w : list bool) : nat := length (filter (fun b => b) w).

  Lemma cF_app : forall u v, cF (u ++ v) = cF u + cF v.
  Proof. intros. unfold cF. rewrite filter_app, length_app. reflexivity. Qed.

  Lemma cF_a : forall n, cF (word_a n) = n.
  Proof. unfold cF, word_a. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

  Lemma cF_b : forall n, cF (word_b n) = 0.
  Proof. unfold cF, word_b. induction n; simpl; [reflexivity | exact IHn]. Qed.

  Lemma cT_app : forall u v, cT (u ++ v) = cT u + cT v.
  Proof. intros. unfold cT. rewrite filter_app, length_app. reflexivity. Qed.

  Lemma cT_a : forall n, cT (word_a n) = 0.
  Proof. unfold cT, word_a. induction n; simpl; [reflexivity | exact IHn]. Qed.

  Lemma cT_b : forall n, cT (word_b n) = n.
  Proof. unfold cT, word_b. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

  (** a^j b^i is in L only if i = j (counting a's gives j = m, counting b's gives i = m). *)
  Lemma anbn_balanced : forall i j, In_L (word_a j ++ word_b i) -> i = j.
  Proof.
    intros i j [m Hm].
    assert (HF : cF (word_a j ++ word_b i) = cF (word_a m ++ word_b m)) by (rewrite Hm; reflexivity).
    assert (HT : cT (word_a j ++ word_b i) = cT (word_a m ++ word_b m)) by (rewrite Hm; reflexivity).
    rewrite !cF_app, !cF_a, !cF_b in HF.
    rewrite !cT_app, !cT_a, !cT_b in HT.
    lia.
  Qed.

  (** The finite-memory input (standard pigeonhole, taken as a hypothesis). *)
  Hypothesis dfa_correct : forall w, accepts delta acc q0 w = true <-> In_L w.

  (** A collision of two distinct a-prefixes contradicts recognising a^n b^n. *)
  Theorem collision_contradicts : forall i j,
    i <> j -> run delta q0 (word_a i) = run delta q0 (word_a j) -> False.
  Proof.
    intros i j Hij Hcol.
    assert (Hi : accepts delta acc q0 (word_a i ++ word_b i) = true).
    { apply (proj2 (dfa_correct _)). exists i. reflexivity. }
    assert (Hsame : accepts delta acc q0 (word_a j ++ word_b i)
                  = accepts delta acc q0 (word_a i ++ word_b i)).
    { unfold accepts. rewrite !run_app. rewrite Hcol. reflexivity. }
    assert (Hj : accepts delta acc q0 (word_a j ++ word_b i) = true)
      by (rewrite Hsame; exact Hi).
    apply (proj1 (dfa_correct _)) in Hj.
    apply anbn_balanced in Hj.
    exact (Hij Hj).
  Qed.

  (** ★ NO DFA recognises a^n b^n: finite memory (a prefix collision) makes it impossible. *)
  Theorem no_dfa_for_anbn :
    (exists i j, i <> j /\ run delta q0 (word_a i) = run delta q0 (word_a j)) -> False.
  Proof. intros [i [j [Hij Hcol]]]. exact (collision_contradicts i j Hij Hcol). Qed.

End NonRegular.

(** Together with RegularElementFloor.v: regular = Element floor (decidable, closed), but the
    floor cannot count without bound — a^n b^n is its role-limit.  "role-limit = the limit of
    finite memory."  The pumping core (loop_pump/pump_preserves) is the general engine; the
    pigeonhole that forces the collision from |Q| finite is the cited finite-memory input. *)

Print Assumptions pump_preserves.
Print Assumptions no_dfa_for_anbn.
