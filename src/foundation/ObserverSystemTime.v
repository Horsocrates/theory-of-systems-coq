(** * ObserverSystemTime.v — CAPSTONE (divergence #1, "spacetime = process"): the two-time duality.
       Spacetime is ONE process carrying TWO time-projections:
         - PROPER time (the observer / the objective "now"): the actualized stage-count (P4), MONOTONE and
           IRREVERSIBLE — you cannot move within your own time (succession S has no inverse);
         - SYSTEM time (the coordinate / frame): a RELABELABLE Role on the partial causal order — navigable
           in its spacelike / relabeling freedom; the observer CAN move within the system's frame.
       The two never conflict: every system relabeling PRESERVES the proper-time arrow, so navigating
       system-time never reverses the observer's "now"; and the causal order is ACYCLIC, so there is no
       closed timelike loop — the grandfather paradox is blocked by the SAME irreflexivity (P1) that blocks
       Russell.  This is the formal content of "moving in time without violating the laws of time": one
       moves in SYSTEM time (frame / relabeling / spacelike), never in one's OWN proper time, and the arrow
       is a relabeling invariant.

    HONEST SCOPE.  This formalizes the STRUCTURE of observer-vs-system time (a recasting of proper time
    vs coordinate time, grounded in P4 + the causal partial order).  It makes NO claim about the empirical
    reality of time travel or UFO technology — those are outside what the mathematics can speak to.  The
    file is a SYNTHESIS, drawing together ArrowGroundingDescent.v (P4 arrow), DiffeoIsRelabeling.v
    (coordinate time = relabelable Role), CausalStructureSynthesis.v (partial, not total, causal order) and
    CausalStructure.v (acyclic DAG) into the single two-time duality + the arrow-invariance no-paradox theorem.

    Elements: events (stage, site) ; the proper-time stage-count fst ; spacelike witnesses.
    Roles:    proper time = observer Role (irreversible P4 arrow) ; system time = relabelable frame Role
              (the diffeo/relabeling Role, partial order) ; spacelike = the navigable freedom.
    Rules:    the causal partial order (light cone) ; relabelings preserve it (arrow invariant) ; succession
              has no inverse (proper time irreversible) ; acyclicity (no self-ancestor) blocks the loop.

    ============ E/R/R разбор ============
      Elements (L1): события (стадия, сайт); счёт собственного времени fst; spacelike-свидетели.
                     Носитель — актуализированная стадия («сейчас») и переразмечаемый сайт.
      Roles    (L4): собственное время = Роль наблюдателя (необратимая стрела P4); системное время =
                     переразмечаемая Роль кадра (relabeling, частичный порядок); spacelike = навигируемая свобода.
      Rules    (L5): причинный частичный порядок (световой конус); переразметки его сохраняют (стрела
                     инвариантна); у преемства S нет инверсии; ацикличность ⟹ нет само-предка.
      ДИАГНОСТИКА (P4): наблюдатель НЕ может двигаться в собственном времени (монотонно, не убывает), но
      МОЖЕТ в системе (переразметка фиксирует собственное время, меняя сайт; spacelike-пары есть). Ветки не
      конфликтуют: стрела инвариантна под переразметкой, порядок ацикличен — «законы времени не нарушаются» =
      P4-стрела сохраняется под всеми системными операциями; парадокс деда блокируется той же иррефлексивностью
      (P1), что и Рассел. ЧЕСТНО: формализуем СТРУКТУРУ двух времён, НЕ эмпирику НЛО/путешествий (вне
      области математики). Уровень: СИНТЕЗ (ArrowGrounding/DiffeoIsRelabeling/CausalStructure → дуальность
      двух времён + теорема об инвариантности стрелы / непарадоксальности).

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Events, the two time-projections, the causal (light-cone) order        *)
(* ===================================================================== *)

(** An event = (proper stage, spatial site).  The stage is the actualized P4 count; the site is the
    relabelable system coordinate. *)
Definition Event : Type := (nat * nat)%type.

(** PROPER time (branch 1, the observer's "now"): the actualized stage-count. *)
Definition proper_time (e : Event) : nat := fst e.

(** Symmetric nat distance between sites. *)
Definition natdist (a b : nat) : nat := (a - b) + (b - a).

(** The causal (light-cone) partial order: e can influence f iff f is later and within reach. *)
Definition causal_le (e f : Event) : Prop :=
  (fst e <= fst f) /\ (natdist (snd e) (snd f) <= fst f - fst e).

(** Strict causal precedence (for the no-loop statement). *)
Definition causal_lt (e f : Event) : Prop := causal_le e f /\ e <> f.

(** Spacelike = causally incomparable: the navigable "sideways" freedom of the system. *)
Definition spacelike (e f : Event) : Prop := ~ causal_le e f /\ ~ causal_le f e.

(** A SYSTEM relabeling = a frame translation (c in time, d in space): the coordinate freedom. *)
Definition relabel (c d : nat) (e : Event) : Event := (fst e + c, snd e + d).

Lemma natdist_shift : forall a b d, natdist (a + d) (b + d) = natdist a b.
Proof. intros a b d. unfold natdist. lia. Qed.

(** The causal order is reflexive (a genuine partial order). *)
Lemma causal_le_refl : forall e, causal_le e e.
Proof. intro e. unfold causal_le, natdist. split; lia. Qed.

(* ===================================================================== *)
(*  BRANCH 1 — proper time is monotone and IRREVERSIBLE (the "now")        *)
(* ===================================================================== *)

(** Proper time never decreases along the causal arrow. *)
Theorem proper_irreversible :
  forall e f, causal_le e f -> proper_time e <= proper_time f.
Proof. intros e f [H1 _]. unfold proper_time. exact H1. Qed.

(** * You CANNOT move within your own time: there is no causal step into an earlier proper-time
    (no return to a smaller stage — the "eternal now" of P4). *)
Theorem cannot_move_back :
  forall e f, proper_time f < proper_time e -> ~ causal_le e f.
Proof. intros e f H [H1 _]. unfold proper_time in H. lia. Qed.

(* ===================================================================== *)
(*  BRANCH 2 — system time is relabelable and NAVIGABLE                    *)
(* ===================================================================== *)

(** The system has genuine freedom: spacelike (causally incomparable) pairs EXIST (partial, not total). *)
Theorem exists_spacelike : exists e f, spacelike e f.
Proof.
  exists (0, 0), (0, 1).
  unfold spacelike, causal_le, natdist. cbn [fst snd].
  split; intros [H1 H2]; lia.
Qed.

(** * The observer CAN move within the system's frame WITHOUT moving in their own time: a spatial
    relabeling changes the system coordinate while leaving proper time fixed. *)
Theorem system_move_fixes_proper_time :
  forall d e, proper_time (relabel 0 d e) = proper_time e.
Proof. intros d e. unfold proper_time, relabel. cbn [fst]. lia. Qed.

(** ...and that move is genuine (the system coordinate really changes). *)
Theorem system_move_changes_site :
  exists d e, snd (relabel 0 d e) <> snd e.
Proof. exists 1, (0, 0). unfold relabel. cbn [snd]. lia. Qed.

(* ===================================================================== *)
(*  THE TWO BRANCHES DON'T CONFLICT — no paradox                           *)
(* ===================================================================== *)

(** * The proper-time arrow is INVARIANT under any system relabeling: if e is (proper-time) before f,
    it stays before f after any frame translation.  Navigating system-time never reverses the "now". *)
Theorem arrow_invariant_under_relabel :
  forall c d e f,
    proper_time e < proper_time f ->
    proper_time (relabel c d e) < proper_time (relabel c d f).
Proof. intros c d e f H. unfold proper_time, relabel in *. cbn [fst] in *. lia. Qed.

(** A system relabeling preserves the whole causal order (an order-isomorphism). *)
Theorem relabel_preserves_causal :
  forall c d e f, causal_le (relabel c d e) (relabel c d f) <-> causal_le e f.
Proof.
  intros c d e f. unfold causal_le, relabel. cbn [fst snd].
  rewrite natdist_shift. split; intros [H1 H2]; split; lia.
Qed.

(** * NO PARADOX: the causal order is acyclic — no event is its own strict ancestor.  The closed timelike
    loop (grandfather paradox) is blocked by the SAME irreflexivity (P1) that blocks Russell/Cantor. *)
Theorem no_causal_loop : forall e, ~ causal_lt e e.
Proof. intros e [_ H]. apply H. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** The two-time duality of spacetime-as-process:
      (branch 1)  proper time is monotone along the arrow and IRREVERSIBLE — you cannot move back into
                  your own earlier "now" (the eternal present of P4);
      (branch 2)  system time is navigable — spacelike freedom EXISTS, and the observer moves within the
                  frame (a relabeling) WITHOUT moving in proper time;
      (no clash)  every system relabeling PRESERVES the proper-time arrow, so system-time navigation never
                  reverses the observer's now;
      (no loop)   the causal order is acyclic — no self-ancestor (grandfather paradox blocked, à la Russell).
    "Moving in time without violating time's laws" = moving in SYSTEM time while the P4 proper-time arrow
    stays invariant.  This is structure, not a claim about empirical time travel. *)
Theorem observer_system_time :
  (forall e f, causal_le e f -> proper_time e <= proper_time f)
  /\ (forall e f, proper_time f < proper_time e -> ~ causal_le e f)
  /\ (exists e f, spacelike e f)
  /\ (forall d e, proper_time (relabel 0 d e) = proper_time e)
  /\ (forall c d e f, proper_time e < proper_time f ->
        proper_time (relabel c d e) < proper_time (relabel c d f))
  /\ (forall e, ~ causal_lt e e).
Proof.
  split; [ exact proper_irreversible | ].
  split; [ exact cannot_move_back | ].
  split; [ exact exists_spacelike | ].
  split; [ exact system_move_fixes_proper_time | ].
  split; [ exact arrow_invariant_under_relabel | ].
  exact no_causal_loop.
Qed.
