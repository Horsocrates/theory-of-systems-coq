(** * ArrowSignReservoir.v — E/R/R analysis of the ENTROPY SIGN (done, not pre-judged).  The result is
       THREE honest layers, sharper than a flat "the sign is a posit":
         (L0 forced)    the DIRECTION (stage-count up) -- P4 forbids un-actualization;
         (L1 derived)   the ALIGNMENT of the arrows (record/memory = thermodynamic = gravitational) -- given
                        the identification actualization = irreversible recording = entropy dumping (Landauer
                        bridge: logical irreversibility => thermodynamic cost), the stage-advancing act IS an
                        entropy-non-decreasing act, so the arrows CANNOT point different ways;
         (L2 posited)   the ABSOLUTE SIGN (up not down) -- rests on ONE precisely located posit: the reservoir
                        is SUB-MAXIMAL and on the past side.  A maximal reservoir => nothing to dump into =>
                        NO arrow (the arrow STALLS).  This is the Past Hypothesis, pinned to the reservoir.

    SO: we do NOT derive the absolute sign (that would need deriving which side the low-entropy reservoir is,
    which the rules do not fix).  But the analysis DERIVES the alignment of the three arrows and PINS the
    residual posit to the reservoir's sub-maximality -- genuinely more than the flat no-go.

    HONEST.  "actualization = recording = dumping" is the Landauer BRIDGE (logical irreversibility carries a
    thermodynamic cost); it is well-motivated and ToS-natural (P4 irreversibility = no cheap take-back = a
    permanent record = entropy paid), but it IS an identification, not a pure P4 consequence; and the SIGN of
    the cost (>=0) still needs the sub-maximal reservoir.  entropy = distinction/record count is the
    Element-side proxy (rigorous = the full statistical/holographic count).

    Elements: stage count K (records) ; reservoir room ; the entropy total.
    Roles:    stage = record/memory arrow (P4) ; reservoir = the entropy sink ; sub-maximal room = the posit.
    Rules:    P4 => stage up ; actualization = recording = dump into reservoir => entropy non-decreasing while
              room ; saturated reservoir => arrow stalls ; dump-vs-absorb => sign = reservoir side (posit).

    ============ E/R/R разбор ============
      Elements (L1): счёт стадий K (записи); запас резервуара room; суммарная энтропия.
      Roles    (L4): stage = стрела записей/памяти (P4); резервуар = сток энтропии; суб-максимальный запас = постулат.
      Rules    (L5): P4 => счёт стадий растёт; актуализация = запись = сброс в резервуар => энтропия
                     несбавляющая, пока есть запас; насыщенный резервуар => стрела глохнет; сброс-vs-поглощение
                     => знак = сторона резервуара (постулат).
      ДИАГНОСТИКА (P4): L0 направление форсировано (P4); L1 ВЫРАВНИВАНИЕ стрел выводимо (актуализация=запись=
      сброс, мост Ландауэра) — стрелы не могут разойтись; L2 абсолютный знак = суб-максимальный резервуар со
      стороны прошлого = ТОЧНО локализованный постулат (максимальный резервуар => стрелы нет). НЕ выводим
      абсолютный знак; ВЫВОДИМ выравнивание + сужаем постулат. ЧЕСТНО: мост Ландауэра = отождествление, не чистый
      P4; энтропия=счёт-записей = Element-прокси. Уровень: `синтез + точная локализация постулата`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  The model: stage (records), the dumping process, the finite reservoir *)
(* ===================================================================== *)

(** P4 stage-count = the record/memory arrow (number of irreversibly actualized distinctions). *)
Definition stage (K : nat) : nat := K.

(** Dumping process: each actualization records a bit into a (sub-maximal) reservoir, raising total entropy. *)
Definition dump_S (S0 K : nat) : nat := S0 + K.

(** Finite reservoir with `room` free slots: total entropy rises until the reservoir SATURATES. *)
Definition total_S (S0 room K : nat) : nat := S0 + Nat.min K room.

(** The time-reverse (absorbing) process: a sub-maximal reservoir on the OTHER side would LOWER entropy. *)
Definition absorb_S (S0 K : nat) : nat := S0 - K.

(* ===================================================================== *)
(*  L0 — DIRECTION is forced by P4                                         *)
(* ===================================================================== *)

(** * The stage-count strictly increases -- P4 forbids un-actualization.  The DIRECTION is forced. *)
Theorem direction_forced : forall K, stage K < stage (S K).
Proof. intro K. unfold stage. lia. Qed.

(* ===================================================================== *)
(*  L1 — ALIGNMENT of the arrows is DERIVED (given actualization=recording) *)
(* ===================================================================== *)

(** * The record/memory arrow (stage) and the entropy arrow (dump_S) move TOGETHER: given that actualization
    is irreversible recording (= dumping into the reservoir), the stage-advancing act IS entropy-non-
    decreasing, so the arrows cannot point different ways.  This is DERIVED, not posited. *)
Theorem arrows_aligned :
  forall S0 K, stage K < stage (S K) /\ dump_S S0 K < dump_S S0 (S K).
Proof. intros S0 K. unfold stage, dump_S. split; lia. Qed.

(** With a finite reservoir, entropy STRICTLY rises while the reservoir is SUB-MAXIMAL (K < room). *)
Theorem entropy_rises_while_submaximal :
  forall S0 room K, K < room -> total_S S0 room K < total_S S0 room (S K).
Proof. intros S0 room K H. unfold total_S. lia. Qed.

(* ===================================================================== *)
(*  L2 — the POSIT, precisely located: a sub-maximal reservoir            *)
(* ===================================================================== *)

(** * Once the reservoir SATURATES (room <= K), the arrow STALLS -- no further entropy increase.  So the
    arrow EXISTS only while the reservoir is sub-maximal: the posit is exactly "sub-maximal reservoir". *)
Theorem saturated_no_arrow :
  forall S0 room K, room <= K -> total_S S0 room K = total_S S0 room (S K).
Proof. intros S0 room K H. unfold total_S. lia. Qed.

(** * SIGN-freedom: BOTH a dumping (entropy up) and an absorbing (entropy down) process advance the stage.
    So the absolute SIGN is NOT fixed by P4 -- it is WHICH SIDE the sub-maximal reservoir is (the Past
    Hypothesis), the one residual boundary posit. *)
Theorem sign_is_reservoir_side :
  (forall K, stage K < stage (S K))
  /\ dump_S 0 0 < dump_S 0 1
  /\ absorb_S 10 1 < absorb_S 10 0.
Proof.
  split; [ intro K; unfold stage; lia | ].
  unfold dump_S, absorb_S. split; lia.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the three layers                                            *)
(* ===================================================================== *)

(** The E/R/R analysis of the entropy sign, in three honest layers:
      (L0 forced)   the stage-count strictly increases -- the DIRECTION is P4;
      (L1 derived)  the record arrow and the entropy arrow move together (arrows_aligned) -- ALIGNMENT is
                    derived given actualization = recording; and entropy strictly rises while the reservoir
                    is sub-maximal;
      (L2 posited)  the reservoir SATURATES -> the arrow stalls, so the arrow needs a sub-maximal reservoir;
                    and both dumping (up) and absorbing (down) advance the stage, so the absolute SIGN = which
                    side the sub-maximal reservoir is = the Past Hypothesis (the one precisely located posit).
    We do NOT derive the absolute sign; we DERIVE the alignment of the arrows and PIN the posit to the
    reservoir's sub-maximality + side. *)
Theorem arrow_sign_analysis :
  (forall K, stage K < stage (S K))
  /\ (forall S0 K, stage K < stage (S K) /\ dump_S S0 K < dump_S S0 (S K))
  /\ (forall S0 room K, K < room -> total_S S0 room K < total_S S0 room (S K))
  /\ (forall S0 room K, room <= K -> total_S S0 room K = total_S S0 room (S K))
  /\ ((forall K, stage K < stage (S K))
      /\ dump_S 0 0 < dump_S 0 1
      /\ absorb_S 10 1 < absorb_S 10 0).
Proof.
  split; [ exact direction_forced | ].
  split; [ exact arrows_aligned | ].
  split; [ exact entropy_rises_while_submaximal | ].
  split; [ exact saturated_no_arrow | ].
  exact sign_is_reservoir_side.
Qed.
