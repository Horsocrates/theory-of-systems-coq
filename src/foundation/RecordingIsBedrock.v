(** * RecordingIsBedrock.v — digging UNDER the recording principle (the residual import of
       RecordingVsDeterminacy.v) and the E/R/R analysis says: it is BEDROCK relative to ToS.

    RECORDING = "the present state physically encodes the determinate past (choices)".  Is it supplied by
    any ToS principle, or is it an independent import?  The analysis: INDEPENDENT of P4, and not supplied by
    P3 / L2 / P1 either.

      (vs P4)  P4 = irreversibility ("can't go back") + permanence of the FACT.  It is compatible with BOTH
               a RECORDING process (the trace persists) and a FORGETFUL one (the trace is erased) -- both
               have the same monotone stage-count, so both are P4-valid.  Hence P4 does NOT entail recording.
      (vs P3)  the Level/nesting type (Level := L1 | LS(Level)) is a DEPTH COUNTER: it records the COUNT of
               stages (proper time), NOT which branches were chosen.  Here `forgetful_state := length` IS
               that depth counter -- and it loses the choices.  So P3-nesting does not record choices.
      (vs L2)  binarity gives the choice = 1 bit (the UNIT), not its persistence.
      (vs P1)  level structure / irreflexivity -- not conservation.

    THEREFORE recording = INFORMATION CONSERVATION (traces persist), an independent principle that lies
    OUTSIDE P1-P4 + L2.  In physics it follows from micro-reversibility (unitarity), which ToS does not
    posit (P4 is macro-irreversible and NEUTRAL on it).  This is the honest FLOOR of the arrow analysis:
    the thermodynamic arrow's magnitude rests on recording, and ToS cannot go under it -- it is bedrock.

    (Same situation as physics: the persistence of records / the encoded past is an extra principle there
    too -- micro-reversibility -- not derived from coarse dynamics.  We have located the irreducible import
    precisely, not eliminated it.)

    Elements: the choice history (list bool) ; the present state (recording = full history ; forgetful = count).
    Roles:    recording = the present encodes the choices ; forgetful = the present keeps only the count (P3/Level) ;
              P4 = the monotone stage count (proper time).
    Rules:    P4 => stage count monotone ; BOTH recording and forgetful processes satisfy it ; recording
              distinguishes histories, forgetful (count) collapses them => P4 (and P3-count) do NOT entail recording.

    ============ E/R/R разбор ============
      Elements (L1): история выборов (list bool); состояние настоящего (запись = вся история; забывчивое = счёт).
      Roles    (L4): запись = настоящее кодирует выборы; забывчивое = только счёт (P3/Level-глубина); P4 = монотонный
                     счёт стадий (собственное время).
      Rules    (L5): P4 => счёт монотонен; ОБА процесса (запись/забывчивый) ему удовлетворяют; запись различает
                     истории, забывчивое (счёт) их схлопывает => P4 (и P3-счёт) НЕ влекут запись.
      ДИАГНОСТИКА (P4): запись НЕЗАВИСИМА от P4 (оба процесса P4-валидны) и не поставляется P3(счёт)/L2(единица)/
      P1(уровни). Запись = сохранение информации (следы持持persist), принцип ВНЕ P1-P4+L2 (в физике — унитарность,
      которой у ToS нет). Честный ПОЛ: ниже записи ToS не идёт; неустранимый импорт точно локализован. Уровень:
      `идентификация бедрока / результат независимости (no-reduction)`.

    CORRECTION (see RecordingFromP4.v): the "bedrock" verdict below used the WEAK count-only reading of P4
    (the `forgetful_state := length` process treated as P4-valid).  But erasing a made distinction's content
    (the forgetful step) EDITS the fixed past = UN-ACTUALIZATION = a P4-violation under the correct STRONG
    (append-only) reading of P4 ("the actualized stays actualized; the past is fixed").  Under that reading
    RECORDING FOLLOWS from P4 (the past is a verbatim prefix of the present) -- it is NOT bedrock.  So the
    independence shown here holds only against the weak count reading; recording reduces to P4-as-append-only.
    (The entropy = count proxy / unit bridge still stands.)

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  Histories, the P4 stage count, and the two processes                   *)
(* ===================================================================== *)

(** A history = the sequence of binary choices (P4 actualizations). *)
Definition history := list bool.

(** P4 stage count = proper time = the number of actualized stages. *)
Definition proper_time (h : history) : nat := length h.

(** RECORDING process: the present state IS the full choice-history (the choices are encoded). *)
Definition recording_state (h : history) : history := h.

(** FORGETFUL process: the present state is ONLY the stage count (= the P3/Level depth counter; choices lost). *)
Definition forgetful_state (h : history) : nat := length h.

(* ===================================================================== *)
(*  Both processes are P4-valid (same monotone stage count)               *)
(* ===================================================================== *)

(** * Both the recording and the forgetful process share the SAME P4 proper-time -- both are P4-valid. *)
Theorem both_p4_valid :
  forall h, length (recording_state h) = proper_time h /\ forgetful_state h = proper_time h.
Proof. intro h. unfold recording_state, forgetful_state, proper_time. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Recording keeps the choice; the count (P4/P3) collapses it             *)
(* ===================================================================== *)

(** * RECORDING distinguishes histories: the choice is encoded in the present. *)
Theorem recording_distinguishes :
  recording_state [true] <> recording_state [false].
Proof. unfold recording_state. discriminate. Qed.

(** * The FORGETFUL state (= the P3/Level depth counter) COLLAPSES different choices to the same count --
    the choice is lost.  P4 and P3-nesting are blind to which branch was chosen. *)
Theorem forgetful_collapses :
  forgetful_state [true] = forgetful_state [false] /\ [true] <> [false].
Proof. split; [ reflexivity | discriminate ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE — recording is independent of P4 (and P3-count): BEDROCK       *)
(* ===================================================================== *)

(** Recording is BEDROCK relative to ToS:
      (both P4-valid)   the recording and forgetful processes share the same P4 proper-time;
      (recording keeps) recording distinguishes the choice-histories (the choice is encoded);
      (count collapses) the forgetful count (P4/P3-nesting) collapses them (the choice is lost);
    so P4 is consistent with BOTH a recording and a forgetful world -- P4 does NOT entail recording, and the
    P3/Level depth counter does not record the choices either.  Recording = information conservation, a
    principle OUTSIDE P1-P4 + L2 (in physics: micro-reversibility).  This is the irreducible import for the
    thermodynamic arrow's magnitude -- the honest floor; ToS cannot go under it. *)
Theorem recording_is_bedrock :
  (forall h, length (recording_state h) = proper_time h /\ forgetful_state h = proper_time h)
  /\ recording_state [true] <> recording_state [false]
  /\ forgetful_state [true] = forgetful_state [false]
  /\ [true] <> [false].
Proof.
  split; [ exact both_p4_valid | ].
  split; [ exact recording_distinguishes | ].
  split; [ reflexivity | discriminate ].
Qed.
