(** * RecordingFromP4.v — the user's challenge, confirmed: irreversibility DOES generate conservation of the
       made distinction.  Under the APPEND-ONLY reading of P4 (irreversible actualization = the made
       distinction's CONTENT stays; the actual accumulates content; the past is FIXED), RECORDING FOLLOWS.
       This CORRECTS RecordingIsBedrock.v, which used a too-weak count-only reading.

    THE TWO READINGS OF P4 ("actualization is irreversible").
      - WEAK (count-only): P4 = the stage count is monotone; the CONTENT at a stage may be overwritten going
        forward.  Under this, a "forgetful" process (erase choices, keep count) is P4-valid -> recording is
        independent (RecordingIsBedrock.v).
      - STRONG (append-only): P4 = "the actualized STAYS actualized"; the made distinction's content is never
        removed; the actual ACCUMULATES content; the past is FIXED.  Under this, RECORDING FOLLOWS.

    WHY THE STRONG READING IS THE CORRECT ONE.
      An actualization is always OF a content (committing to A); there is no contentless "event".  So
      "stays actualized" = the content stays.  Overwriting a past choice EDITS the fixed past -- exactly what
      irreversibility forbids -- even though the count goes up.  Erasing a made distinction = returning the
      system to undifferentiated w.r.t. it = UN-ACTUALIZING it = a P4-violation.  So the weak count-only
      reading (which allows erasure) separates the event from its content and is incoherent.

    THE RESULT (append-only model).  The actual = the accumulating list of made choices; actualize = APPEND
    (never remove).  Then the past is a verbatim PREFIX of the present (conserved = recorded); the oldest
    distinction stays at the head; and a "forgetful" step (changing a past entry) is NOT an append = an
    UN-ACTUALIZATION = a P4-violation.  Recording is therefore the CONTENT of P4-irreversibility, not a
    separate bedrock import.

    HONEST RESIDUAL.  (1) This is the STRONG reading; it enriches the bare `Level := L1 | LS` formalization
    (a depth counter that tracks only the count) to content-accumulation -- faithful to P4's "the past is
    fixed", but a richer model than the bare counter.  (2) The entropy = count proxy (the unit bridge to
    physical entropy) still stands -- this concerns conservation of the made DISTINCTION, not the bridge to
    thermodynamic units.  So: recording reduces to P4-as-append-only; the proxy remains.

    Elements: the actual = list of made distinctions (content) ; each appended choice.
    Roles:    P4-actualization = append (irreversible accumulation) ; the past = the conserved prefix ;
              recording = the past is readable from the present.
    Rules:    actualize = append, never remove (P4: content stays) => past conserved (recorded) ; forgetting
              (overwrite/remove a past entry) = un-actualization (~P4).

    ============ E/R/R разбор ============
      Elements (L1): актуальное = список сделанных различий (содержание); добавляемый выбор.
      Roles    (L4): P4-актуализация = добавление (необратимое накопление); прошлое = сохранённый префикс;
                     запись = прошлое читаемо из настоящего.
      Rules    (L5): actualize = append, без удаления (P4: содержание остаётся) => прошлое сохранено (записано);
                     забывание (перезапись/удаление прошлой записи) = раз-актуализация (~P4).
      ДИАГНОСТИКА (P4): пользователь прав — необратимость (append-only, содержание остаётся) ПОРОЖДАЕТ
      сохранение сделанного различия = запись. Слабое счётное чтение (RecordingIsBedrock) разрешало стирание =
      раз-актуализацию, оно некогерентно. Запись НЕ бедрок — это содержание P4. ОСТАТОК: сильное чтение богаче
      голого Level=счётчик (надо обогатить до накопления содержания, верно духу P4); прокси энтропия=счёт стоит.
      Уровень: `редукция записи к P4 (сильное чтение) + коррекция прошлого вывода`.

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  The actual = append-only accumulation of made distinctions (content)   *)
(* ===================================================================== *)

(** The ACTUAL: the accumulating list of made choices (with content).  Strong reading of P4. *)
Definition actual := list bool.

(** P4-actualization: APPEND the chosen branch.  Never remove (irreversible -- the past is fixed). *)
Definition actualize (a : actual) (choice : bool) : actual := a ++ [choice].

(* ===================================================================== *)
(*  Append-only => the past is CONSERVED (recorded)                        *)
(* ===================================================================== *)

(** * The past is a verbatim PREFIX of the present: every made distinction is conserved (recorded). *)
Theorem actualize_conserves_past : forall a c, exists s, actualize a c = a ++ s.
Proof. intros a c. exists [c]. reflexivity. Qed.

(** * The OLDEST made distinction stays at the head -- the earliest record is never overwritten. *)
Theorem actualize_keeps_oldest :
  forall a c, a <> [] -> hd_error (actualize a c) = hd_error a.
Proof.
  intros a c Hne. destruct a as [| x a'].
  - contradiction.
  - unfold actualize. simpl. reflexivity.
Qed.

(* ===================================================================== *)
(*  Forgetting = un-actualization (a P4-violation)                         *)
(* ===================================================================== *)

(** * A "forgetful" step that CHANGES a past entry is NOT a P4-actualization (an append): overwriting the
    fixed past edits the actual -- exactly what irreversibility forbids.  Witness: [true] -> [false] cannot
    be reached by appending to [true]. *)
Theorem forgetting_not_actualization : ~ (exists s, [false] = [true] ++ s).
Proof. intros [s H]. discriminate H. Qed.

(** Every actualization is an APPEND (forward extension), never an edit of the past. *)
Theorem actualize_only_appends : forall a c, actualize a c = a ++ [c].
Proof. intros a c. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE — recording reduces to P4-as-append-only                      *)
(* ===================================================================== *)

(** The user's point, confirmed: under the append-only reading of P4 (the made distinction's content stays;
    the past is fixed), RECORDING follows -- it is the content of P4-irreversibility, not a bedrock import:
      (conserved)   the past is a verbatim prefix of the present (every made distinction recorded);
      (oldest kept) the earliest distinction is never overwritten;
      (append-only) actualization only ever appends (forward), never edits the past;
      (forgetting=~P4) a step that changes a past entry is NOT an append = un-actualization = a P4-violation.
    So recording is NOT bedrock; it reduces to P4 read as irreversible content-accumulation.  (Residual: the
    strong reading enriches the bare Level=count formalization; the entropy=count proxy still stands.) *)
Theorem recording_from_p4 :
  (forall a c, exists s, actualize a c = a ++ s)
  /\ (forall a c, a <> [] -> hd_error (actualize a c) = hd_error a)
  /\ (forall a c, actualize a c = a ++ [c])
  /\ (~ (exists s, [false] = [true] ++ s)).
Proof.
  split; [ exact actualize_conserves_past | ].
  split; [ exact actualize_keeps_oldest | ].
  split; [ exact actualize_only_appends | exact forgetting_not_actualization ].
Qed.
