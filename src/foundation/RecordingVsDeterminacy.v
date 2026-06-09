(** * RecordingVsDeterminacy.v — digging R2 (the residual reading of LandauerFromP4.v), and the E/R/R
       analysis REFUTES the reduction: R2 conflated two distinct things, and once separated, Landauer does
       NOT reduce to P4.

    R2 was: "P4-determinacy (the past is a fixed fact) => the unchosen branch is RETAINED as a record".
    The analysis splits this into TWO distinct notions:
      - METAPHYSICAL DETERMINACY: there IS a fact that A was chosen (P4: the past is fixed).  About reality.
      - PHYSICAL RECORDING:        the PRESENT state ENCODES that A was chosen (the Landauer-relevant bit).
    These are NOT the same: a determinate past choice can be UNRECORDED (erased without trace) -- it is still
    a definite fact that it happened, yet nothing in the present encodes it.  P4-irreversibility ("can't go
    back") and P4-fixity ("the fact is unchangeable") hold whether or not there is a record (there is nothing
    to "go back" to either way; the fact is fixed regardless of encoding).

    THEREFORE (the refutation): the entropy cost attaches to RECORDING, not to determinacy; P4 supplies only
    the FACT, not the physical encoding.  A determinate-but-unrecorded past has ZERO cost.  So P4 does NOT
    supply the Landauer floor's positivity -- RECORDING does, and recording is a SEPARATE principle
    (information physically encoded; in physics it follows from micro-reversibility, which P4 does not give).
    Landauer does NOT reduce to P4 -- it IS the recording principle.  This CORRECTS LandauerFromP4.v's
    "reduction modulo R2": R2 was the genuine import, not a derivable reading.

    HONEST NET RESULT for the arrow analysis (sharpened, not weakened):
      direction      = FORCED (P4) ;
      alignment      = DERIVED (given actualization = recording) ;
      sign-side      = REDUCED to the origin (A=exists + P4, ArrowSignFromOrigin.v) ;
      floor VALUE    = binarity (L2) ;
      floor POSITIVITY = RECORDING (info physically encoded) -- a genuine SEPARATE input, NOT P4 ;
      "entropy"      = the distinction-count proxy (the unit bridge).
    So the arrow's irreducible imports are exactly: RECORDING + the entropy=count bridge.  Everything else
    is P4 + L2 + origin.  This is the honest floor of the whole analysis.

    Elements: the past choice (a definite bool = the fact) ; the present record (option bool = encoded or not).
    Roles:    determinacy = the choice is a definite fact (P4) ; recording = the present encodes it (Landauer).
    Rules:    P4 => determinate ; determinacy does NOT entail recording ; cost <= recording (not determinacy).

    ============ E/R/R разбор ============
      Elements (L1): прошлый выбор (определённый bool = факт); запись в настоящем (option bool = закодировано или нет).
      Roles    (L4): определённость = выбор есть определённый факт (P4); запись = настоящее кодирует его (Ландауэр).
      Rules    (L5): P4 => определённость; определённость НЕ влечёт запись; стоимость <= запись (не определённость).
      ДИАГНОСТИКА (P4): анализ R2 ОПРОВЕРГАЕТ редукцию — P4 даёт ФАКТ, не физическую ЗАПИСЬ; определённое-но-
      незаписанное прошлое стоит 0. Положительность ландауэровского пола поставляет ЗАПИСЬ (информация физически
      закодирована — отдельный принцип, в физике из микрообратимости, которой у P4 нет), НЕ P4. Ландауэр НЕ
      сводится к P4 — он ЕСТЬ принцип записи. КОРРЕКЦИЯ LandauerFromP4 (R2 = настоящий импорт, не выводимое чтение).
      Уровень: `честная коррекция / точная локализация настоящего импорта`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  The two notions: determinacy (P4) vs recording (Landauer)             *)
(* ===================================================================== *)

(** METAPHYSICAL DETERMINACY (P4): the past choice is a definite fact (a definite bool). *)
Definition determinate (c : bool) : Prop := c = true \/ c = false.

(** PHYSICAL RECORDING: the present state encodes the choice (Some b) or has erased it (None). *)
Definition recorded (r : option bool) : Prop := exists b, r = Some b.

(** The Landauer entropy cost is carried by the physical RECORD, not by the metaphysical fact. *)
Definition entropy_cost (r : option bool) : nat :=
  match r with Some _ => 1 | None => 0 end.

(* ===================================================================== *)
(*  P4 gives determinacy; determinacy does NOT give recording             *)
(* ===================================================================== *)

(** * P4: every past choice is a definite fact (determinacy). *)
Theorem p4_gives_determinacy : forall c, determinate c.
Proof. intro c. unfold determinate. destruct c; [ left | right ]; reflexivity. Qed.

(** * ...but determinacy does NOT entail recording: a determinate choice can be erased (None). *)
Theorem determinacy_not_recording : exists c r, determinate c /\ ~ recorded r.
Proof.
  exists true, None. split.
  - left; reflexivity.
  - intros [b H]; discriminate H.
Qed.

(* ===================================================================== *)
(*  The entropy cost attaches to RECORDING, not determinacy               *)
(* ===================================================================== *)

(** A determinate-but-unrecorded past is FREE -- the cost is not from the fact. *)
Theorem unrecorded_is_free : entropy_cost None = 0.
Proof. reflexivity. Qed.

(** * Positive cost REQUIRES a physical record (not mere determinacy). *)
Theorem cost_requires_recording : forall r, 0 < entropy_cost r -> recorded r.
Proof.
  intros r H. destruct r as [b|].
  - exists b. reflexivity.
  - simpl in H. exfalso. lia.
Qed.

(** * So P4-determinacy alone does NOT force the Landauer cost: a determinate, unrecorded past costs 0. *)
Theorem determinacy_does_not_force_cost :
  exists c r, determinate c /\ ~ recorded r /\ entropy_cost r = 0.
Proof.
  exists true, None. split.
  - left; reflexivity.
  - split; [ intros [b H]; discriminate H | reflexivity ].
Qed.

(* ===================================================================== *)
(*  CAPSTONE — Landauer = recording, NOT P4 (R2 was a conflation)          *)
(* ===================================================================== *)

(** Digging R2 refutes the reduction: separated, P4 gives only the FACT (determinacy); the entropy cost is
    carried by RECORDING (the present encodes the fact), a SEPARATE principle:
      (P4 fact)     every past choice is determinate;
      (not record)  but a determinate choice can be unrecorded;
      (free)        an unrecorded (erased) past costs 0;
      (needs record) positive cost requires a physical record;
      (P4 not enough) so a determinate-but-unrecorded past costs 0 -- P4 alone does NOT force the floor.
    Landauer does NOT reduce to P4 -- it IS the recording principle (information physically encoded), which
    P4's metaphysical determinacy does not supply.  This corrects LandauerFromP4.v: R2 was the real import. *)
Theorem landauer_is_recording_not_p4 :
  (forall c, determinate c)
  /\ (exists c r, determinate c /\ ~ recorded r)
  /\ (entropy_cost None = 0)
  /\ (forall r, 0 < entropy_cost r -> recorded r)
  /\ (exists c r, determinate c /\ ~ recorded r /\ entropy_cost r = 0).
Proof.
  split; [ exact p4_gives_determinacy | ].
  split; [ exact determinacy_not_recording | ].
  split; [ reflexivity | ].
  split; [ exact cost_requires_recording | ].
  exact determinacy_does_not_force_cost.
Qed.
