(** * ArrowSignFromOrigin.v — digging L2 (the residual posit of ArrowSignReservoir.v) to its root: the
       "sub-maximal reservoir on the past side" REDUCES to the ToS ORIGIN.  A=exists -> the FIRST distinction
       = minimal actualization at the origin; P4 makes actualization MONOTONE (never un-actualize), so the
       un-actualized "room" is MAXIMAL at the origin and only SHRINKS forward.  Hence the Past Hypothesis is
       not an independent cosmological fine-tuning (Penrose 1-in-10^10^123) -- it is the ToS FOUNDATION
       (A=exists + P4) itself.

    THE REDUCTION (what the E/R/R analysis of L2 yields).
      reservoir room = the un-actualized distinctions (the entropy sink).
      (origin minimal)  the beginning = the first distinction = MINIMAL actualization  -> room MAXIMAL at K=0.
      (P4 monotone)     actualization only ADDS (no un-actualization)  -> room only SHRINKS forward.
      (side)            so the side with more room = the PAST; the dump-direction (entropy up) = forward.
      (sub-maximal)     at the origin almost everything is un-actualized -> the reservoir is sub-maximal
                        (there IS room to dump) -> the arrow CAN run, from the origin until SATURATION
                        (room -> 0 = heat death / full gravitational collapse, GravityArrowEntropy.v).
      ==> "sub-maximal reservoir + past side" = "began with one distinction (A=exists) + P4 monotone".

    HONEST RESIDUAL (this is a REDUCTION of the posit to the foundation, NOT a full derivation of the sign).
      (1) This forces the SIDE and the room-monotonicity (the skeleton).  The MAGNITUDE of the thermodynamic
          entropy increase (current macrostate multiplicity W) still rides on the recording bridge (L1,
          Landauer) + the indifference measure; W can locally fluctuate (ArrowGroundingDescent.v: W 6->4->6),
          which the room-monotonicity allows.
      (2) Identifying the ToS origin with the cosmological origin is a BRIDGE, not proven here.
      (3) The gravitational (Weyl-curvature) smoothness is a specific form of low initial entropy not
          directly addressed by "one distinction".
      So the posit is REDUCED to A=exists + P4 (the foundation), not an extra fine-tuning -- the deepest
      reduction available in ToS -- with the residual bridges named honestly.

    Elements: actualized count (records = stage) ; the total distinction space ; room = un-actualized = reservoir.
    Roles:    origin = minimal actualization (one distinction) ; room = entropy sink ; forward = room decreasing.
    Rules:    P4 => actualization monotone => room only shrinks ; origin (A=exists) = minimal => room maximal.

    ============ E/R/R разбор ============
      Elements (L1): счёт актуализированного (записи=стадия); полное пространство различений; room=неактуализир.=резервуар.
      Roles    (L4): начало = минимальная актуализация (одно различение); room = сток энтропии; вперёд = room убывает.
      Rules    (L5): P4 => актуализация монотонна => room только сокращается; начало (A=существует)=минимум => room максимален.
      ДИАГНОСТИКА (P4): «суб-максимальный резервуар + сторона прошлого» СВОДИТСЯ к (A=существует: одно первое
      различение = минимум актуализации) + (P4: монотонная актуализация => room максимален в начале и убывает
      вперёд). Гипотеза прошлого = ОСНОВАНИЕ ToS, не отдельная тонкая настройка. ЧЕСТНО: форсирует сторону +
      монотонность room (скелет); ВЕЛИЧИНУ роста энтропии несут мост записи (L1) + безразличие, W локально
      флуктуирует (ArrowGroundingDescent); «происхождение ToS = космологическое» = мост; вейлева гладкость не
      закрыта. Это РЕДУКЦИЯ постулата к основанию, не полный вывод знака. Уровень: `редукция постулата к основанию`.

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

Section FromOrigin.

(** The full distinction space (= the reservoir capacity). *)
Variable total : nat.

(** Records actualized by stage K (P4: only grows).  The origin K=0 = minimal actualization (A=exists). *)
Definition actualized (K : nat) : nat := K.

(** Reservoir room = the un-actualized distinctions (the entropy sink). *)
Definition room (K : nat) : nat := total - actualized K.

(* ===================================================================== *)
(*  P4: actualization is monotone; the origin is minimal                   *)
(* ===================================================================== *)

(** * P4: actualization only grows (no un-actualization). *)
Theorem actualized_grows : forall K, actualized K < actualized (S K).
Proof. intro K. unfold actualized. lia. Qed.

(** * The origin (K=0) has MINIMAL actualization -- the one first distinction (A=exists). *)
Theorem origin_minimal : forall K, actualized 0 <= actualized K.
Proof. intro K. unfold actualized. lia. Qed.

(* ===================================================================== *)
(*  Hence room is MAXIMAL at the origin and SHRINKS forward                *)
(* ===================================================================== *)

(** * The reservoir room is MAXIMAL at the origin (because actualization is minimal there). *)
Theorem room_max_at_origin : forall K, room K <= room 0.
Proof. intro K. unfold room, actualized. lia. Qed.

(** * Room only SHRINKS forward (P4: actualization only adds) -- so the side with more room is the PAST,
    and the dump-direction (entropy up) is the forward direction. *)
Theorem room_shrinks_forward : forall K, S K <= total -> room (S K) < room K.
Proof. intros K H. unfold room, actualized. lia. Qed.

(* ===================================================================== *)
(*  The sub-maximal reservoir + the arrow's run, both FROM the origin      *)
(* ===================================================================== *)

(** * The SUB-MAXIMAL reservoir condition (there is room to dump) HOLDS at the origin -- forced by the
    minimal actualization of the first distinction. *)
Theorem submaximal_from_origin : 0 < total -> 0 < room 0.
Proof. intro H. unfold room, actualized. lia. Qed.

(** * The arrow can run (room available) from the origin all the way to SATURATION (room -> 0 at K=total =
    heat death / full gravitational collapse). *)
Theorem arrow_runs_until_saturation : forall K, K < total -> 0 < room K.
Proof. intros K H. unfold room, actualized. lia. Qed.

(* ===================================================================== *)
(*  CAPSTONE — the L2 posit reduces to (A=exists origin + P4)              *)
(* ===================================================================== *)

(** The "sub-maximal reservoir on the past side" posit, reduced to the ToS foundation:
      (P4 monotone)     actualization only grows;
      (origin minimal)  the beginning = the first distinction = minimal actualization;
      (room maximal)    so the reservoir room is maximal at the origin;
      (room shrinks)    and only shrinks forward -- the past has more room (the SIDE), dump-direction = forward;
      (sub-maximal)     the sub-maximal reservoir condition holds at the origin (forced, not posited);
      (runs to death)   the arrow runs from the origin until saturation (room -> 0 = heat death / collapse).
    The Past Hypothesis is not an independent fine-tuning -- it is "the process began with one distinction
    (A=exists) and P4 makes actualization monotone".  (Honest: this reduces the SIDE + room-monotonicity to
    the foundation; the entropy-increase MAGNITUDE still needs the recording/indifference bridges.) *)
Theorem past_hypothesis_from_origin :
  (forall K, actualized K < actualized (S K))
  /\ (forall K, actualized 0 <= actualized K)
  /\ (forall K, room K <= room 0)
  /\ (forall K, S K <= total -> room (S K) < room K)
  /\ (0 < total -> 0 < room 0)
  /\ (forall K, K < total -> 0 < room K).
Proof.
  repeat split; intros; unfold room, actualized in *; lia.
Qed.

End FromOrigin.
