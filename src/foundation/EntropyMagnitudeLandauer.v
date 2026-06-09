(** * EntropyMagnitudeLandauer.v — the residual #1 of the arrow analysis: the MAGNITUDE of entropy
       production per actualization, via the recording (Landauer) bridge.  HONEST: this is the FIRST file
       of the gravity<->time<->arrow arc that imports a PHYSICS PRINCIPLE (Landauer) as an explicit INPUT,
       not derived from P4.  So the results are CONDITIONAL on Landauer (the hypothesis `1 <= cost`); the
       Coq file is still 0-axiom (Landauer enters as a premise, not an `Axiom`), but conceptually it is an
       imported bridge, not a ToS derivation.

    THE DECOMPOSITION (what is ToS vs what is Landauer).
      (Landauer, INPUT)   irreversible recording of one bit costs >= 1 bit of entropy: `cost >= 1`.  This is
                          the bridge "logical irreversibility => thermodynamic cost"; it CANNOT be derived
                          from pure P4 (that would need the second law) -- it is a named premise here.
      (Binarity L2, ToS)  a distinction is exactly ONE bit (the primal A | ~A), so the minimal cost = 1 bit.
      (Derived, given cost>=1)  entropy grows LINEARLY with the record count (proper time): each actualization
                          adds `cost` bits; entropy increase >= the stage count (1 bit per proper-time tick);
                          and (with the reservoir of ArrowSignFromOrigin.v) this holds WHILE room lasts, then
                          SATURATES (heat death / full collapse).

    THE TIE: entropy increase >= proper time (in bits).  Since proper time = the stage count (the irreversibly
    actualized records, P4) and each record costs >= 1 bit (Landauer + binarity), entropy production is bounded
    BELOW by proper time: dS >= dtau * (1 bit).  The thermodynamic clock cannot run slower than the proper-time
    clock (in bits per stage) -- a quantitative floor linking the two times.

    HONEST SCOPE.  Results are CONDITIONAL on Landauer (`1 <= cost`); this is NOT a derivation of Landauer or
    of the second law.  ToS supplies the UNIT (binarity = 1 bit) and the proper-time tie; Landauer supplies
    that the cost is real/positive.  entropy in BITS = the Element-side count (rigorous = full statistical
    entropy).  The sign/direction were handled in ArrowSignReservoir.v / ArrowSignFromOrigin.v; this file is
    only the per-step MAGNITUDE.

    Elements: cost per actualization (bits) ; entropy (bits) ; stage count (proper time / records).
    Roles:    cost = Landauer floor (entropy per recorded bit) ; value 1 = binarity (L2) ; entropy = records*cost.
    Rules:    Landauer (input) cost>=1 ; binarity cost=1 ; dS = cost per actualization ; S >= S0 + proper_time*cost.

    ============ E/R/R разбор ============
      Elements (L1): стоимость на актуализацию cost (биты); энтропия (биты); счёт стадий (собственное время).
      Roles    (L4): cost = ландауэровский пол (энтропия на бит); значение 1 = бинарность (L2); энтропия = записи*cost.
      Rules    (L5): Ландауэр (ВХОД) cost>=1; бинарность cost=1; dS = cost на актуализацию; S >= S0 + собств_время*cost.
      ДИАГНОСТИКА (P4): Ландауэр — ЯВНЫЙ вход (не выводим из чистого P4); ToS даёт единицу (бинарность) + привязку
      энтропии к собственному времени (dS >= dtau*ln2). Выводимо ПРИ cost>=1: линейность, скорость, пол >= собств.
      время, насыщение. ЧЕСТНО: НЕ вывод Ландауэра/2-го начала; результаты УСЛОВНЫ. Coq 0-аксиомен (Ландауэр =
      гипотеза, не Axiom). Уровень: `вывод-при-явном-входе`.

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only; Landauer = the premise `1 <= cost`)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Proper time, the entropy floor, the binarity unit                      *)
(* ===================================================================== *)

(** Proper time = the stage count = the irreversibly actualized records (P4). *)
Definition stage (K : nat) : nat := K.

(** Entropy floor (in bits): S0 + cost per actualization, accumulated over K stages. *)
Definition min_entropy (cost S0 K : nat) : nat := S0 + cost * K.

(** With a finite reservoir of `room` slots: the floor accumulates only while the reservoir has room. *)
Definition capped_entropy (cost S0 room K : nat) : nat := S0 + cost * Nat.min K room.

(** Binarity (L2): a distinction is exactly one bit, so the minimal Landauer cost is 1 bit. *)
Definition binary_cost : nat := 1.

(** * ToS contribution: binarity fixes the minimal floor at exactly 1 bit. *)
Theorem binarity_minimal_floor : 1 <= binary_cost.
Proof. unfold binary_cost. lia. Qed.

(* ===================================================================== *)
(*  The RATE and the MAGNITUDE (conditional on Landauer: cost >= 1)         *)
(* ===================================================================== *)

(** * RATE: each actualization raises the entropy floor by exactly the per-bit cost. *)
Theorem entropy_rate :
  forall cost S0 K, min_entropy cost S0 (S K) = min_entropy cost S0 K + cost.
Proof. intros cost S0 K. unfold min_entropy. lia. Qed.

(** * Given Landauer (cost >= 1): entropy STRICTLY increases at every actualization. *)
Theorem entropy_strictly_increases :
  forall cost S0 K, 1 <= cost -> min_entropy cost S0 K < min_entropy cost S0 (S K).
Proof. intros cost S0 K H. unfold min_entropy. nia. Qed.

(** * THE TIE (magnitude): entropy increase >= proper time (in bits) -- the thermodynamic clock cannot run
    slower than the proper-time clock; each proper-time tick costs >= 1 bit. *)
Theorem entropy_at_least_proper_time :
  forall cost S0 K, 1 <= cost -> S0 + stage K <= min_entropy cost S0 K.
Proof. intros cost S0 K H. unfold min_entropy, stage. nia. Qed.

(* ===================================================================== *)
(*  Tie to the reservoir (ArrowSignFromOrigin.v): grows while room, then saturates *)
(* ===================================================================== *)

(** * The entropy floor grows (at rate `cost`) WHILE the reservoir is sub-maximal (K < room). *)
Theorem capped_grows_while_room :
  forall cost S0 room K, 1 <= cost -> K < room ->
    capped_entropy cost S0 room K < capped_entropy cost S0 room (S K).
Proof.
  intros cost S0 room K Hc Hr. unfold capped_entropy.
  rewrite (Nat.min_l K room) by lia.
  rewrite (Nat.min_l (S K) room) by lia.
  nia.
Qed.

(** * ...and SATURATES (no further increase) once the reservoir is full (heat death / full collapse). *)
Theorem capped_saturates :
  forall cost S0 room K, room <= K ->
    capped_entropy cost S0 room K = capped_entropy cost S0 room (S K).
Proof.
  intros cost S0 room K H. unfold capped_entropy.
  rewrite (Nat.min_r K room) by lia.
  rewrite (Nat.min_r (S K) room) by lia.
  reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** The per-step MAGNITUDE of entropy production, given the Landauer bridge:
      (binarity)    the minimal floor is exactly 1 bit (a distinction is binary, L2);
      (rate)        each actualization adds `cost` bits to the entropy floor;
      (strict)      given cost >= 1 (Landauer), entropy strictly increases each actualization;
      (tie)         entropy increase >= the proper-time (stage) count -- >= 1 bit per proper-time tick;
      (while room)  the floor grows while the reservoir is sub-maximal ...
      (saturate)    ... and saturates once the reservoir is full.
    ToS supplies the unit (binarity = 1 bit) and the proper-time tie; Landauer supplies cost >= 1 (the input).
    This is a derivation GIVEN the Landauer bridge, NOT a derivation of Landauer or the second law. *)
Theorem entropy_magnitude_landauer :
  (1 <= binary_cost)
  /\ (forall cost S0 K, min_entropy cost S0 (S K) = min_entropy cost S0 K + cost)
  /\ (forall cost S0 K, 1 <= cost -> min_entropy cost S0 K < min_entropy cost S0 (S K))
  /\ (forall cost S0 K, 1 <= cost -> S0 + stage K <= min_entropy cost S0 K)
  /\ (forall cost S0 room K, 1 <= cost -> K < room ->
        capped_entropy cost S0 room K < capped_entropy cost S0 room (S K))
  /\ (forall cost S0 room K, room <= K ->
        capped_entropy cost S0 room K = capped_entropy cost S0 room (S K)).
Proof.
  repeat split.
  - exact binarity_minimal_floor.
  - exact entropy_rate.
  - exact entropy_strictly_increases.
  - exact entropy_at_least_proper_time.
  - exact capped_grows_while_room.
  - exact capped_saturates.
Qed.
