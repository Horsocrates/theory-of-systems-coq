(** * TotalityNow.v — totality is about "now": potential expires, the future is an event

    Formal companion of the adjudicated canon (2026-07-31, T-V1..V4):

    «Может быть, но нет» decomposes along TWO axes:
      - «может быть» — the LOGICAL status of the system: the structure
        permits existence; the permission is CARRIED by present actuals
        (apples carry «juice may be»);
      - «но нет»     — the CURRENT ONTOLOGICAL status: not existent;
        the ZDO-event (act of distinction = execution of sufficient
        ground) changes exactly this axis and only this axis.

    Consequences, each a theorem below:
      1. The axes are independent (permitted without realized;
         realized without still-permitted).
      2. Potential has a LIFETIME: it is carried by its actuals and
         dies with them — it can expire UNREALIZED (the apples rot).
         Hence «может быть» is NOT «будет»: the eternalist reading of
         totality («всякий потенциал уже втайне отвечен — «будет, но
         скрыто»») is REFUTED by a counterexample-theorem.
      3. Totality is a predicate of the ACTUAL sub-field of the current
         step (dichotomy of the present — by construction of the actual
         layer), and is NEVER applicable to the future: the successor
         is not a function of the present — both continuations are
         typable. This openness is the field of freedom of will.

    E/R/R:
      Elements: carriers (apples), products (juice); a state = the
                actual layer of one step.
      Roles:    permitted — the logical axis («может быть»), carried by
                Elements; realized — the ontological axis («но нет /
                и есть»).
      Rules:    Step-events; each constructor carries its ground as a
                hypothesis — ZDO built into the event type: make (the
                operator's act), rot (time extinguishing the carriers),
                stay (nothing left to act on).
      P4 check: potential is a property of the current slice, with a
                lifetime — not a storehouse of hidden future facts;
                the future is event-shaped, not read off the present.

    Sister file: BinarityVsTotality.v (the L3 split; pending/actualize).
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import Bool.

(* ========================================================================= *)
(*  1. The step: a state is the actual layer "now".                          *)
(* ========================================================================= *)

Record State := mkState { apples : bool; juice : bool }.

(** «может быть» — logical axis: the permission is carried by actuals. *)
Definition permitted (s : State) : bool := apples s.

(** «но нет / и есть» — ontological axis: the current assignment. *)
Definition realized (s : State) : bool := juice s.

Definition s0      : State := mkState true  false.  (* apples, no juice  *)
Definition s_juice : State := mkState false true.   (* juice made        *)
Definition s_rot   : State := mkState false false.  (* rotted: both gone *)

(* ========================================================================= *)
(*  2. The two axes are independent: neither reads off the other.            *)
(* ========================================================================= *)

Theorem permitted_without_realized :
  permitted s0 = true /\ realized s0 = false.
Proof. split; reflexivity. Qed.

Theorem realized_without_permission_left :
  realized s_juice = true /\ permitted s_juice = false.
Proof. split; reflexivity. Qed.

(* ========================================================================= *)
(*  3. ZDO-events: every transition carries its ground as a hypothesis of    *)
(*     its constructor. No assignment without ground — by type.              *)
(* ========================================================================= *)

Inductive Step : State -> State -> Prop :=
  | step_make : forall s, apples s = true  -> Step s s_juice
  | step_rot  : forall s, apples s = true  -> Step s (mkState false (juice s))
  | step_stay : forall s, apples s = false -> Step s s.

(* ========================================================================= *)
(*  4. Freedom: from one present, two lawful futures. The successor is not   *)
(*     a function of the present — both continuations are typable and they   *)
(*     differ. This openness is what the field of will holds open.           *)
(* ========================================================================= *)

Theorem freedom_two_continuations :
  Step s0 s_juice /\ Step s0 s_rot /\ s_juice <> s_rot.
Proof.
  split; [ exact (step_make s0 eq_refl) | split ].
  - exact (step_rot s0 eq_refl).
  - intro H. exact (diff_true_false (f_equal juice H)).
Qed.

Theorem future_not_readable :
  exists s s1 s2, Step s s1 /\ Step s s2 /\ s1 <> s2.
Proof.
  exists s0, s_juice, s_rot. exact freedom_two_continuations.
Qed.

(* ========================================================================= *)
(*  5. Two runs from the same present: realization happens on one and        *)
(*     never on the other. The future is an event, not a reading.            *)
(* ========================================================================= *)

Definition make_run (n : nat) : State :=
  match n with O => s0 | S _ => s_juice end.

Definition rot_run (n : nat) : State :=
  match n with O => s0 | S _ => s_rot end.

Lemma make_run_traj : forall n, Step (make_run n) (make_run (S n)).
Proof.
  intro n. destruct n.
  - exact (step_make s0 eq_refl).
  - exact (step_stay s_juice eq_refl).
Qed.

Lemma rot_run_traj : forall n, Step (rot_run n) (rot_run (S n)).
Proof.
  intro n. destruct n.
  - exact (step_rot s0 eq_refl).
  - exact (step_stay s_rot eq_refl).
Qed.

Theorem realization_happens_on_make :
  exists n, realized (make_run n) = true.
Proof. exists 1. reflexivity. Qed.

(** The apples rot: the permission was alive at step 0, realization never
    came, and from step 1 on the permission itself is dead. Potential
    EXPIRES — unrealized. «Потенциал был, реализации не было.» *)

Theorem potential_expires :
  permitted (rot_run 0) = true /\
  (forall n, realized (rot_run n) = false) /\
  (forall n, permitted (rot_run (S n)) = false).
Proof.
  split; [ reflexivity | split ].
  - intro n. destruct n; reflexivity.
  - intro n. reflexivity.
Qed.

(* ========================================================================= *)
(*  6. The eternalist reading refuted: «может быть» does NOT mean «будет,    *)
(*     но скрыто». A lawful run exists on which the permission held and      *)
(*     realization never comes.                                              *)
(* ========================================================================= *)

Definition eternalism : Prop :=
  forall run : nat -> State,
    (forall n, Step (run n) (run (S n))) ->
    permitted (run 0) = true ->
    exists n, realized (run n) = true.

Theorem eternalism_refuted : ~ eternalism.
Proof.
  intro E.
  destruct (E rot_run rot_run_traj eq_refl) as [n Hn].
  destruct n; discriminate Hn.
Qed.

(* ========================================================================= *)
(*  7. Totality is about NOW: the actual sub-field of the current step is    *)
(*     assigned (dichotomy of the present — by construction of the actual    *)
(*     layer), while the future is not a function of the present. The        *)
(*     capstone pair IS the canon: «тотальность всегда о сейчас — и          *)
(*     никогда о будущем».                                                   *)
(* ========================================================================= *)

Theorem totality_now : forall s : State,
  (realized s = true \/ realized s = false) /\
  (permitted s = true \/ permitted s = false).
Proof.
  intro s. split.
  - destruct (realized s); [ left | right ]; reflexivity.
  - destruct (permitted s); [ left | right ]; reflexivity.
Qed.

(** Capstone: now — assigned; future — branching; eternalism — false. *)

Theorem totality_is_about_now :
  (forall s : State, realized s = true \/ realized s = false)
  /\ (exists s s1 s2, Step s s1 /\ Step s s2 /\ s1 <> s2)
  /\ ~ eternalism.
Proof.
  split; [ | split ].
  - intro s. destruct (realized s); [ left | right ]; reflexivity.
  - exact future_not_readable.
  - exact eternalism_refuted.
Qed.

(* HONESTY NOTE: the model is a statement carrier. The bool dichotomy of
   `totality_now` carries «наличное определено» by construction of the
   actual layer — it does not prove the metaphysics; the metaphysical
   weight lives in the adjudicated canon. What the model proves
   irreducibly: independence of the two axes, expiry of unrealized
   potential, non-functionality of the future, and the falsity of
   eternalism within any such step-world.                                *)

Print Assumptions freedom_two_continuations.
Print Assumptions potential_expires.
Print Assumptions eternalism_refuted.
Print Assumptions totality_is_about_now.
