(** * BinarityVsTotality.v — L3 split: binarity is a theorem, totality is the axiom

    Splitting the Law of Excluded Middle into its two theses:

    * BINARITY  — "no third option": the value-space of every distinction
      has exactly two cells. Constructively PROVABLE — no axiom. This is
      the law derivable from the act of distinction itself (co-definition
      of the sides + exclusivity, i.e. L1 + L2).

    * TOTALITY  — "the assignment has always already happened": every
      proposition already HAS one of the two values. NOT provable; this
      is precisely the axiom `classic` (imported from Distinction.v, the
      single canonical source — no re-declaration here). The formal
      status of the potential layer («может быть, но нет») is: a
      distinction whose assignment is pending.

    E/R/R structure:
      Elements: the two sides (P, ~P); the pending act; the completed
                act (canonical Distinction); the assignment witness.
      Roles:    positive / negative — roles of the sides (canonical);
                NEW role: the assignment as a position of its own —
                `exhaustive` is not a structural constant but the RECORD
                OF AN EVENT (actualization).
      Rules:    co-definition (L1: p_codef), exclusion (L2, constructive),
                binarity of the value-space (THEOREMS, axiom-free: a
                third region is refutable already for a pending act),
                `actualize` — the transition rule pending -> completed
                (consumes a witness), totality (`classic`) — the single
                ACCEPTED rule: every assignment already available — a
                counting regime, not a world-thesis (its eternalist
                reading is refuted in TotalityNow.v).
      P4 check: binarity is forced by co-definition — could not be
                otherwise (pure CIC). Totality is NOT forced (Kripke
                models of CIC where it fails witness independence) —
                a named door, not a wall painted to look structural.

    Resolution of the dual-status question for L3:
      L3-as-binarity  — derived  (Qed, closed under global context);
      L3-as-totality  — posited  (Axiom classic, one door);
      what separates them is the act of assignment.

    Bridge to the canon: `pending_of` is the axiom-free twin of
    `distinction_of`; `distinction_of P = actualize (pending_of P)
    (classic P)` holds by reflexivity — the axiom enters the canonical
    constructor EXACTLY at the assignment argument, nowhere else.

    STATUS: 9 Qed, 0 Admitted, 0 new axioms (totality half rests on the
    central `classic` from foundation/Distinction.v only)
    Author: Horsocrates | Date: July 2026
*)

From ToS Require Import foundation.Distinction.

(* ========================================================================= *)
(*  1. Binarity of the value-space: once a status is assigned, it is one     *)
(*     of exactly two. No third value exists to assign.                      *)
(* ========================================================================= *)

Inductive Side : Type := Pos | Neg.

Theorem side_binarity : forall s : Side, s = Pos \/ s = Neg.
Proof. intro s. destruct s; [ left | right ]; reflexivity. Qed.

(* ========================================================================= *)
(*  2. Binarity for propositions: it is IMPOSSIBLE that neither P nor ~P     *)
(*     holds. Double-negated excluded middle is an intuitionistic theorem    *)
(*     (Brouwer himself proved this form): the third status is refutable —   *)
(*     while the availability of the assignment is not thereby asserted.    *)
(*     This is the exact formal content of «нет третьей опции».              *)
(* ========================================================================= *)

Theorem L3_binarity : forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  intros P H.
  apply H. right. intro p.
  apply H. left. exact p.
Qed.

(* ========================================================================= *)
(*  3. For comparison: L2 (non-contradiction) — also axiom-free. Note the    *)
(*     asymmetry: L2 needs nothing; L3-as-totality (below) needs a           *)
(*     postulate. This asymmetry IS the whole dispute.                       *)
(* ========================================================================= *)

Theorem L2_constructive : forall P : Prop, ~ (P /\ ~ P).
Proof. intros P [p np]. exact (np p). Qed.

(* ========================================================================= *)
(*  4. The pending act: two sides co-defined and exclusive — but no          *)
(*     assignment yet. The formal type of the potential layer,               *)
(*     «может быть, но нет».                                                 *)
(* ========================================================================= *)

Record PendingDistinction := mkPending {
  p_pos       : Prop;
  p_neg       : Prop;
  p_codef     : p_neg <-> ~ p_pos;               (* co-definition (L1) *)
  p_exclusive : ~ (p_pos /\ p_neg)               (* L2, built in       *)
}.

(** Binarity holds already for a PENDING act: a third region is
    impossible even before assignment. *)

Theorem pending_binarity :
  forall D : PendingDistinction, ~ ~ (p_pos D \/ p_neg D).
Proof.
  intros D H.
  apply H. right. apply (proj2 (p_codef D)). intro p.
  apply H. left. exact p.
Qed.

(** The axiom-free twin of the canonical `distinction_of`: any Prop
    yields a PENDING distinction with no axiom at all — compare
    Distinction.v, where `distinction_of` must consume `classic` to
    fill the `exhaustive` field. *)

Definition pending_of (P : Prop) : PendingDistinction :=
  mkPending P (~ P)
    (iff_refl (~ P))
    (fun H => match H with conj p np => np p end).

(* ========================================================================= *)
(*  5. The completed act IS the canonical Distinction (Distinction.v):       *)
(*     `exhaustive` read correctly is not a structural constant — it is      *)
(*     the RECORD OF AN EVENT: the act of actualization. `actualize` is      *)
(*     literally the function carrying a pending act plus a witness into     *)
(*     a completed one. D(K) grows by applications of `actualize`.           *)
(* ========================================================================= *)

Definition actualize
  (D : PendingDistinction)
  (assignment : p_pos D \/ p_neg D) : Distinction :=
  mkDistinction (p_pos D) (p_neg D) (p_exclusive D) assignment.

(** Actualization preserves the sides — the event adds the assignment,
    it does not touch the roles. *)

Theorem actualize_sides :
  forall (D : PendingDistinction) (a : p_pos D \/ p_neg D),
    positive (actualize D a) = p_pos D /\ negative (actualize D a) = p_neg D.
Proof. intros D a. split; reflexivity. Qed.

(** Completed acts satisfy the strong disjunction — trivially, by
    projection of the recorded assignment. Uncontested by anyone,
    Brouwer included. *)

Theorem L3_completed :
  forall C : Distinction, positive C \/ negative C.
Proof. intro C. exact (exhaustive C). Qed.

(* ========================================================================= *)
(*  6. TOTALITY — the accepted counting regime, stated as what it is:        *)
(*     every proposition's assignment is already available; every pending    *)
(*     act already completable, no witness supplied. Does not follow from    *)
(*     anything above — and its eternalist ontological reading («every       *)
(*     potential is already secretly answered») is REFUTED in the sister     *)
(*     file TotalityNow.v: potential can expire unrealized (the apples       *)
(*     rot); totality is a predicate of the current actual slice, never      *)
(*     of the future. What `classic` accepts is a regime of reckoning,       *)
(*     not a thesis about the world.                                         *)
(*     We do NOT declare a fifth copy of the axiom:                          *)
(*     `classic` is imported from Distinction.v, its single canonical        *)
(*     home in the foundation layer.                                         *)
(* ========================================================================= *)

Definition decided (P : Prop) : Prop := P \/ ~ P.

(** Totality restated: `classic` says exactly that every P is decided. *)

Lemma classic_decides : forall P : Prop, decided P.
Proof. exact classic. Qed.

(** Totality closes every pending act at once: *)

Theorem totality_completes :
  forall D : PendingDistinction,
    exists C : Distinction,
      positive C = p_pos D /\ negative C = p_neg D.
Proof.
  intro D.
  destruct (classic (p_pos D)) as [yes | no].
  - exists (actualize D (or_introl yes)). split; reflexivity.
  - exists (actualize D (or_intror (proj2 (p_codef D) no))).
    split; reflexivity.
Qed.

(** The bridge, by pure conversion: the canonical `distinction_of` IS
    the actualization of the axiom-free pending act by totality. The
    axiom enters at the assignment argument and nowhere else. *)

Theorem distinction_of_is_actualization :
  forall P : Prop, distinction_of P = actualize (pending_of P) (classic P).
Proof. intro P. reflexivity. Qed.

(* ========================================================================= *)
(*  Summary of the split:                                                    *)
(*                                                                           *)
(*    side_binarity, L3_binarity, pending_binarity  — theorems, free.        *)
(*      («опции всегда бинарны — третьего не дано»)                          *)
(*    L2_constructive, actualize_sides, L3_completed — theorems, free.       *)
(*      (completed acts are assigned — by definition of completion)          *)
(*    classic_decides, totality_completes,                                   *)
(*    distinction_of_is_actualization               — rest on `classic`.     *)
(*      («назначение всегда уже доступно» — accepted counting regime,       *)
(*       NOT a world-thesis: its eternalist reading is refuted in            *)
(*       TotalityNow.v; the price of case-splits on undecided propositions)  *)
(*                                                                           *)
(*  Both sides of the dispute are right: binarity is derivable,              *)
(*  totality is an axiom. What separates them is the act of assignment.      *)
(* ========================================================================= *)

Print Assumptions side_binarity.
Print Assumptions L3_binarity.
Print Assumptions pending_binarity.
Print Assumptions pending_of.
Print Assumptions totality_completes.
Print Assumptions distinction_of_is_actualization.
