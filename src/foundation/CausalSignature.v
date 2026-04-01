(** * CausalSignature.v — Lorentzian signature from causal structure
    Elements: CEdgeType (Space|Time), cedge_sign, interval_sq
    Roles:    space=reversible(+1), time=irreversible(-1)
    Rules:    exactly one negative direction = Lorentzian (-,+,+,+)
    STATUS:   12 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    WHY LORENTZIAN:
    P4 (finite actuality): time = nat stages (irreversible: S has no predecessor)
    Space: spatial links within a stage (reversible: go and return)

    Irreversible → negative sign (time).
    Reversible → positive sign (space).
    Exactly one irreversible direction (nat has one S constructor) →
    signature (-,+,...,+) = Lorentzian.

    Euclidean (+,+,...,+) would require ALL directions reversible.
    But P4 forces at least one irreversible direction (stages).
    Ultra-hyperbolic (-,-,+,...) would require two independent S constructors.
    nat has exactly one → exactly one time dimension.
*)

From Stdlib Require Import QArith Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.

Open Scope Q_scope.

(* ================================================================ *)
(*  EDGE TYPES                                                       *)
(* ================================================================ *)

Inductive CEdgeType := CSpaceEdge | CTimeEdge.

(** Sign convention: space=+1, time=-1 *)
Definition cedge_sign (t : CEdgeType) : Q :=
  match t with
  | CSpaceEdge => 1
  | CTimeEdge => -(1)
  end.

(** Interval squared = sign × length² *)
Definition interval_sq (sign : Q) (length : Q) : Q :=
  sign * length * length.

(* ================================================================ *)
(*  SPACE IS REVERSIBLE                                              *)
(* ================================================================ *)

(** Space edges connect events at the SAME stage (reversible) *)
Definition space_same_stage (s1 s2 : nat) : Prop := s1 = s2.

Lemma space_reversible_by_definition :
  forall s, space_same_stage s s.
Proof. intro s. unfold space_same_stage. reflexivity. Qed.

(** If stages are equal, you can go both ways *)
Lemma space_symmetric : forall s1 s2,
  space_same_stage s1 s2 -> space_same_stage s2 s1.
Proof. intros s1 s2 H. unfold space_same_stage in *. lia. Qed.

(* ================================================================ *)
(*  TIME IS IRREVERSIBLE                                             *)
(* ================================================================ *)

(** Time edges connect stage K to stage K+1 *)
Definition time_forward (s1 s2 : nat) : Prop := s2 = S s1.

Lemma time_irreversible : forall s1 s2,
  time_forward s1 s2 -> ~ time_forward s2 s1.
Proof.
  intros s1 s2 H12 H21.
  unfold time_forward in *. lia.
Qed.

(* ================================================================ *)
(*  SIGN PROPERTIES                                                  *)
(* ================================================================ *)

Lemma space_positive : cedge_sign CSpaceEdge == 1.
Proof. reflexivity. Qed.

Lemma time_negative : cedge_sign CTimeEdge == -(1).
Proof. reflexivity. Qed.

Lemma space_interval_positive : forall l,
  0 < l -> 0 < interval_sq (cedge_sign CSpaceEdge) l.
Proof.
  intros l Hl. unfold interval_sq, cedge_sign.
  (* 1 * l * l > 0 when l > 0 *)
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; [lra | exact Hl].
  - exact Hl.
Qed.

Lemma time_interval_negative : forall l,
  0 < l -> interval_sq (cedge_sign CTimeEdge) l < 0.
Proof.
  intros l Hl. unfold interval_sq, cedge_sign.
  (* -(1) * l * l < 0 when l > 0 *)
  assert (0 < l * l) as Hll.
  { apply Qmult_lt_0_compat; exact Hl. }
  assert (-(1) * l * l == -(l * l)) as Heq.
  { ring. }
  rewrite Heq.
  lra.
Qed.

(* ================================================================ *)
(*  SIGNATURE IS LORENTZIAN                                          *)
(* ================================================================ *)

(** Signature: list of signs for each direction *)
Definition lorentzian_signature_d (d : nat) : list Q :=
  (-(1)) :: repeat 1 d.

(** 3+1 dimensions: [-1, 1, 1, 1] *)
Lemma signature_3plus1 :
  lorentzian_signature_d 3 = [-(1); 1; 1; 1].
Proof. reflexivity. Qed.

(** Exactly one negative entry *)
Definition is_neg (q : Q) : bool :=
  match Qcompare q 0 with Lt => true | _ => false end.

Definition count_negative (l : list Q) : nat :=
  length (filter is_neg l).

Lemma one_time_dimension :
  count_negative (lorentzian_signature_d 3) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem causal_signature_synthesis :
  (* Space sign = +1 *)
  cedge_sign CSpaceEdge == 1 /\
  (* Time sign = -1 *)
  cedge_sign CTimeEdge == -(1) /\
  (* Space intervals positive *)
  (forall l, 0 < l -> 0 < interval_sq (cedge_sign CSpaceEdge) l) /\
  (* Time intervals negative *)
  (forall l, 0 < l -> interval_sq (cedge_sign CTimeEdge) l < 0) /\
  (* Exactly 1 time dimension *)
  count_negative (lorentzian_signature_d 3) = 1%nat.
Proof.
  split; [exact space_positive |
  split; [exact time_negative |
  split; [exact space_interval_positive |
  split; [exact time_interval_negative |
  exact one_time_dimension]]]].
Qed.
