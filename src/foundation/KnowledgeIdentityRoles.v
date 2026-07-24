(** * KnowledgeIdentityRoles.v — Identity Through Change: Characteristics as Roles (ToS System)

    Formalizes the adjudicated identity thread (working journal TZh-1..TZh-4,
    2026-07-21, Knigi/Logika/00): characteristics of A read as ROLES of the
    system A — critical characteristic = necessary role (must be filled while
    A exists), additional = permitted role (filling contingent), form =
    ELEMENT occupying the role; the modal square realized on role statuses;
    the empty cell (a critical characteristic mutable in its essence) as an
    impossible construction — change of a necessary role is not a change of
    A but another A; and the four aspects of identity (Ship of Theseus,
    AR vol. 2 ch. 11) as four criteria over one substrate — machine-checked
    Hobbes table: no contradiction, different answers to different questions;
    identity of a process held by its constitution while elements flow.

    Elements: fillings (element per role — the form); ships (substrate with
              planks, shape, history, recognition); moments of time.
    Roles:    role statuses of a constitution (necessary / permitted /
              forbidden); four identity criteria (material / structural /
              functional / conceptual); modal layers on role statuses.
    Rules:    well-manifestedness (necessary filled, forbidden empty);
              same A = same constitution; essence always manifest while A
              exists; potential status only for permitted roles; change of
              a necessary role = other A (never an alteration of the same);
              verdict of "the same?" depends on the criterion — the question
              is incomplete until the criterion is named.
    Status:   all proved; self-contained (no ToS imports).
    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: July 2026
*)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(* ================================================================ *)
(** ** 1. Constitution: characteristics as roles                     *)
(* ================================================================ *)

Inductive RoleStatus : Type := RNecessary | RPermitted | RForbidden.

(** The constitution of A: which role carries which status. This is
    the criterion — what makes A = A. *)
Definition Constitution : Type := nat -> RoleStatus.

(** A manifestation: which element (the FORM) occupies which role. *)
Definition Filling : Type := nat -> option nat.

(** Well-manifested A: every necessary role is filled; no forbidden
    role is filled. Permitted roles are free either way. *)
Definition well_manifested (c : Constitution) (f : Filling) : Prop :=
  forall r, (c r = RNecessary -> exists e, f r = Some e)
         /\ (c r = RForbidden  -> f r = None).

(** Same A = same constitution (identity of the criterion). *)
Definition same_A (c1 c2 : Constitution) : Prop := forall r, c1 r = c2 r.

Lemma same_A_refl : forall c, same_A c c.
Proof. intros c r. reflexivity. Qed.

(** The essence is always manifest while A exists: a necessary role
    cannot stand empty (TZh-V3). *)
Theorem essence_always_manifest : forall c f r,
  well_manifested c f -> c r = RNecessary -> exists e, f r = Some e.
Proof. intros c f r W H. destruct (W r) as [Hn _]. exact (Hn H). Qed.

(* ---------------- a concrete A: the "human" example ---------------- *)

(** Role 0 — necessary (what lets A exist); role 1 — permitted
    (a limb: may be present or absent); the rest — forbidden. *)
Definition human_c : Constitution :=
  fun r => match r with
           | 0 => RNecessary
           | 1 => RPermitted
           | _ => RForbidden
           end.

Definition f_full : Filling :=
  fun r => match r with 0 => Some 10 | 1 => Some 20 | _ => None end.

Definition f_sparse : Filling :=
  fun r => match r with 0 => Some 11 | _ => None end.

Lemma human_full_wm : well_manifested human_c f_full.
Proof.
  intros r. split; intros H.
  - destruct r as [|[|r']]; simpl in H;
      [exists 10; reflexivity | discriminate | discriminate].
  - destruct r as [|[|r']]; simpl in H;
      [discriminate | discriminate | reflexivity].
Qed.

Lemma human_sparse_wm : well_manifested human_c f_sparse.
Proof.
  intros r. split; intros H.
  - destruct r as [|[|r']]; simpl in H;
      [exists 11; reflexivity | discriminate | discriminate].
  - destruct r as [|[|r']]; simpl in H;
      [discriminate | discriminate | reflexivity].
Qed.

(** A permitted role may stand empty — the additional characteristic
    in the unmanifested status ("may be, but is not"). *)
Theorem permitted_may_be_empty :
  well_manifested human_c f_sparse /\
  human_c 1 = RPermitted /\ f_sparse 1 = None.
Proof. split; [apply human_sparse_wm | split; reflexivity]. Qed.

(** The same permitted role may be filled — manifestation differs,
    A stays A. *)
Theorem permitted_may_be_filled :
  well_manifested human_c f_full /\
  human_c 1 = RPermitted /\ f_full 1 = Some 20.
Proof. split; [apply human_full_wm | split; reflexivity]. Qed.

(** A1 -> A2: elements change (10 -> 11), the permitted role empties,
    the constitution is untouched — identity stands. *)
Theorem manifestation_varies_identity_stands :
  same_A human_c human_c /\
  f_full 0 = Some 10 /\ f_sparse 0 = Some 11 /\
  well_manifested human_c f_full /\ well_manifested human_c f_sparse.
Proof.
  split; [apply same_A_refl | split; [reflexivity | split;
    [reflexivity | split; [apply human_full_wm | apply human_sparse_wm]]]].
Qed.

(* ---------------- the empty cell ---------------- *)

(** "The same A with role 0 no longer necessary" — a different
    constitution. *)
Definition other_c : Constitution :=
  fun r => match r with
           | 0 => RPermitted
           | 1 => RPermitted
           | _ => RForbidden
           end.

Theorem change_necessary_is_other_A : ~ same_A human_c other_c.
Proof. intros H. specialize (H 0). simpl in H. discriminate. Qed.

(** The empty cell in general: a critical characteristic mutable in
    its essence is impossible — changing the status of a necessary
    role yields ANOTHER A, never an altered same A (TZh-V2). *)
Theorem critical_mutable_impossible : forall c1 c2 r,
  c1 r = RNecessary -> c2 r <> RNecessary -> ~ same_A c1 c2.
Proof.
  intros c1 c2 r H1 H2 Hs. apply H2. rewrite <- (Hs r). exact H1.
Qed.

(* ================================================================ *)
(** ** 2. The modal square on role statuses (TZh-V7)                 *)
(* ================================================================ *)

Inductive Layer : Type := LNecessary | LActual | LPotential | LImpossible.

Definition layer_of (s : RoleStatus) (fill : option nat) : Layer :=
  match s, fill with
  | RNecessary, _      => LNecessary
  | RPermitted, Some _ => LActual
  | RPermitted, None   => LPotential
  | RForbidden, _      => LImpossible
  end.

(** All four layers realized on the constitution of one system. *)
Theorem square_covered :
  layer_of RNecessary (Some 0) = LNecessary /\
  layer_of RPermitted (Some 0) = LActual /\
  layer_of RPermitted None     = LPotential /\
  layer_of RForbidden None     = LImpossible.
Proof. repeat split; reflexivity. Qed.

(** A forbidden role is never manifest in a well-manifested A. *)
Theorem forbidden_never_manifest : forall c f r,
  well_manifested c f -> c r = RForbidden -> f r = None.
Proof. intros c f r W H. destruct (W r) as [_ Hf]. exact (Hf H). Qed.

(** The essence sits in the necessary layer whatever its form. *)
Theorem essence_layer_stable : forall fill,
  layer_of RNecessary fill = LNecessary.
Proof. intros [e|]; reflexivity. Qed.

(* ================================================================ *)
(** ** 3. Four aspects over one substrate: the Hobbes table          *)
(* ================================================================ *)

Fixpoint list_nat_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && list_nat_eqb xs ys
  | _, _ => false
  end.

Record Ship : Type := mkShip {
  planks     : list nat;  (** material: the elements *)
  shape      : nat;       (** structural: the organization *)
  continuous : bool;      (** functional: unbroken history of role-filling *)
  recognized : bool       (** conceptual: status granted by witnesses *)
}.

Definition material_same   (a b : Ship) : bool := list_nat_eqb (planks a) (planks b).
Definition structural_same (a b : Ship) : bool := Nat.eqb (shape a) (shape b).
Definition functional_same (a b : Ship) : bool := Bool.eqb (continuous a) (continuous b).
Definition conceptual_same (a b : Ship) : bool := Bool.eqb (recognized a) (recognized b).

Definition original   : Ship := mkShip [1; 2; 3] 0 true  true.
Definition maintained : Ship := mkShip [4; 5; 6] 0 true  true.
Definition rebuilt    : Ship := mkShip [1; 2; 3] 0 false false.

(** The Hobbes table, machine-checked: the maintained ship is the same
    functionally and conceptually, the rebuilt one — materially; both
    are the same structurally. No contradiction: different answers to
    different questions. *)
Theorem hobbes_table :
  material_same   original maintained = false /\
  material_same   original rebuilt    = true  /\
  structural_same original maintained = true  /\
  structural_same original rebuilt    = true  /\
  functional_same original maintained = true  /\
  functional_same original rebuilt    = false /\
  conceptual_same original maintained = true  /\
  conceptual_same original rebuilt    = false.
Proof. repeat split; reflexivity. Qed.

(** "The same?" is incomplete until the criterion is named: the
    verdict on one and the same pair depends on the criterion. *)
Theorem verdict_depends_on_criterion :
  material_same original rebuilt <> functional_same original rebuilt.
Proof. intros H. discriminate H. Qed.

(* ---------------- identity as process ---------------- *)

(** The maintained ship through time: elements flow, the constitution
    (shape, continuous role-filling) stands — the identity of a
    process is held by its rule, not by its states. *)
Definition ship_at (t : nat) : Ship :=
  mkShip [t + 1; t + 2; t + 3] 0 true true.

Theorem process_identity : forall t,
  structural_same (ship_at t) (ship_at 0) = true /\
  functional_same (ship_at t) (ship_at 0) = true.
Proof. intros t. split; reflexivity. Qed.

Theorem elements_flow : material_same (ship_at 1) (ship_at 0) = false.
Proof. reflexivity. Qed.

(* ================================================================ *)
(** ** 4. Registry entry: change of essence passed off as alteration *)
(* ================================================================ *)

(** "The same A, just changed in its essence" — the substitution: a
    different criterion means a different A; there is a role where the
    constitutions disagree, and identity fails. *)
Theorem essence_change_is_other_A :
  ~ same_A human_c other_c /\ (exists r, human_c r <> other_c r).
Proof.
  split; [exact change_necessary_is_other_A |].
  exists 0. simpl. discriminate.
Qed.
