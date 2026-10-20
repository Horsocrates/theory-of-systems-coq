(** * HigmanLemma.v — Higman's lemma for the one-letter alphabet + Dickson's lemma for pairs
    Elements: list embedding (list_le); WQO in the sequential form (is_wqo); right minima
    Roles:    a WQO is an order with no bad infinite sequence; Nat.le is the base WQO;
              a right minimum of f is a position not exceeded by any later value
    Rules:    nat is well-founded => Nat.le is a WQO (constructive, strong induction on the
              first value); one-letter lists embed by length => Higman for the one-letter
              alphabet (constructive, reduces to Nat.le); Dickson for pairs: along the right
              minima of f the sequence g would have to descend forever => needs a minimum over
              an infinite tail, taken classically (classic = L3)
    STATUS:   11 Qed, 0 Admitted; axioms: Classical_Prop.classic only, and only under
              tail_min_exists, right_min_unbounded, dickson_pair, higman_synthesis — the rest
              is closed under the global context (Print Assumptions at the end)
    SCOPE:    Higman's lemma for an ARBITRARY finite alphabet is NOT proved here: only the
              one-letter case (lists of unit), which is Nat.le on lengths.
    REPAIR (2026-10-17): the March version never compiled.  wqo_nat_le, wqo_bool,
              dickson_pair and higman_unit inspected only the first three terms of the
              sequence and, in branches such as f 0 > f 1 > f 2, tried to prove false goals
              (first failure: line 40, "Cannot find witness").  The statements are unchanged;
              the proofs are new.  The file no longer declares its own `classic`: it uses the
              standard Classical_Prop.classic, the one ToS_Axioms.v re-exports.
    Author:   Horsocrates | Date: March 2026 (proofs repaired October 2026)
*)

From Stdlib Require Import List Lia Bool PeanoNat Classical_Prop.
Import ListNotations.

Definition is_wqo {A : Type} (le : A -> A -> Prop) : Prop :=
  forall f : nat -> A, exists i j : nat, (i < j)%nat /\ le (f i) (f j).

Inductive list_le {A} (le : A -> A -> Prop) : list A -> list A -> Prop :=
  | list_le_nil : forall ys, list_le le [] ys
  | list_le_cons : forall x xs y ys,
      le x y -> list_le le xs ys -> list_le le (x :: xs) (y :: ys)
  | list_le_skip : forall xs y ys,
      list_le le xs ys -> list_le le xs (y :: ys).

Lemma list_le_nil_always : forall A (le : A -> A -> Prop) ys,
  list_le le [] ys.
Proof. intros. constructor. Qed.

(* ================================================================= *)
(* NAT.LE IS A WQO (constructive)                                      *)
(* ================================================================= *)

(** Strong induction on the first value: either f 0 <= f 1, or the shifted
    sequence starts strictly lower and the bound drops by one. *)
Lemma wqo_nat_le_bounded : forall m (f : nat -> nat),
  (f 0 <= m)%nat -> exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat.
Proof.
  induction m as [| m IH]; intros f Hm.
  - exists 0, 1. split; lia.
  - destruct (Nat.le_gt_cases (f 0) (f 1)) as [H01 | H10].
    + exists 0, 1. split; [lia | exact H01].
    + destruct (IH (fun n => f (S n))) as [i [j [Hij Hle]]].
      * simpl. lia.
      * exists (S i), (S j). split; [lia | exact Hle].
Qed.

Lemma wqo_nat_le : is_wqo Nat.le.
Proof.
  intro f. exact (wqo_nat_le_bounded (f 0) f (Nat.le_refl _)).
Qed.

(* ================================================================= *)
(* DICKSON PAIR (classic = L3)                                         *)
(* ================================================================= *)

(** A right minimum of f: no later value is smaller. *)
Definition right_min (f : nat -> nat) (n : nat) : Prop :=
  forall m, (n < m)%nat -> (f n <= f m)%nat.

(** Every tail [k, ∞) of f has a position of its minimum value.  The case
    split «is some value of the tail below v?» quantifies over an infinite
    tail, hence classic. *)
Lemma tail_min_exists : forall (f : nat -> nat) (k : nat),
  exists n, (k <= n)%nat /\ forall m, (k <= m)%nat -> (f n <= f m)%nat.
Proof.
  intros f k.
  assert (Hv : forall v, (exists m, (k <= m)%nat /\ (f m <= v)%nat) ->
                 exists n, (k <= n)%nat /\ forall m, (k <= m)%nat -> (f n <= f m)%nat).
  { induction v as [| v IH]; intros [m0 [Hk0 Hm0]].
    - exists m0. split; [exact Hk0 |]. intros m _. lia.
    - destruct (classic (exists m, (k <= m)%nat /\ (f m <= v)%nat)) as [Hex | Hno].
      + exact (IH Hex).
      + exists m0. split; [exact Hk0 |]. intros m Hkm.
        destruct (Nat.le_gt_cases (f m) v) as [Hmv | Hmv].
        * exfalso. apply Hno. exists m. split; [exact Hkm | exact Hmv].
        * lia. }
  apply (Hv (f k)). exists k. split; lia.
Qed.

(** Right minima of f occur beyond every bound. *)
Lemma right_min_unbounded : forall (f : nat -> nat) (k : nat),
  exists n, (k <= n)%nat /\ right_min f n.
Proof.
  intros f k. destruct (tail_min_exists f k) as [n [Hkn Hmin]].
  exists n. split; [exact Hkn |]. intros m Hnm. apply Hmin. lia.
Qed.

(** Dickson's lemma for pairs.  If no pair i < j had f i <= f j and g i <= g j,
    then along the right minima of f the values of g would descend forever —
    impossible in nat. *)
Lemma dickson_pair : forall f g : nat -> nat,
  exists i j : nat, (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat.
Proof.
  intros f g.
  destruct (classic (exists i j : nat,
              (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat)) as [H | Hbad].
  - exact H.
  - exfalso.
    assert (Hdesc : forall i, right_min f i ->
              exists j, (i < j)%nat /\ right_min f j /\ (g j < g i)%nat).
    { intros i Hi.
      destruct (right_min_unbounded f (S i)) as [j [Hij Hj]].
      exists j. split; [lia | split; [exact Hj |]].
      destruct (Nat.le_gt_cases (g i) (g j)) as [Hle | Hlt]; [| exact Hlt].
      exfalso. apply Hbad. exists i, j.
      split; [lia | split; [exact (Hi j ltac:(lia)) | exact Hle]]. }
    assert (Hno : forall v i, right_min f i -> (g i <= v)%nat -> False).
    { induction v as [| v IH]; intros i Hi Hgi.
      - destruct (Hdesc i Hi) as [j [_ [_ Hgj]]]. lia.
      - destruct (Hdesc i Hi) as [j [_ [Hj Hgj]]]. apply (IH j Hj). lia. }
    destruct (right_min_unbounded f 0) as [i [_ Hi]].
    exact (Hno (g i) i Hi (Nat.le_refl _)).
Qed.

(* ================================================================= *)
(* WQO FOR SPECIFIC TYPES                                             *)
(* ================================================================= *)

Lemma wqo_unit : is_wqo (fun _ _ : unit => True).
Proof. intro f. exists 0, 1. split; [lia | exact I]. Qed.

(** false <= anything; true <= true only. *)
Lemma wqo_bool : is_wqo (fun a b : bool => implb a b = true).
Proof.
  intro f.
  destruct (f 0) eqn:E0.
  - destruct (f 1) eqn:E1.
    + exists 0, 1. split; [lia | rewrite E0, E1; reflexivity].
    + exists 1, 2. split; [lia | rewrite E1; reflexivity].
  - exists 0, 1. split; [lia | rewrite E0; reflexivity].
Qed.

(* ================================================================= *)
(* HIGMAN FOR UNIT LISTS (constructive)                                *)
(* ================================================================= *)

Lemma unit_list_embed_by_length : forall (xs ys : list unit),
  (length xs <= length ys)%nat -> list_le (fun _ _ => True) xs ys.
Proof.
  induction xs as [| [] xs' IH]; intros ys Hlen.
  - constructor.
  - destruct ys as [| [] ys']. simpl in Hlen. lia.
    apply list_le_cons. exact I. apply IH. simpl in Hlen. lia.
Qed.

Lemma higman_unit : is_wqo (list_le (fun _ _ : unit => True)).
Proof.
  intro f.
  destruct (wqo_nat_le (fun n => length (f n))) as [i [j [Hij Hle]]].
  exists i, j. split; [exact Hij | apply unit_list_embed_by_length; exact Hle].
Qed.

(* ================================================================= *)
(* SYNTHESIS                                                           *)
(* ================================================================= *)

Theorem higman_synthesis :
  is_wqo (fun _ _ : unit => True) /\
  is_wqo (fun a b : bool => implb a b = true) /\
  is_wqo Nat.le /\
  is_wqo (list_le (fun _ _ : unit => True)) /\
  (forall f g : nat -> nat, exists i j,
    (i < j)%nat /\ (f i <= f j)%nat /\ (g i <= g j)%nat).
Proof.
  split; [| split; [| split; [| split]]].
  - exact wqo_unit.
  - exact wqo_bool.
  - exact wqo_nat_le.
  - exact higman_unit.
  - exact dickson_pair.
Qed.

(* Axiom audit: closed under the global context — wqo_nat_le, wqo_unit,
   wqo_bool, higman_unit; Classical_Prop.classic — dickson_pair,
   higman_synthesis. *)
Print Assumptions wqo_nat_le.
Print Assumptions wqo_bool.
Print Assumptions higman_unit.
Print Assumptions dickson_pair.
Print Assumptions higman_synthesis.
