(* CausalCone.v *)
(* E: Event, in_future_cone *)
(* R: Cone = set of causally reachable events *)
(* R: Boundary = lightlike. Inside = timelike. Outside = spacelike. *)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Z_scope.

Definition Event := (nat * nat)%type.

Definition in_future_cone (origin target : Event) : Prop :=
  let (s, K) := origin in
  let (s', K') := target in
  (K <= K')%nat /\ (Z.abs (Z.of_nat s' - Z.of_nat s) <= Z.of_nat (K' - K))%Z.

Lemma self_in_cone : in_future_cone (3%nat, 5%nat) (3%nat, 5%nat).
Proof. unfold in_future_cone. split; simpl; lia. Qed.

Lemma nearby_future : in_future_cone (3%nat, 5%nat) (4%nat, 6%nat).
Proof. unfold in_future_cone. split; simpl; lia. Qed.

Lemma far_not_in_cone : ~ in_future_cone (3%nat, 5%nat) (10%nat, 6%nat).
Proof. unfold in_future_cone. simpl. intros [H1 H2]. lia. Qed.

Lemma on_boundary : in_future_cone (3%nat, 5%nat) (6%nat, 8%nat).
Proof. unfold in_future_cone. split; simpl; lia. Qed.

Lemma past_not_future : ~ in_future_cone (3%nat, 5%nat) (3%nat, 4%nat).
Proof. unfold in_future_cone. intros [H1 H2]. lia. Qed.

Lemma cone_transitive_ex :
  in_future_cone (0%nat, 0%nat) (1%nat, 1%nat) /\
  in_future_cone (1%nat, 1%nat) (2%nat, 2%nat) ->
  in_future_cone (0%nat, 0%nat) (2%nat, 2%nat).
Proof. intros _. unfold in_future_cone. split; simpl; lia. Qed.

Lemma symmetric_site :
  in_future_cone (5%nat, 0%nat) (3%nat, 3%nat) /\
  in_future_cone (5%nat, 0%nat) (7%nat, 3%nat).
Proof.
  split; unfold in_future_cone; split; simpl; lia.
Qed.

(* Cone widens with time *)
Lemma cone_widens :
  in_future_cone (5%nat, 0%nat) (0%nat, 5%nat) /\
  ~ in_future_cone (5%nat, 0%nat) (0%nat, 4%nat).
Proof.
  split; unfold in_future_cone; simpl;
  [split; lia | intros [H1 H2]; lia].
Qed.

Lemma spacelike_separation : ~ in_future_cone (0%nat, 0%nat) (5%nat, 3%nat).
Proof. unfold in_future_cone. simpl. intros [H1 H2]. lia. Qed.
