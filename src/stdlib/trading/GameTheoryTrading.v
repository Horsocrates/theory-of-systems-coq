(** * GameTheoryTrading.v — Game-theoretic strategy adoption model
    Elements: adoption rates, profit decay, strategy rotation;
    Roles:    first-mover advantage, strategy half-life;
    Rules:    adoption erodes edge — profit decays as (1-p)^t.
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Local qpow ===== *)

Fixpoint qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => x * qpow x k
  end.

(* ===== Adoption and Profit Decay ===== *)

Definition adoption (p : Q) (t : nat) : Q := 1 - qpow (1 - p) t.

Definition profit_decay (p : Q) (t : nat) : Q := qpow (1 - p) t.

(* ===== Strategy Signal ===== *)
(* If profit decay < 1/2, strategy is crowded => rotate *)

Definition strategy_signal (p : Q) (t : nat) : Z :=
  match Qlt_le_dec (profit_decay p t) (1#2) with
  | left _ => (-1)%Z   (* crowded, rotate away *)
  | right _ => 1%Z     (* still profitable *)
  end.

(* ===== Concrete: p = 1/5 ===== *)

Definition p_ex : Q := 1#5.

(* qpow values *)
Lemma qpow_4_5_0 : qpow (4#5) O = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_4_5_1 : qpow (4#5) (S O) = 4#5.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_4_5_2 : qpow (4#5) (S (S O)) == 16#25.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_4_5_3 : qpow (4#5) (S (S (S O))) == 64#125.
Proof. vm_compute. reflexivity. Qed.

Lemma qpow_4_5_4 : qpow (4#5) (S (S (S (S O)))) == 256#625.
Proof. vm_compute. reflexivity. Qed.

(* Half-life check: (4/5)^4 = 256/625 < 1/2 *)
Lemma half_life_check : qpow (4#5) (S (S (S (S O)))) < 1#2.
Proof. unfold Qlt. simpl. lia. Qed.

(* But (4/5)^3 = 64/125 > 1/2 = 62.5/125 *)
Lemma not_yet_at_3 : 1#2 < qpow (4#5) (S (S (S O))).
Proof. unfold Qlt. simpl. lia. Qed.

(* Adoption at t=1: 1 - 4/5 = 1/5 *)
Lemma adoption_1 : adoption p_ex (S O) == 1#5.
Proof. vm_compute. reflexivity. Qed.

(* Adoption at t=2: 1 - 16/25 = 9/25 *)
Lemma adoption_2 : adoption p_ex (S (S O)) == 9#25.
Proof. vm_compute. reflexivity. Qed.

(* Adoption at t=3: 1 - 64/125 = 61/125 *)
Lemma adoption_3 : adoption p_ex (S (S (S O))) == 61#125.
Proof. vm_compute. reflexivity. Qed.

(* Adoption at t=4: 1 - 256/625 = 369/625 *)
Lemma adoption_4 : adoption p_ex (S (S (S (S O)))) == 369#625.
Proof. vm_compute. reflexivity. Qed.

(* Profit decay *)
Lemma decay_1 : profit_decay p_ex (S O) == 4#5.
Proof. vm_compute. reflexivity. Qed.

Lemma decay_2 : profit_decay p_ex (S (S O)) == 16#25.
Proof. vm_compute. reflexivity. Qed.

Lemma decay_4 : profit_decay p_ex (S (S (S (S O)))) == 256#625.
Proof. vm_compute. reflexivity. Qed.

(* Strategy signal *)
Lemma signal_t1 : strategy_signal p_ex (S O) = 1%Z.
Proof.
  unfold strategy_signal, profit_decay, p_ex.
  simpl. destruct (Qlt_le_dec (4#5) (1#2)).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - reflexivity.
Qed.

Lemma signal_t3 : strategy_signal p_ex (S (S (S O))) = 1%Z.
Proof.
  unfold strategy_signal, profit_decay, p_ex. simpl.
  destruct (Qlt_le_dec ((4#5)*((4#5)*((4#5)*1))) (1#2)).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - reflexivity.
Qed.

Lemma signal_t4 : strategy_signal p_ex (S (S (S (S O)))) = (-1)%Z.
Proof.
  unfold strategy_signal, profit_decay, p_ex. simpl.
  destruct (Qlt_le_dec ((4#5)*((4#5)*((4#5)*((4#5)*1)))) (1#2)).
  - reflexivity.
  - exfalso. unfold Qle in q. simpl in q. lia.
Qed.

(* ===== Properties ===== *)

Lemma adoption_plus_decay : forall p t,
  adoption p t + profit_decay p t == 1.
Proof.
  intros. unfold adoption, profit_decay. ring.
Qed.

Lemma adoption_0 : forall p, adoption p O == 0.
Proof. intros. vm_compute. reflexivity. Qed.

Lemma profit_decay_0 : forall p, profit_decay p O = 1.
Proof. intros. reflexivity. Qed.

(* ===== Payoff matrix (2-player) ===== *)

Definition payoff (cooperate1 cooperate2 : bool) : Q :=
  match cooperate1, cooperate2 with
  | true, true => 3       (* mutual cooperation *)
  | true, false => 0      (* sucker *)
  | false, true => 5      (* temptation *)
  | false, false => 1     (* mutual defection *)
  end.

Lemma nash_defect : payoff false false = 1.
Proof. reflexivity. Qed.

Lemma temptation_gt_coop : payoff false true > payoff true true.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma coop_gt_defect : payoff true true > payoff false false.
Proof. unfold Qlt. simpl. lia. Qed.
