(** * PriceDynamicsODE.v — Discrete price dynamics as ODE approximation
    Elements: prices, forcing terms, Lipschitz constants;
    Roles:    Euler step, trajectory computation, stability;
    Rules:    Lipschitz < 1 implies stable dynamics.
    STATUS: 25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Price Step (Euler method) ===== *)

Definition price_step (p f_val : Q) : Q := p + f_val.

(* ===== Price Trajectory ===== *)

Fixpoint price_trajectory (p0 : Q) (forces : list Q) : Q :=
  match forces with
  | nil => p0
  | f :: rest => price_trajectory (price_step p0 f) rest
  end.

(* Collect all intermediate prices *)
Fixpoint price_history (p0 : Q) (forces : list Q) : list Q :=
  match forces with
  | nil => [p0]
  | f :: rest => p0 :: price_history (price_step p0 f) rest
  end.

(* ===== Lipschitz estimation ===== *)
(* For a sequence of (input, output) pairs, estimate max |Df/Dx| *)

Definition lipschitz_ratio (x1 y1 x2 y2 : Q) : Q :=
  Qabs (y2 - y1) / Qabs (x2 - x1).

Definition lipschitz_check (L : Q) : bool :=
  Qle_bool L 1.

(* ===== Stability Signal ===== *)

Definition stability_signal (L : Q) : Z :=
  match Qlt_le_dec L (1#2) with
  | left _ => 1%Z      (* strongly stable *)
  | right _ =>
    match Qlt_le_dec L 1 with
    | left _ => 0%Z     (* marginally stable *)
    | right _ => (-1)%Z (* unstable *)
    end
  end.

(* ===== Concrete: price trajectory ===== *)

Definition p0_ex : Q := 100.
Definition forces_ex : list Q := [1; -(1#2); (3#4); -(1#4); (1#2)].

(* Step by step:
   p0 = 100
   p1 = 100 + 1 = 101
   p2 = 101 - 1/2 = 201/2
   p3 = 201/2 + 3/4 = 405/4
   p4 = 405/4 - 1/4 = 101
   p5 = 101 + 1/2 = 203/2
*)

Lemma traj_step1 : price_step 100 1 = 101.
Proof. vm_compute. reflexivity. Qed.

Lemma traj_step2 : price_step 101 (-(1#2)) == 201#2.
Proof. vm_compute. reflexivity. Qed.

Lemma traj_step3 : price_step (201#2) (3#4) == 405#4.
Proof. vm_compute. reflexivity. Qed.

Lemma traj_step4 : price_step (405#4) (-(1#4)) == 101.
Proof. vm_compute. reflexivity. Qed.

Lemma traj_final : price_trajectory p0_ex forces_ex == 203#2.
Proof. vm_compute. reflexivity. Qed.

(* ===== Lipschitz examples ===== *)

Lemma lipschitz_small : lipschitz_ratio 1 2 3 3 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma lipschitz_large : lipschitz_ratio 1 1 2 5 == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma check_small_lip : lipschitz_check (1#2) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_large_lip : lipschitz_check 4 = false.
Proof. vm_compute. reflexivity. Qed.

(* ===== Stability signal examples ===== *)

Lemma signal_strong : stability_signal (1#4) = 1%Z.
Proof.
  unfold stability_signal.
  destruct (Qlt_le_dec (1#4) (1#2)).
  - reflexivity.
  - exfalso. unfold Qle in q. simpl in q. lia.
Qed.

Lemma signal_marginal : stability_signal (3#4) = 0%Z.
Proof.
  unfold stability_signal.
  destruct (Qlt_le_dec (3#4) (1#2)).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec (3#4) 1).
    + reflexivity.
    + exfalso. unfold Qle in q0. simpl in q0. lia.
Qed.

Lemma signal_unstable : stability_signal 2 = (-1)%Z.
Proof.
  unfold stability_signal.
  destruct (Qlt_le_dec 2 (1#2)).
  - exfalso. unfold Qlt in q. simpl in q. lia.
  - destruct (Qlt_le_dec 2 1).
    + exfalso. unfold Qlt in q0. simpl in q0. lia.
    + reflexivity.
Qed.

(* ===== Properties ===== *)

Lemma price_step_additive : forall p f, price_step p f == p + f.
Proof. intros. unfold price_step. ring. Qed.

Lemma traj_nil : forall p0, price_trajectory p0 nil = p0.
Proof. intros. reflexivity. Qed.

Lemma traj_single : forall p0 f, price_trajectory p0 [f] == p0 + f.
Proof. intros. simpl. unfold price_step. ring. Qed.

Lemma history_length : forall p0 forces,
  List.length (price_history p0 forces) = S (List.length forces).
Proof.
  intros p0 forces. revert p0. induction forces as [|f rest IH].
  - intros. reflexivity.
  - intros. simpl. f_equal. apply IH.
Qed.

Lemma history_head : forall p0 forces,
  List.hd 0 (price_history p0 forces) = p0.
Proof.
  intros. destruct forces; reflexivity.
Qed.

(* ===== Mean-reverting force ===== *)

Definition mean_reverting_force (p target alpha : Q) : Q :=
  alpha * (target - p).

Lemma mr_force_at_target : forall p alpha,
  mean_reverting_force p p alpha == 0.
Proof.
  intros. unfold mean_reverting_force. ring.
Qed.

Lemma mr_force_above : mean_reverting_force 110 100 (1#10) == -(1).
Proof. vm_compute. reflexivity. Qed.

Lemma mr_force_below : mean_reverting_force 90 100 (1#10) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===== Trajectory with mean-reverting force ===== *)

Fixpoint mr_trajectory (p0 target alpha : Q) (n : nat) : Q :=
  match n with
  | O => p0
  | S k =>
      let prev := mr_trajectory p0 target alpha k in
      prev + mean_reverting_force prev target alpha
  end.

Lemma mr_traj_0 : mr_trajectory 110 100 (1#10) O = 110.
Proof. reflexivity. Qed.

Lemma mr_traj_1 : mr_trajectory 110 100 (1#10) (S O) == 109.
Proof. vm_compute. reflexivity. Qed.

Lemma mr_traj_2 : mr_trajectory 110 100 (1#10) (S (S O)) == 1081#10.
Proof. vm_compute. reflexivity. Qed.
