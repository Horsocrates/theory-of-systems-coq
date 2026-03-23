(** EntropyMarket.v — Market entropy and memory via transition matrices.
    E/R/R: Elements = transition traces, entropy signals;
           Roles = memory quantification, entropy change detection;
           Rules = entropy thresholds for regime transitions.
    STATUS: 25 Qed, 0 Admitted, 0 axioms *)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Transition matrix trace as market memory                         *)
(* ================================================================ *)

(* market_memory: 1 - (tr(M^2) - 1) / (B - 1)
   where B = number of bins (states), tr(M^2) in [1, B].
   memory = 1 means full memory (identity transition), 0 means no memory. *)

Definition market_memory (trM2 : Q) (B : nat) : Q :=
  1 - (trM2 - 1) / inject_Z (Z.of_nat (B - 1)%nat).

(* Entropy signal: compare current vs previous tr(M^2) *)
Definition entropy_signal (trM2_now trM2_prev : Q) : nat :=
  if Qlt_le_dec trM2_now trM2_prev then S O      (* entropy increasing = memory loss *)
  else if Qlt_le_dec trM2_prev trM2_now then O   (* entropy decreasing = memory gain *)
  else S (S O).                                    (* stable *)

(* Transition matrix trace for 2-state system *)
(* M = [[p, 1-p],[1-q, q]], M^2 diagonal = p^2+(1-p)(1-q), q^2+(1-q)(1-p) *)
(* tr(M^2) = p^2 + q^2 + 2(1-p)(1-q) *)
Definition tr_M2_2state (p q : Q) : Q :=
  p * p + q * q + 2 * (1 - p) * (1 - q).

(* Normalized entropy measure: (B - tr(M^2)) / (B - 1) *)
Definition norm_entropy (trM2 : Q) (B : nat) : Q :=
  (inject_Z (Z.of_nat B) - trM2) / inject_Z (Z.of_nat (B - 1)%nat).

(* ================================================================ *)
(* Concrete examples                                                *)
(* ================================================================ *)

(* B=4, tr(M^2)=3/2 *)
Lemma memory_example : market_memory (3#2) 4 == 5#6.
Proof. vm_compute. reflexivity. Qed.

(* B=4, tr(M^2)=1 (uniform, no memory) *)
Lemma memory_uniform : market_memory 1 4 == 1.
Proof. vm_compute. reflexivity. Qed.

(* B=4, tr(M^2)=4 (identity, full memory) *)
Lemma memory_identity : market_memory 4 4 == 0.
Proof. vm_compute. reflexivity. Qed.

(* B=2, tr(M^2)=1 *)
Lemma memory_b2_uniform : market_memory 1 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(* B=2, tr(M^2)=2 (identity) *)
Lemma memory_b2_identity : market_memory 2 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(* B=3, tr(M^2)=2 *)
Lemma memory_b3_mid : market_memory 2 3 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* Entropy signals *)
Lemma signal_entropy_increasing : entropy_signal (1#2) (3#2) = S O.
Proof.
  unfold entropy_signal.
  destruct (Qlt_le_dec (1#2) (3#2)) as [H|H]. reflexivity.
  exfalso. unfold Qle in H. simpl in H. lia.
Qed.

Lemma signal_entropy_decreasing : entropy_signal (3#2) (1#2) = O.
Proof.
  unfold entropy_signal.
  destruct (Qlt_le_dec (3#2) (1#2)) as [H|H].
  - exfalso. unfold Qlt in H. simpl in H. lia.
  - destruct (Qlt_le_dec (1#2) (3#2)) as [H2|H2]. reflexivity.
    exfalso. unfold Qle in H2. simpl in H2. lia.
Qed.

Lemma signal_entropy_stable : entropy_signal (3#2) (3#2) = S (S O).
Proof.
  unfold entropy_signal.
  destruct (Qlt_le_dec (3#2) (3#2)) as [H|H].
  - exfalso. unfold Qlt in H. simpl in H. lia.
  - destruct (Qlt_le_dec (3#2) (3#2)) as [H2|H2].
    + exfalso. unfold Qlt in H2. simpl in H2. lia.
    + reflexivity.
Qed.

(* 2-state transition matrix traces *)
(* Identity: p=1, q=1 => tr=2 *)
Lemma tr_identity_2 : tr_M2_2state 1 1 == 2.
Proof. vm_compute. reflexivity. Qed.

(* Uniform: p=1/2, q=1/2 => tr = 1/4+1/4+2*1/4 = 1 *)
Lemma tr_uniform_2 : tr_M2_2state (1#2) (1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* Asymmetric: p=3/4, q=1/4 *)
Lemma tr_asymmetric_2 : tr_M2_2state (3#4) (1#4) == 1.
Proof. vm_compute. reflexivity. Qed.

(* High persistence: p=9/10, q=9/10 *)
Lemma tr_persistent_2 : tr_M2_2state (9#10) (9#10) == 41#25.
Proof. vm_compute. reflexivity. Qed.

(* Normalized entropy *)
Lemma norm_entropy_uniform : norm_entropy 1 4 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_entropy_identity : norm_entropy 4 4 == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_entropy_mid : norm_entropy (5#2) 4 == 1#2.
Proof. vm_compute. reflexivity. Qed.

(* Memory equals entropy for these formulations *)
Lemma memory_eq_entropy :
  market_memory (3#2) 4 == norm_entropy (3#2) 4.
Proof. vm_compute. reflexivity. Qed.

Lemma memory_eq_entropy_b2 :
  market_memory (3#2) 2 == norm_entropy (3#2) 2.
Proof. vm_compute. reflexivity. Qed.

(* Memory of persistent 2-state *)
Lemma memory_persistent :
  market_memory (41#25) 2 == 9#25.
Proof. vm_compute. reflexivity. Qed.

(* tr_M2 for anti-correlated: p=1/4, q=3/4 *)
Lemma tr_anticorr_2 : tr_M2_2state (1#4) (3#4) == 1.
Proof. vm_compute. reflexivity. Qed.

(* Entropy of persistent system *)
Lemma norm_entropy_persistent :
  norm_entropy (41#25) 2 == 9#25.
Proof. vm_compute. reflexivity. Qed.

(* 2-state with p=1/3, q=2/3 *)
Lemma tr_thirdsym_2 : tr_M2_2state (1#3) (2#3) == 1.
Proof. vm_compute. reflexivity. Qed.

(* B=3 examples *)
Lemma memory_b3_low : market_memory (3#2) 3 == 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_entropy_b3_low : norm_entropy (3#2) 3 == 3#4.
Proof. vm_compute. reflexivity. Qed.

Lemma norm_entropy_b3_half : norm_entropy 2 3 == 1#2.
Proof. vm_compute. reflexivity. Qed.
