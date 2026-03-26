(* MajorizationSchur.v *)
(* Elements: apply_T mixing operator, ln_pade approximation, S2 entropy *)
(* Roles: majorization (mixing moves toward uniform), Schur concavity *)
(* Rules: concrete majorization, concrete entropy increase, max at 1/2 *)

From Coq Require Import QArith Lia Lqa.
From ToS Require Import stdlib.foundations.DoublyStochastic.

Open Scope Q_scope.

(* ===== Mixing Operator ===== *)

Definition apply_T (t a : Q) : Q := (1-t)*a + t*(1-a).

(* Concrete: apply_T (1/3) (3/4) = 7/12 *)
Lemma apply_T_concrete_1 : apply_T (1#3) (3#4) == 7#12.
Proof. vm_compute. reflexivity. Qed.

(* Concrete: apply_T (1/4) (9/10) = 7/10 *)
Lemma apply_T_concrete_2 : apply_T (1#4) (9#10) == 7#10.
Proof. vm_compute. reflexivity. Qed.

(* Majorization: mixing moves toward 1/2 *)

(* 7/12 < 3/4 *)
Lemma majorization_closer_1 : apply_T (1#3) (3#4) < 3#4.
Proof. vm_compute. reflexivity. Qed.

(* 7/12 > 1/2 *)
Lemma majorization_above_half_1 : 1#2 < apply_T (1#3) (3#4).
Proof. vm_compute. reflexivity. Qed.

(* 7/10 < 9/10 *)
Lemma majorization_closer_2 : apply_T (1#4) (9#10) < 9#10.
Proof. vm_compute. reflexivity. Qed.

(* 7/10 > 1/2 *)
Lemma majorization_above_half_2 : 1#2 < apply_T (1#4) (9#10).
Proof. vm_compute. reflexivity. Qed.

(* apply_T at 1/2 is fixed point *)
Lemma apply_T_fixed_half : forall t, apply_T t (1#2) == 1#2.
Proof. intros t. unfold apply_T. ring. Qed.

(* ===== Entropy via Pade Approximation ===== *)

Definition ln_pade (x : Q) : Q := 2 * (x - 1) / (x + 1).

Definition S2 (a : Q) : Q := -(a * ln_pade a + (1-a) * ln_pade (1-a)).

(* Concrete entropy values *)

Lemma S2_at_34 : S2 (3#4) == 18#35.
Proof. vm_compute. reflexivity. Qed.

Lemma S2_at_712 : S2 (7#12) == 210#323.
Proof. vm_compute. reflexivity. Qed.

Lemma S2_at_half : S2 (1#2) == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma S2_at_910 : S2 (9#10) == 54#209.
Proof. vm_compute. reflexivity. Qed.

Lemma S2_at_710 : S2 (7#10) == 126#221.
Proof. vm_compute. reflexivity. Qed.

(* ===== Entropy Increase: S2(a) < S2(apply_T t a) ===== *)

(* S2(3/4) < S2(7/12) *)
Lemma entropy_increase_1 : S2 (3#4) < S2 (apply_T (1#3) (3#4)).
Proof. vm_compute. reflexivity. Qed.

(* S2(9/10) < S2(7/10) *)
Lemma entropy_increase_2 : S2 (9#10) < S2 (apply_T (1#4) (9#10)).
Proof. vm_compute. reflexivity. Qed.

(* ===== Maximum at 1/2 ===== *)

(* S2(3/4) < S2(1/2) *)
Lemma S2_34_lt_max : S2 (3#4) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

(* S2(9/10) < S2(1/2) *)
Lemma S2_910_lt_max : S2 (9#10) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

(* S2(7/12) < S2(1/2) *)
Lemma S2_712_lt_max : S2 (7#12) < S2 (1#2).
Proof. vm_compute. reflexivity. Qed.

(* Connection to T_distinction *)
Lemma T_distinction_matches : forall p,
  T_distinction p 0 1 == p.
Proof. intros p. unfold T_distinction. simpl. ring. Qed.
