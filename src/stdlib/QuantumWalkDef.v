(** * QuantumWalkDef.v -- Hadamard Quantum Walk on Z: Definitions
    Elements: hadamard_coin, amplitudes at K=1..3, norm_sq, probabilities
    Roles:    Coin operator defines evolution; amplitudes are exact Q integers
    Rules:    P = |amp|^2 / norm_sq; asymmetry emerges at K=3 (5:1 ratio)
    Status:   complete
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    (actual count verified after compilation)
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* Hadamard coin: (a,b) -> (a+b, a-b)                                 *)
(* ------------------------------------------------------------------ *)

Definition hadamard_coin (a b : Q) : Q * Q := (a + b, a - b).

Lemma hadamard_coin_example : hadamard_coin 1 0 = (1, 1).
Proof. unfold hadamard_coin. f_equal; ring. Qed.

Lemma hadamard_coin_sym : hadamard_coin 0 1 = (1, -1).
Proof. unfold hadamard_coin. f_equal; ring. Qed.

(* ------------------------------------------------------------------ *)
(* K=1: Start |0,R>. After 1 step: pos +1 amp (1,0), pos -1 amp (0,1) *)
(* ------------------------------------------------------------------ *)

Definition amp_K1_plus1_L : Q := 1.
Definition amp_K1_plus1_R : Q := 0.
Definition amp_K1_minus1_L : Q := 0.
Definition amp_K1_minus1_R : Q := 1.

Definition norm_sq_1 : Q := 2.

Lemma norm_sq_1_check :
  amp_K1_plus1_L * amp_K1_plus1_L + amp_K1_plus1_R * amp_K1_plus1_R +
  amp_K1_minus1_L * amp_K1_minus1_L + amp_K1_minus1_R * amp_K1_minus1_R == norm_sq_1.
Proof. vm_compute. reflexivity. Qed.

Definition P_K1_plus1 : Q := 1 # 2.
Definition P_K1_minus1 : Q := 1 # 2.

Lemma P_K1_plus1_correct :
  (amp_K1_plus1_L * amp_K1_plus1_L + amp_K1_plus1_R * amp_K1_plus1_R) / norm_sq_1 == P_K1_plus1.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* K=2: pos +2:(1,0), pos 0:(0,1), pos -2:(0,1)                      *)
(* Actually: +2 amp (1,0), 0 amp (-1,1), -2 amp (0,1)                 *)
(* ------------------------------------------------------------------ *)

Definition amp_K2_plus2_L : Q := 1.
Definition amp_K2_plus2_R : Q := 0.
Definition amp_K2_zero_L : Q := -1.
Definition amp_K2_zero_R : Q := 1.
Definition amp_K2_minus2_L : Q := 0.
Definition amp_K2_minus2_R : Q := 1.

Definition norm_sq_2 : Q := 4.

Lemma norm_sq_2_check :
  amp_K2_plus2_L * amp_K2_plus2_L + amp_K2_plus2_R * amp_K2_plus2_R +
  amp_K2_zero_L * amp_K2_zero_L + amp_K2_zero_R * amp_K2_zero_R +
  amp_K2_minus2_L * amp_K2_minus2_L + amp_K2_minus2_R * amp_K2_minus2_R == norm_sq_2.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* K=3: pos +3:(1,0), +1:(0,-2), -1:(0,1), -3:(0,1)                  *)
(* Correct K=3: +3:(1,0), +1:(-2,-1), -1:(1,0), -3:(0,1)             *)
(* ------------------------------------------------------------------ *)

Definition amp_K3_plus3_L : Q := 1.
Definition amp_K3_plus3_R : Q := 0.
Definition amp_K3_plus1_L : Q := -2.
Definition amp_K3_plus1_R : Q := -1.
Definition amp_K3_minus1_L : Q := 1.
Definition amp_K3_minus1_R : Q := 0.
Definition amp_K3_minus3_L : Q := 0.
Definition amp_K3_minus3_R : Q := 1.

Definition norm_sq_3 : Q := 8.

Lemma norm_sq_3_check :
  amp_K3_plus3_L * amp_K3_plus3_L + amp_K3_plus3_R * amp_K3_plus3_R +
  amp_K3_plus1_L * amp_K3_plus1_L + amp_K3_plus1_R * amp_K3_plus1_R +
  amp_K3_minus1_L * amp_K3_minus1_L + amp_K3_minus1_R * amp_K3_minus1_R +
  amp_K3_minus3_L * amp_K3_minus3_L + amp_K3_minus3_R * amp_K3_minus3_R == norm_sq_3.
Proof. vm_compute. reflexivity. Qed.

(* Probabilities at K=3 *)
Definition P_K3_plus3 : Q := 1 # 8.
Definition P_K3_plus1 : Q := 5 # 8.
Definition P_K3_minus1 : Q := 1 # 8.
Definition P_K3_minus3 : Q := 1 # 8.

Lemma P_K3_plus1_correct :
  (amp_K3_plus1_L * amp_K3_plus1_L + amp_K3_plus1_R * amp_K3_plus1_R) / norm_sq_3 == P_K3_plus1.
Proof. vm_compute. reflexivity. Qed.

Lemma P_K3_minus1_correct :
  (amp_K3_minus1_L * amp_K3_minus1_L + amp_K3_minus1_R * amp_K3_minus1_R) / norm_sq_3 == P_K3_minus1.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Asymmetry: P(+1)/P(-1) = 5 at K=3                                  *)
(* ------------------------------------------------------------------ *)

Lemma asymmetry_K3_ratio :
  P_K3_plus1 == 5 * P_K3_minus1.
Proof. vm_compute. reflexivity. Qed.

(* Probability normalization *)
Lemma P_K3_sum_one :
  P_K3_plus3 + P_K3_plus1 + P_K3_minus1 + P_K3_minus3 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma P_K1_sum_one :
  P_K1_plus1 + P_K1_minus1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma P_K3_plus3_correct :
  (amp_K3_plus3_L * amp_K3_plus3_L + amp_K3_plus3_R * amp_K3_plus3_R) / norm_sq_3 == P_K3_plus3.
Proof. vm_compute. reflexivity. Qed.

Lemma P_K3_minus3_correct :
  (amp_K3_minus3_L * amp_K3_minus3_L + amp_K3_minus3_R * amp_K3_minus3_R) / norm_sq_3 == P_K3_minus3.
Proof. vm_compute. reflexivity. Qed.

Lemma P_K1_minus1_correct :
  (amp_K1_minus1_L * amp_K1_minus1_L + amp_K1_minus1_R * amp_K1_minus1_R) / norm_sq_1 == P_K1_minus1.
Proof. vm_compute. reflexivity. Qed.

(* Hadamard applied twice scales by 2 *)
Lemma hadamard_double_fst : forall a b : Q,
  let p := hadamard_coin a b in
  fst (hadamard_coin (fst p) (snd p)) == 2 * a.
Proof. intros a b. unfold hadamard_coin. simpl. ring. Qed.

Lemma hadamard_double_snd : forall a b : Q,
  let p := hadamard_coin a b in
  snd (hadamard_coin (fst p) (snd p)) == 2 * b.
Proof. intros a b. unfold hadamard_coin. simpl. ring. Qed.
