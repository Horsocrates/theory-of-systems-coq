(** * MarchenkoPasturFilter.v — Random matrix eigenvalue filtering
    Elements: eigenvalues, MP thresholds, Newton sqrt iterations;
    Roles:    signal vs noise classification, spectral filtering;
    Rules:    eigenvalues above MP upper bound are signal.
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ===== Newton iteration for sqrt ===== *)

Definition newton_step (s x : Q) : Q := (x + s / x) / (2#1).

Fixpoint sqrt_newton (s : Q) (x0 : Q) (steps : nat) : Q :=
  match steps with
  | O => x0
  | S k => newton_step s (sqrt_newton s x0 k)
  end.

(* ===== Marchenko-Pastur upper bound: (1 + sqrt(q))^2 ===== *)

Definition mp_upper (q : Q) (steps : nat) : Q :=
  let sq := sqrt_newton q 1 steps in
  (1 + sq) * (1 + sq).

(* ===== Signal classification ===== *)

Definition is_signal (eigenvalue threshold : Q) : bool :=
  negb (Qle_bool eigenvalue threshold).

Definition classify_eigenvalue (eigenvalue q : Q) (steps : nat) : bool :=
  is_signal eigenvalue (mp_upper q steps).

(* ===== Concrete: q = 1/3 ===== *)

Definition q_ex : Q := 1#3.

(* Newton iterations for sqrt(1/3), starting at 1 *)
Lemma newton_0 : sqrt_newton q_ex 1 O = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_1 : sqrt_newton q_ex 1 (S O) == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma newton_2_val : sqrt_newton q_ex 1 (S (S O)) == 7#12.
Proof. vm_compute. reflexivity. Qed.

(* MP upper bound at various Newton steps *)
Lemma mp_upper_0 : mp_upper q_ex O = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma mp_upper_1 : mp_upper q_ex (S O) == 25#9.
Proof. vm_compute. reflexivity. Qed.

Lemma mp_upper_2 : mp_upper q_ex (S (S O)) == 361#144.
Proof. vm_compute. reflexivity. Qed.

(* Signal classification examples *)
Lemma big_eigenvalue_is_signal :
  is_signal 5 (mp_upper q_ex (S (S O))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma small_eigenvalue_is_noise :
  is_signal 1 (mp_upper q_ex (S (S O))) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma borderline_eigenvalue :
  is_signal 3 (mp_upper q_ex (S (S O))) = true.
Proof. vm_compute. reflexivity. Qed.

(* classify_eigenvalue tests *)
Lemma classify_signal_5 : classify_eigenvalue 5 q_ex (S (S O)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma classify_noise_1 : classify_eigenvalue 1 q_ex (S (S O)) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===== Newton step decreasing (converging from above for sqrt(1/3)) ===== *)

Lemma newton_1_lt_0 : sqrt_newton q_ex 1 (S O) < sqrt_newton q_ex 1 O.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma newton_2_lt_1 : sqrt_newton q_ex 1 (S (S O)) < sqrt_newton q_ex 1 (S O).
Proof. unfold Qlt. simpl. lia. Qed.

(* MP upper decreasing as sqrt refines *)
Lemma mp_upper_1_lt_0 : mp_upper q_ex (S O) < mp_upper q_ex O.
Proof. unfold Qlt. simpl. lia. Qed.

(* ===== Multiple eigenvalue filtering ===== *)

Definition filter_signals (eigenvalues : list Q) (threshold : Q) : list Q :=
  List.filter (fun e => is_signal e threshold) eigenvalues.

Definition count_signals (eigenvalues : list Q) (threshold : Q) : nat :=
  List.length (filter_signals eigenvalues threshold).

Definition example_eigenvalues : list Q := [5; 3; 1; (1#2); 4; (2#3)].

Lemma count_signals_example :
  count_signals example_eigenvalues (mp_upper q_ex (S (S O))) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma filter_signals_example :
  List.length (filter_signals example_eigenvalues 4) = 1%nat.
Proof. vm_compute. reflexivity. Qed.
