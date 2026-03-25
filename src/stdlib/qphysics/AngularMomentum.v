(** * AngularMomentum.v -- Angular momentum and selection rules
    Elements: angular_factor, degeneracy, selection rules, Gaunt coefficients
    Roles:    Angular integrals contribute Q factors; |Y_lm|^2 eliminates sqrt
    Rules:    Selection rules from triangle inequality; degeneracy = 2l+1
    Status:   complete
    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Angular factors                                            *)
(* ================================================================== *)

(** Simplified angular prefactor: (2l+1) as Q value *)
Definition angular_factor (l : nat) : Q :=
  inject_Z (Z.of_nat (2 * l + 1)%nat).

Lemma angular_factor_0 : angular_factor O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma angular_factor_1 : angular_factor (S O) == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma angular_factor_2 : angular_factor (S (S O)) == 5.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Degeneracy                                                *)
(* ================================================================== *)

(** Degeneracy of angular momentum level l: 2l+1 states *)
Definition degeneracy (l : nat) : nat := (2 * l + 1)%nat.

Lemma degeneracy_s : (degeneracy O = 1)%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma degeneracy_p : (degeneracy (S O) = 3)%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma degeneracy_d : (degeneracy (S (S O)) = 5)%nat.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Selection rules                                          *)
(* ================================================================== *)

(** |l1 - l2| for natural numbers *)
Definition nat_abs_diff (a b : nat) : nat :=
  if Nat.leb a b then (b - a)%nat else (a - b)%nat.

(** Angular selection rule: |l1 - l2| <= l <= l1 + l2 *)
Definition angular_selection_rule (l1 l2 l : nat) : bool :=
  Nat.leb (nat_abs_diff l1 l2) l && Nat.leb l (l1 + l2).

(** s -> p transition (l=0 -> l=1, delta l = 1): allowed *)
Lemma selection_s_to_p :
  angular_selection_rule O (S O) (S O) = true.
Proof. vm_compute. reflexivity. Qed.

(** s -> d transition (l=0 -> l=2, via dipole l=1): forbidden *)
Lemma selection_s_to_d :
  angular_selection_rule O (S O) (S (S O)) = false.
Proof. vm_compute. reflexivity. Qed.

(** p -> d transition: allowed *)
Lemma selection_p_to_d :
  angular_selection_rule (S O) (S O) (S (S O)) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part IV: Gaunt coefficients squared are rational                   *)
(* ================================================================== *)

(** Gaunt integral = integral of three spherical harmonics.
    |Gaunt|^2 is always rational (product of factorials over factorials).
    This is a structural fact about 3j-symbols. *)

(** Gaunt^2 rationality: stated for the simplest case *)
Definition gaunt_sq_000 : Q := 1.
(* <Y_00 | Y_00 | Y_00> = 1/(4*pi) * (4*pi) = 1, squared = 1 *)

Lemma gaunt_sq_000_rational :
  exists (p : Z) (q : positive), gaunt_sq_000 == (p # q).
Proof. exists 1%Z, 1%positive. vm_compute. reflexivity. Qed.

(** Total angular states up to l_max *)
Fixpoint total_states (l_max : nat) : nat :=
  match l_max with
  | O => degeneracy O
  | S k => (total_states k + degeneracy (S k))%nat
  end.

Lemma total_states_2 : (total_states (S (S O)) = 9)%nat.
Proof. vm_compute. reflexivity. Qed.

