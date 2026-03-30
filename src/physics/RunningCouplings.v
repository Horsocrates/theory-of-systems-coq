(* ========================================================================= *)
(*  RUNNINGCOUPLINGS — Three Gauge Couplings Running with Energy Scale       *)
(*                                                                          *)
(*  Part of: Theory of Systems — Process Physics                            *)
(*                                                                          *)
(*  At unification scale: all couplings ~ kappa = 1/10.                     *)
(*  RG coefficients: b1=41/6 (U(1)), b2=-19/6 (SU(2)), b3=-7 (SU(3)).     *)
(*  U(1) grows at low energy; SU(2), SU(3) exhibit asymptotic freedom.     *)
(*                                                                          *)
(*  Elements: b1, b2, b3, alpha_inv_gut, alpha1/2/3_inv                    *)
(*  Roles:    coupling unification and asymptotic freedom from process      *)
(*  Rules:    sign of b_i determines running direction; b3<0 strongest AF   *)
(*  Status:   unification | splitting | confinement                        *)
(*                                                                          *)
(*  STATUS: 15 Qed, 0 Admitted                                              *)
(*  AXIOMS: none (purely constructive over Q)                               *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ---- Core definitions ---- *)

(* RG beta function coefficients for SM *)
Definition b1 : Q := 41 # 6.      (* U(1): positive = grows at low energy *)
Definition b2 : Q := -(19 # 6).   (* SU(2): negative = asymptotic freedom *)
Definition b3 : Q := -(7).        (* SU(3): negative = strong AF *)

(* At GUT unification: kappa^{-1} = 10 *)
Definition alpha_inv_gut : Q := 10.

(* Running couplings: alpha_inv_i(K) = alpha_inv_GUT + b_i * K *)
Definition alpha1_inv (K : nat) : Q := alpha_inv_gut + b1 * inject_Z (Z.of_nat K).
Definition alpha2_inv (K : nat) : Q := alpha_inv_gut + b2 * inject_Z (Z.of_nat K).
Definition alpha3_inv (K : nat) : Q := alpha_inv_gut + b3 * inject_Z (Z.of_nat K).

(* ---- Theorems ---- *)

(* 1. Unification: all couplings equal at K=0 *)
Lemma unification : alpha1_inv 0 == 10 /\ alpha2_inv 0 == 10 /\ alpha3_inv 0 == 10.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* 2. U(1) coupling weakens (alpha1_inv grows) *)
Lemma U1_grows : alpha1_inv 0 < alpha1_inv 1.
Proof. vm_compute. reflexivity. Qed.

(* 3. SU(2) coupling strengthens (alpha2_inv shrinks) *)
Lemma SU2_shrinks : alpha2_inv 1 < alpha2_inv 0.
Proof. vm_compute. reflexivity. Qed.

(* 4. SU(3) most strongly asymptotically free *)
Lemma SU3_strong_AF : alpha3_inv 1 < alpha3_inv 0.
Proof. vm_compute. reflexivity. Qed.

(* 5. SU(3) drops faster than SU(2) *)
Lemma SU3_faster_than_SU2 : alpha3_inv 1 < alpha2_inv 1.
Proof. vm_compute. reflexivity. Qed.

(* 6. At K=1: concrete values *)
(* alpha1_inv(1) = 10 + 41/6 = 101/6 ~ 16.8 *)
(* alpha2_inv(1) = 10 - 19/6 = 41/6  ~ 6.8 *)
(* alpha3_inv(1) = 10 - 7   = 3            *)
Lemma splitting_at_K1 :
  alpha1_inv 1 == 101 # 6 /\
  alpha2_inv 1 == 41 # 6 /\
  alpha3_inv 1 == 3.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* 7. Confinement scale: alpha3_inv goes negative past K=1 *)
(* alpha3_inv(2) = 10 - 14 = -4 *)
Lemma confinement_scale : alpha3_inv 2 == -(4).
Proof. vm_compute. reflexivity. Qed.

(* 8. SU(3) is asymptotically free: b3 < 0 *)
Lemma asymptotic_freedom_SU3 : b3 < 0.
Proof. vm_compute. reflexivity. Qed.

(* 9. SU(2) is asymptotically free: b2 < 0 *)
Lemma asymptotic_freedom_SU2 : b2 < 0.
Proof. vm_compute. reflexivity. Qed.

(* 10. U(1) is NOT asymptotically free: b1 > 0 *)
Lemma U1_not_AF : 0 < b1.
Proof. vm_compute. reflexivity. Qed.

(* 11. Ordering at K=1: alpha3 < alpha2 < alpha1 (inverse) *)
Lemma ordering_K1 : alpha3_inv 1 < alpha2_inv 1 /\ alpha2_inv 1 < alpha1_inv 1.
Proof. split; vm_compute; reflexivity. Qed.

(* 12. alpha1_inv is strictly increasing *)
Lemma alpha1_increasing : forall K : nat, alpha1_inv K < alpha1_inv (S K).
Proof.
  intro K. unfold alpha1_inv.
  rewrite Nat2Z.inj_succ.
  assert (Heq : inject_Z (Z.of_nat K + 1)%Z == inject_Z (Z.of_nat K) + 1).
  { rewrite inject_Z_plus. reflexivity. }
  rewrite Heq. unfold alpha_inv_gut, b1. lra.
Qed.

(* 13. alpha3_inv is strictly decreasing *)
Lemma alpha3_decreasing : forall K : nat, alpha3_inv (S K) < alpha3_inv K.
Proof.
  intro K. unfold alpha3_inv.
  rewrite Nat2Z.inj_succ.
  assert (Heq : inject_Z (Z.of_nat K + 1)%Z == inject_Z (Z.of_nat K) + 1).
  { rewrite inject_Z_plus. reflexivity. }
  rewrite Heq. unfold alpha_inv_gut, b3. lra.
Qed.

(* 14. SU(3) stronger than SU(2) at any K>0: b3 < b2 *)
Lemma b3_most_negative : b3 < b2.
Proof. vm_compute. reflexivity. Qed.

(* 15. Sum of beta coefficients *)
(* b1 + b2 + b3 = 41/6 - 19/6 - 7 = 22/6 - 7 = 22/6 - 42/6 = -20/6 = -10/3 *)
Lemma beta_sum : b1 + b2 + b3 == -(10 # 3).
Proof. vm_compute. reflexivity. Qed.
