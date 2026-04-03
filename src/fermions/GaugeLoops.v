(** GaugeLoops.v — Gauge and self-coupling loop corrections *)
(** Combined with top loop: total correction to Higgs mass         *)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import fermions.TopLoop.

(* ================================================================= *)
(* Gauge boson loop sum (same structure as fermion)                  *)
(* gauge_loop_sum_4(m_W_sq) = (1/4)*(2/(1/2+m_W_sq) + 1/(1+m_W_sq))*)
(* ================================================================= *)

Definition gauge_loop_sum_4 (m_W_sq : Q) : Q :=
  (1#4) * (2 / ((1#2) + m_W_sq) + 1 / (1 + m_W_sq)).

Definition delta_mH_gauge (g_sq loop : Q) : Q :=
  3 * g_sq * loop.

Definition delta_mH_self (lam loop : Q) : Q :=
  3 * lam * lam * loop.

(* ================================================================= *)
(* Our specific couplings for the total correction                  *)
(* g^2 = 42/100,  m_W^2 = 1/10,  lambda = 1/2                     *)
(* ================================================================= *)

Definition our_delta_total : Q :=
  delta_mH_sq 1 (top_loop_sum_4 1)
  + delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10))
  + delta_mH_self (Qmake 1 2) (gauge_loop_sum_4 1).

(* ================================================================= *)
(* Theorem 1: Gauge loop sum at m_W^2=1/10                          *)
(* = (1/4)*(2/(3/5) + 1/(11/10)) = (1/4)*(10/3 + 10/11)           *)
(* = (1/4)*(140/33) = 35/33                                         *)
(* ================================================================= *)

Theorem gauge_loop_value :
  gauge_loop_sum_4 (Qmake 1 10) == 35#33.
Proof. unfold gauge_loop_sum_4. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Theorem 2: Gauge correction is positive                          *)
(* delta_gauge = 3 * 42/100 * 35/33 = 147/110                      *)
(* ================================================================= *)

Theorem gauge_positive :
  delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10)) > 0.
Proof.
  unfold delta_mH_gauge, gauge_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 3: Gauge correction concrete value                       *)
(* ================================================================= *)

Theorem gauge_correction_value :
  delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10)) == 147#110.
Proof.
  unfold delta_mH_gauge, gauge_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 4: Self-coupling correction is positive                  *)
(* delta_self = 3 * (1/2)^2 * 11/24 = 3/4 * 11/24 = 11/32         *)
(* ================================================================= *)

Theorem self_positive :
  delta_mH_self (Qmake 1 2) (gauge_loop_sum_4 1) > 0.
Proof.
  unfold delta_mH_self, gauge_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 5: Self correction concrete value                        *)
(* gauge_loop_sum_4(1) = 11/24 (same as top_loop_sum_4(1))         *)
(* delta_self = 3 * 1/4 * 11/24 = 33/96 = 11/32                   *)
(* ================================================================= *)

Theorem self_correction_value :
  delta_mH_self (Qmake 1 2) (gauge_loop_sum_4 1) == 11#32.
Proof.
  unfold delta_mH_self, gauge_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 6: Top correction is negative (re-exported)              *)
(* delta_top = -3 * 1 * 11/24 = -11/8                              *)
(* ================================================================= *)

Theorem top_negative :
  delta_mH_sq 1 (top_loop_sum_4 1) < 0.
Proof.
  unfold delta_mH_sq, N_c, top_loop_sum_4. vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 7: TOTAL correction is POSITIVE                          *)
(* total = -11/8 + 147/110 + 11/32 = 537/1760 > 0                  *)
(* Gauge + self overcome the top quark!                              *)
(* ================================================================= *)

Theorem total_sign :
  our_delta_total > 0.
Proof.
  unfold our_delta_total, delta_mH_sq, N_c, top_loop_sum_4,
         delta_mH_gauge, gauge_loop_sum_4, delta_mH_self.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Theorem 8: Total correction concrete value                       *)
(* ================================================================= *)

Theorem total_correction_value :
  our_delta_total == 537#1760.
Proof.
  unfold our_delta_total, delta_mH_sq, N_c, top_loop_sum_4,
         delta_mH_gauge, gauge_loop_sum_4, delta_mH_self.
  vm_compute. reflexivity.
Qed.

(* ================================================================= *)
(* Synthesis                                                         *)
(* ================================================================= *)

Theorem gauge_loops_synthesis :
  delta_mH_sq 1 (top_loop_sum_4 1) < 0 /\
  delta_mH_gauge (Qmake 42 100) (gauge_loop_sum_4 (Qmake 1 10)) > 0 /\
  delta_mH_self (Qmake 1 2) (gauge_loop_sum_4 1) > 0 /\
  our_delta_total > 0 /\
  our_delta_total == 537#1760.
Proof.
  unfold our_delta_total, delta_mH_sq, N_c, top_loop_sum_4,
         delta_mH_gauge, gauge_loop_sum_4, delta_mH_self.
  repeat split; vm_compute; reflexivity.
Qed.
