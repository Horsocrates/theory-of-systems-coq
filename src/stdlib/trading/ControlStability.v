(** * ControlStability.v — Lyapunov stability for trading systems as ToS System
    Elements: deviation values dV, Lyapunov function (dV^2), stability windows
    Roles:    stability checking (is_stable_step), window analysis (is_stable_window)
    Rules:    Lyapunov function must decrease step-by-step for stability,
              unstable if any step increases Lyapunov value
    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Lyapunov function: V(dV) = dV^2                                 *)
(* ================================================================ *)

Definition lyapunov (dV : Q) : Q := dV * dV.

(* Single step stability: V(now) <= V(prev) *)
Definition is_stable_step (dV_now dV_prev : Q) : bool :=
  Qle_bool (lyapunov dV_now) (lyapunov dV_prev).

(* Window stability: all consecutive pairs are stable *)
Fixpoint is_stable_window (deviations : list Q) : bool :=
  match deviations with
  | nil => true
  | _ :: nil => true
  | prev :: ((now :: _) as rest) =>
      is_stable_step now prev && is_stable_window rest
  end.

(* Count unstable steps in window *)
Fixpoint unstable_count (deviations : list Q) : nat :=
  match deviations with
  | nil => O
  | _ :: nil => O
  | prev :: ((now :: _) as rest) =>
      (if is_stable_step now prev then O else S O) + unstable_count rest
  end.

(* ================================================================ *)
(* Concrete Lyapunov values                                         *)
(* ================================================================ *)

Lemma lyapunov_1 : lyapunov 1 == 1.
Proof. unfold lyapunov. vm_compute. reflexivity. Qed.

Lemma lyapunov_half : lyapunov (1#2) == 1#4.
Proof. unfold lyapunov. vm_compute. reflexivity. Qed.

Lemma lyapunov_quarter : lyapunov (1#4) == 1#16.
Proof. unfold lyapunov. vm_compute. reflexivity. Qed.

Lemma lyapunov_zero : lyapunov 0 == 0.
Proof. unfold lyapunov. vm_compute. reflexivity. Qed.

Lemma lyapunov_neg : lyapunov (-(1)) == 1.
Proof. unfold lyapunov. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Step stability checks                                            *)
(* ================================================================ *)

(* Decreasing deviation: stable *)
Lemma step_stable_1_half : is_stable_step (1#2) 1 = true.
Proof. unfold is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Equal deviation: stable *)
Lemma step_stable_equal : is_stable_step 1 1 = true.
Proof. unfold is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Increasing deviation: unstable *)
Lemma step_unstable_half_1 : is_stable_step 1 (1#2) = false.
Proof. unfold is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Negative to smaller magnitude: stable *)
Lemma step_stable_neg : is_stable_step (1#2) (-(1)) = true.
Proof. unfold is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Window stability                                                 *)
(* ================================================================ *)

(* Decreasing sequence: stable *)
Definition dev_stable : list Q := [1; 1#2; 1#4; 1#8].

Lemma window_stable : is_stable_window dev_stable = true.
Proof. unfold dev_stable, is_stable_window, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Increasing sequence: unstable *)
Definition dev_unstable : list Q := [1#8; 1#4; 1#2; 1].

Lemma window_unstable : is_stable_window dev_unstable = false.
Proof. unfold dev_unstable, is_stable_window, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Constant sequence: stable *)
Definition dev_constant : list Q := [1#2; 1#2; 1#2; 1#2].

Lemma window_constant_stable : is_stable_window dev_constant = true.
Proof. unfold dev_constant, is_stable_window, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* Mixed: mostly stable with one blip *)
Definition dev_mixed : list Q := [1; 1#2; 3#4; 1#4].

Lemma window_mixed_unstable : is_stable_window dev_mixed = false.
Proof. unfold dev_mixed, is_stable_window, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Unstable step counting                                           *)
(* ================================================================ *)

Lemma unstable_count_stable : unstable_count dev_stable = O.
Proof. unfold dev_stable, unstable_count, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

Lemma unstable_count_unstable : unstable_count dev_unstable = 3%nat.
Proof. unfold dev_unstable, unstable_count, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

Lemma unstable_count_mixed : unstable_count dev_mixed = 1%nat.
Proof. unfold dev_mixed, unstable_count, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

Lemma unstable_count_constant : unstable_count dev_constant = O.
Proof. unfold dev_constant, unstable_count, is_stable_step, lyapunov. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Lyapunov monotonicity                                            *)
(* ================================================================ *)

(* Lyapunov value decreases along stable sequence *)
Lemma lyap_decreasing_step1 :
  lyapunov (1#2) < lyapunov 1.
Proof. unfold lyapunov, Qlt. vm_compute. reflexivity. Qed.

Lemma lyap_decreasing_step2 :
  lyapunov (1#4) < lyapunov (1#2).
Proof. unfold lyapunov, Qlt. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Synthesis                                                        *)
(* ================================================================ *)

Definition control_stability_synthesis : Prop :=
  is_stable_window dev_stable = true /\
  is_stable_window dev_unstable = false /\
  unstable_count dev_mixed = 1%nat /\
  lyapunov (1#2) < lyapunov 1.

Lemma control_stability_synthesis_holds : control_stability_synthesis.
Proof.
  split. exact window_stable.
  split. exact window_unstable.
  split. exact unstable_count_mixed.
  exact lyap_decreasing_step1.
Qed.
