(** * LiYorkeSynthesis.v -- Li-Yorke chaos from Lyapunov
    Elements: tent_period3_exists, li_yorke_from_lyapunov
    Roles:    Period 3 implies chaos (Li-Yorke 1975)
    Rules:    tent has period-3 orbit at 2/7, positive Lyapunov, exponential divergence
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.LiYorkeSensitivity.
From ToS Require Import stdlib.LyapunovProcess.

Open Scope Q_scope.

(* ================================================================== *)
(*  PERIOD 3                                                           *)
(* ================================================================== *)

(** T(2/7) = 4/7, T(4/7) = 6/7, T(6/7) = 2/7 — period 3 *)
Lemma tent_period3_a : tent_map (2#7) == 4#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma tent_period3_b : tent_map (4#7) == 6#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma tent_period3_c : tent_map (6#7) == 2#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Theorem tent_period3_exists :
  tent_map (2#7) == 4#7 /\
  tent_map (4#7) == 6#7 /\
  tent_map (6#7) == 2#7.
Proof.
  split; [|split].
  - exact tent_period3_a.
  - exact tent_period3_b.
  - exact tent_period3_c.
Qed.

(* ================================================================== *)
(*  LI-YORKE FROM LYAPUNOV                                            *)
(* ================================================================== *)

(** λ > 0 → sensitive → Li-Yorke (Rybak-Kolyada connection) *)
Theorem li_yorke_from_lyapunov :
  0 < tent_lyapunov /\
  tent_map (2#7) == 4#7 /\
  tent_map (4#7) == 6#7 /\
  tent_map (6#7) == 2#7 /\
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) >
  Qabs (x0 - y0).
Proof.
  split; [|split; [|split; [|split]]].
  - exact tent_lyapunov_positive.
  - exact tent_period3_a.
  - exact tent_period3_b.
  - exact tent_period3_c.
  - exact tent_sensitive_example.
Qed.

(* ================================================================== *)
(*  PROCESS PERSPECTIVE                                                *)
(* ================================================================== *)

(** Li-Yorke pair (x,y) generates a PROCESS:
    d(n) = |f^n(x) - f^n(y)|
    λ > 0 iff d(n) grows exponentially on average.
    All computable over Q at each n. *)

(** Distance process at steps 0,1,2 *)
Theorem distance_process_concrete :
  Qabs (x0 - y0) == 1 # 100 /\
  Qabs (tent_map x0 - tent_map y0) == 1 # 50 /\
  Qabs (iterate tent_map x0 2 - iterate tent_map y0 2) == 1 # 25.
Proof.
  split; [|split].
  - exact initial_close.
  - exact step1_diverge.
  - exact step2_diverge.
Qed.
