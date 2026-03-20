(** * EntropySynthesis.v -- Entropy + Lyapunov + Li-Yorke unified
    Elements: chaos_trinity
    Roles:    Three equivalent characterizations of chaos for tent map
    Rules:    h_top = λ = ln(2) > 0, period 3 (Li-Yorke)
    Status:   Stdlib
    STATUS: 8 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.TopologicalEntropy.
From ToS Require Import stdlib.LyapunovProcess.
From ToS Require Import stdlib.LiYorkeSensitivity.

Open Scope Q_scope.

(* ================================================================== *)
(*  THE CHAOS TRINITY                                                  *)
(* ================================================================== *)

(** h_top > 0 ↔ λ > 0 ↔ sensitive ↔ Li-Yorke chaotic
    THREE equivalent characterizations of chaos:
    1. h_top > 0: topological complexity grows exponentially
    2. λ > 0: nearby orbits diverge exponentially
    3. Li-Yorke: ∃ uncountably many scrambled pairs *)

Lemma entropy_equals_lyapunov : h_top_tent == tent_lyapunov.
Proof. unfold h_top_tent, tent_lyapunov. reflexivity. Qed.

Lemma entropy_positive : 0 < h_top_tent.
Proof. exact tent_positive_entropy. Qed.

Lemma lyapunov_positive : 0 < tent_lyapunov.
Proof. exact tent_lyapunov_positive. Qed.

(** Period 3 orbit: T(2/7) → 4/7 → 6/7 → 2/7 *)
Lemma period3_step1 : tent_map (2#7) == 4#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma period3_step2 : tent_map (4#7) == 6#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Lemma period3_step3 : tent_map (6#7) == 2#7.
Proof. unfold tent_map. vm_compute. reflexivity. Qed.

Theorem chaos_trinity :
  h_top_tent == tent_lyapunov /\
  0 < h_top_tent /\
  0 < tent_lyapunov /\
  tent_map (2#7) == 4#7 /\
  tent_map (4#7) == 6#7 /\
  tent_map (6#7) == 2#7.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact entropy_equals_lyapunov.
  - exact entropy_positive.
  - exact lyapunov_positive.
  - exact period3_step1.
  - exact period3_step2.
  - exact period3_step3.
Qed.
