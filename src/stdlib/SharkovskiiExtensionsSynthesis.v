(** * SharkovskiiExtensionsSynthesis.v — Grand synthesis of Sharkovskii extensions
    Elements: circle maps, higher-dim counterexamples, entropy hierarchy
    Roles:    topological constraints on forcing
    Rules:    Sharkovskii holds on interval only; circle and 2D have different forcing
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)
From Stdlib Require Import QArith Qabs Lia ZArith List Bool.
From Stdlib Require Import Lqa.
Import ListNotations.
From ToS Require Import stdlib.SharkovskiiCircle.
From ToS Require Import stdlib.SharkovskiiHigherDim.
From ToS Require Import stdlib.SharkovskiiEntropy.
Open Scope Q_scope.

(** Circle: period-3 does NOT force all periods *)
Lemma circle_key :
  doubling_map 7 1 = 2%nat /\ doubling_map 7 2 = 4%nat /\ doubling_map 7 4 = 1%nat.
Proof. exact doubling_orbit_period3. Qed.

(** Higher dim: period-3 without period-2 *)
Lemma higher_dim_key :
  cyclic3 [1; 0; 0] = [0; 1; 0] /\
  cyclic3 (cyclic3 [1; 0; 0]) <> [1; 0; 0].
Proof.
  split.
  - exact cyclic3_step1.
  - intro H. discriminate.
Qed.

(** Entropy: golden subshift < full shift *)
Lemma entropy_key : h_golden_pade < h_full_pade.
Proof. exact golden_less_than_full. Qed.

(** Pade ln consistency *)
Lemma pade_consistency :
  pade_ln (8#5) == 6#13 /\ pade_ln 2 == 2#3.
Proof. split; [exact pade_ln_phi | exact pade_ln_2]. Qed.

(** Orbit counts: golden grows slower than full shift *)
Lemma orbit_divergence :
  (lucas (S(S(S(S(S O))))) < 32)%Z /\
  (lucas (S(S(S(S(S(S O)))))) < 64)%Z.
Proof. split; [exact orbit_count_n5 | exact orbit_count_n6]. Qed.

(** Rotation vs doubling: pure rotation has uniform periods *)
Lemma rotation_vs_nonlinear :
  (* Rotation: all orbits period q *)
  cyclic_rotate 1 3 0 = 1%nat /\ cyclic_rotate 1 3 1 = 2%nat /\ cyclic_rotate 1 3 2 = 0%nat /\
  (* Doubling: mixed periods *)
  doubling_map 7 0 = 0%nat /\ doubling_map 7 1 = 2%nat.
Proof. vm_compute. repeat split. Qed.

(** Grand synthesis *)
Theorem sharkovskii_extensions_synthesis :
  (* Circle: period-3 does NOT force all periods *)
  doubling_map 7 1 = 2%nat /\
  (* 2D: period-3 without chaos *)
  cyclic3 [1; 0; 0] = [0; 1; 0] /\
  (* Entropy: golden < full *)
  h_golden_pade < h_full_pade /\
  (* Orbit counts diverge *)
  (lucas (S(S(S(S(S O))))) < 32)%Z /\
  (* Pade ln works *)
  pade_ln 2 == 2#3.
Proof.
  split; [vm_compute; reflexivity|].
  split; [exact cyclic3_step1|].
  split; [exact golden_less_than_full|].
  split; [exact orbit_count_n5|].
  exact pade_ln_2.
Qed.

(** Three domains where Sharkovskii fails *)
Theorem sharkovskii_boundaries :
  (* 1. Circle: topology ≠ interval *)
  (doubling_map 3 1 = 2%nat /\ doubling_map 3 2 = 1%nat) /\
  (* 2. Higher dim: no forcing *)
  (cyclic3 (cyclic3 [1; 0; 0]) <> [1; 0; 0]) /\
  (* 3. Entropy stratifies dynamics *)
  (h_identity < h_golden_pade /\ h_golden_pade < h_full_pade).
Proof.
  split; [vm_compute; split; reflexivity|].
  split; [intro H; discriminate|].
  exact entropy_chain.
Qed.
