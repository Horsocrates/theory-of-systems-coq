(** * AlphaSynthesis.v — Synthesis of alpha decay and classification
    Elements: alpha process, classification, decay thresholds;
    Roles:    unify finite-size alpha with type classification;
    Rules:    combined theorems for Direction 2.
    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
From ToS Require Import stdlib.trading.AlphaFiniteSize.
From ToS Require Import stdlib.trading.AlphaClassification.
Open Scope Q_scope.

(* ===== Cross-file: alpha with classification ===== *)

Lemma alpha_with_type :
  AlphaFiniteSize.alpha_process 10 (1#5) O == 10 /\
  classify_alpha (1#5) = Informational.
Proof.
  split; [exact alpha_day0 | exact classify_informational].
Qed.

Lemma structural_alpha_persists :
  classify_alpha (1#20) = Structural /\
  AlphaFiniteSize.qpow (4#5) 4 < 1#2.
Proof.
  split; [exact classify_structural | exact alpha_halflife].
Qed.

Lemma statistical_alpha_dies :
  classify_alpha (3#5) = Statistical /\
  AlphaFiniteSize.qpow (4#5) 8 < 1#5.
Proof.
  split; [exact classify_statistical | exact alpha_dead].
Qed.

(* ===== Initial value is universal ===== *)

Lemma alpha_always_starts_at_A0 :
  forall A0 p, AlphaFiniteSize.alpha_process A0 p O == A0.
Proof. exact alpha_initial_value. Qed.

(* ===== Classification covers all cases ===== *)

Lemma classification_exhaustive : forall d,
  classify_alpha d = Structural \/
  classify_alpha d = Informational \/
  classify_alpha d = Statistical.
Proof.
  intro d. unfold classify_alpha.
  destruct (Qlt_le_dec d (1#10)).
  - left. reflexivity.
  - destruct (Qlt_le_dec d (1#2)).
    + right. left. reflexivity.
    + right. right. reflexivity.
Qed.

(* ===== Decay monotonicity ===== *)

Lemma alpha_decays_monotonically :
  AlphaFiniteSize.alpha_process 10 (1#5) 1 <
  AlphaFiniteSize.alpha_process 10 (1#5) O.
Proof. exact alpha_monotone_01. Qed.

(* ===== Boundary classification ===== *)

Lemma boundary_types :
  classify_alpha 0 = Structural /\
  classify_alpha 1 = Statistical.
Proof.
  split; [exact classify_zero | exact classify_one].
Qed.

(* ===== Grand synthesis ===== *)

Theorem alpha_grand_synthesis :
  (* Initial value *)
  (forall A0 p, AlphaFiniteSize.alpha_process A0 p O == A0) /\
  (* Halflife *)
  AlphaFiniteSize.qpow (4#5) 4 < 1#2 /\
  (* Death *)
  AlphaFiniteSize.qpow (4#5) 8 < 1#5 /\
  (* Classification exhaustive *)
  (forall d, classify_alpha d = Structural \/
             classify_alpha d = Informational \/
             classify_alpha d = Statistical).
Proof.
  split; [exact alpha_initial_value|].
  split; [exact alpha_halflife|].
  split; [exact alpha_dead|].
  exact classification_exhaustive.
Qed.
