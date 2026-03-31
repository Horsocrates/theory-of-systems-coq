(** * SingleSourcePrinciple.v — One graph → one C → C cancels
    Elements: coupling budget C, sin² from C
    Roles:    Single source → C₁ = C₂ → sin²θ independent of C
    Rules:    Standard Model: g,g' independent → sin²θ free.
              ToS: g,g' from SAME graph → C cancels → sin²θ determined.
    STATUS:   7 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: March 2026

    WHY C_SU(2) = C_U(1):
    Both couplings emerge from the SAME distinction graph.
    One graph → one total coupling budget C.
    g² = C/dim(SU(2)) = C/3.
    g'² = C/n_metric = C/10.
    sin²θ = (C/10)/(C/3 + C/10) = 3/13. C cancels.

    If they came from DIFFERENT sources, C₁ ≠ C₂ → sin²θ = free parameter.
    THIS is the difference between ToS (0 free params) and SM (19 free params).
*)

From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================== *)
(*  SINGLE SOURCE: C cancels                                           *)
(* ================================================================== *)

Definition sin2_from_C (C : Q) (dim_gauge dim_ambient : nat) : Q :=
  let g_sq := C / inject_Z (Z.of_nat dim_gauge) in
  let gprime_sq := C / inject_Z (Z.of_nat dim_ambient) in
  gprime_sq / (g_sq + gprime_sq).

(** ★ THE THEOREM: C cancels for ANY positive C *)
Lemma C_cancels_3_10 : forall C : Q, C > 0 ->
  sin2_from_C C 3 10 == 3 # 13.
Proof.
  intros C HC. unfold sin2_from_C. simpl.
  field. lra.
Qed.

(** Concrete instances showing C-independence *)
Lemma C_cancels_at_1 : sin2_from_C 1 3 10 == 3 # 13.
Proof. vm_compute. reflexivity. Qed.

Lemma C_cancels_at_42 : sin2_from_C 42 3 10 == 3 # 13.
Proof. vm_compute. reflexivity. Qed.

Lemma C_cancels_at_137 : sin2_from_C 137 3 10 == 3 # 13.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  INDEPENDENT SOURCES: C does NOT cancel                             *)
(* ================================================================== *)

(** If C₁ ≠ C₂: sin² depends on their ratio *)
Definition sin2_independent (C1 C2 : Q) (dim_gauge dim_ambient : nat) : Q :=
  let g_sq := C1 / inject_Z (Z.of_nat dim_gauge) in
  let gprime_sq := C2 / inject_Z (Z.of_nat dim_ambient) in
  gprime_sq / (g_sq + gprime_sq).

(** Different C's give different sin² *)
Lemma independent_gives_different :
  sin2_independent 1 1 3 10 == 3 # 13 /\
  sin2_independent 1 2 3 10 == 6 # 16.
Proof.
  split; unfold sin2_independent; vm_compute; reflexivity.
Qed.

(** 3/13 ≠ 6/16: different C ratio → different answer *)
Lemma independent_not_unique : ~ ((3#13) == (6#16)).
Proof. unfold Qeq. simpl. lia. Qed.

(* ================================================================== *)
(*  SYNTHESIS                                                          *)
(* ================================================================== *)

Theorem single_source_principle :
  (* Single source: C cancels *)
  (forall C, C > 0 -> sin2_from_C C 3 10 == 3 # 13) /\
  (* Independent: different C → different answer *)
  ~ ((3#13) == (6#16)) /\
  (* ToS has 0 free params in this ratio. SM has 1. *)
  sin2_from_C 42 3 10 == 3 # 13.
Proof.
  split; [exact C_cancels_3_10 |
  split; [exact independent_not_unique |
  exact C_cancels_at_42]].
Qed.
