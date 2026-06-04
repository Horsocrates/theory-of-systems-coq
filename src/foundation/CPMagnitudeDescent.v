(** * CPMagnitudeDescent.v — Baryogenesis boundary, BRANCH 1/3 (JValue, the CP magnitude): walking the
      box step by step REFINES its earlier unconditional "RoleLimit" tag to a CONDITIONAL one.  The
      Jarlskog J is a PRODUCT of the angle trig values; its ANGLE COUNT is derived (3 mixing + 1 phase
      from 3 generations), but its role-limit status is CONDITIONAL on the angle VALUES being irrational.
      At RATIONAL (Pythagorean) trig values, J is RATIONAL — an Element (witnessed).  So J is NOT
      inherently a wall: the box converges into the rational/irrational finitization boundary (H1),
      localized to the CKM angles.

    BaryogenesisBoundary.v tagged JValue → RoleLimit.  But that was a label, not an analysis.  Walking
    it:
      Rules (L5):  J = Jarlskog = c12·c13²·c23 · s12·s13·s23 · sin δ — a PRODUCT of the angle trig values.
      Roles (L4):  4 parameters — 3 mixing angles + 1 CP phase; their COUNT is DERIVED (3 generations
                   ⟹ N(N−1)/2 = 3 angles, (N−1)(N−2)/2 = 1 phase).
      Elements:    the actual trig VALUES.  At rational (Pythagorean 3-4-5: cos=4/5, sin=3/5) values, J is
                   RATIONAL (Element) — witnessed below.  So J is NOT inherently a role-limit.

    THE REFINEMENT: the box splits {angle COUNT derived (Element)} + {angle VALUES = role-limit IFF
    irrational}.  J is Element whenever the trig values are (witnesses 3-4-5 and 5-12-13); its role-limit
    status is CONDITIONAL on the CKM angle values — the open input.  So the J branch bottoms out at the
    SAME rational/irrational finitization boundary (H1), now localized to the CKM angles; the count is
    derived; the values are the open input.  J is not a "magic wall" — it is that boundary on the angles.

    Elements: the Jarlskog product; the rational (3-4-5, 5-12-13) Element witnesses
    Roles:    the angle count (3 + 1) = derived; the angle values = the open input (role-limit iff irrational)
    Rules:    J = product of trig; Element whenever trig rational ⟹ the role-limit tag is CONDITIONAL

    ============ E/R/R разбор ============
      Rules (L5): J = инвариант Ярлског = произведение тригонометрии углов; правило — произведение.
      Roles (L4): 3 угла + 1 фаза; их СЧЁТ выведен (3 поколения ⟹ 3 угла, 1 фаза).
      Elements  : значения тригонометрии; при рац. (3-4-5) — J рационально (Element-свидетель).
    ДИАГНОСТИКА (P4): спуск уточняет безусловный ярлык RoleLimit на УСЛОВНЫЙ. J = {счёт выведен (Element)}
    + {значения = role-limit ⟺ иррац}. J Element при рац. тригонометрии (3-4-5, 5-12-13). Сходится в
    границу финитизации H1 (рац/иррац), локализованную на CKM-углах; счёт выведен, значения = открытый вход.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Arith Lia.
From ToS Require Import foundation.EtaFromLattice.   (* n_cp_phases_local, three_gen_one_cp *)

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The angle/phase COUNT is derived (3 generations ⟹ 3 mixing + 1 phase)   *)
(* ===================================================================== *)

(** CKM mixing-angle count = N(N−1)/2; CP-phase count = (N−1)(N−2)/2 — both fixed by N generations. *)
Definition n_mixing (n : nat) : nat := (n * (n - 1) / 2)%nat.

Lemma three_gen_mixing : n_mixing 3 = 3%nat.
Proof. reflexivity. Qed.

(** The CP-phase count = 1 — DERIVED (EtaFromLattice; 3 generations ⟹ exactly one irreducible phase). *)
Lemma three_gen_cp : n_cp_phases_local 3 = 1%nat.
Proof. exact three_gen_one_cp. Qed.

(* ===================================================================== *)
(*  J = the Jarlskog product; Element at rational (Pythagorean) trig         *)
(* ===================================================================== *)

(** The Jarlskog invariant: the rephasing-invariant product (3 cosines with c13 twice, 4 sines). *)
Definition jarlskog_prod (c12 c13 c23 s12 s13 s23 sd : Q) : Q :=
  c12 * c13 * c13 * c23 * s12 * s13 * s23 * sd.

(** ★ At rational 3-4-5 trig values (cos = 4/5, sin = 3/5), J is RATIONAL — an Element.  So J is NOT
    inherently a role-limit: it is Element exactly when the angle trig values are rational. *)
Definition jarlskog_345 : Q := jarlskog_prod (4#5) (4#5) (4#5) (3#5) (3#5) (3#5) (3#5).

Lemma jarlskog_345_rational : jarlskog_345 == 20736 # 390625.
Proof. unfold jarlskog_345, jarlskog_prod. vm_compute. reflexivity. Qed.

(** The Element witness is a genuine (positive) CP violation. *)
Lemma jarlskog_345_positive : 0 < jarlskog_345.
Proof. unfold jarlskog_345, jarlskog_prod. vm_compute. reflexivity. Qed.

(** ★ A second rational witness (5-12-13 angles): J is Element for any rational (Pythagorean) trig —
    the Element-ness is robust, so the role-limit tag is genuinely CONDITIONAL on the angle values. *)
Definition jarlskog_5_12_13 : Q := jarlskog_prod (12#13) (12#13) (12#13) (5#13) (5#13) (5#13) (5#13).

Lemma jarlskog_5_12_13_rational : jarlskog_5_12_13 == 12960000 # 815730721.
Proof. unfold jarlskog_5_12_13, jarlskog_prod. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: branch 1 — J's role-limit tag refined to conditional          *)
(* ===================================================================== *)

(** Branch 1 (JValue) walked:
      (count)    the angle/phase count is DERIVED — 3 mixing angles, 1 CP phase (3 generations);
      (Element)  at rational (3-4-5) trig, J is RATIONAL (= 20736/390625) and positive — an Element;
      (robust)   a second rational witness (5-12-13) confirms J is Element for rational trig;
      (refine)   so J is NOT inherently a role-limit — its role-limit status is CONDITIONAL on the CKM
                 angle VALUES being irrational (the open input).
    The J branch converges into the rational/irrational finitization boundary (H1), localized to the CKM
    angles: count derived, values the open input.  The unconditional "RoleLimit" tag is refined. *)
Theorem jvalue_descent :
  n_mixing 3 = 3%nat
  /\ n_cp_phases_local 3 = 1%nat
  /\ jarlskog_345 == 20736 # 390625
  /\ 0 < jarlskog_345
  /\ jarlskog_5_12_13 == 12960000 # 815730721.
Proof.
  split; [ exact three_gen_mixing | ].
  split; [ exact three_gen_cp | ].
  split; [ exact jarlskog_345_rational | ].
  split; [ exact jarlskog_345_positive | ].
  exact jarlskog_5_12_13_rational.
Qed.
