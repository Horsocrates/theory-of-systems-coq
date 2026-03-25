(** * FineStructure.v -- Fine structure corrections as exact Q
    Elements: alpha_fine_sq, fine_correction, delta_E_2_half,
              hyperfine_scale, lamb_shift_scale
    Roles:    Relativistic corrections to hydrogen levels in exact Q
    Rules:    ΔE_fine = -α²/(2n³)·(n/(j+1/2) - 3/4); all Q arithmetic
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Fine structure constant                                    *)
(* ================================================================== *)

(** alpha = 1/137 (rational approximation, error ~0.03%) *)
Definition alpha_fs : Q := 1#137.

(** alpha^2 = 1/18769 *)
Definition alpha_fs_sq : Q := alpha_fs * alpha_fs.

Lemma alpha_fs_sq_value : alpha_fs_sq == 1#18769.
Proof. vm_compute. reflexivity. Qed.

(** alpha^4 = 1/18769^2 = 1/352275361 *)
Definition alpha_fs_4 : Q := alpha_fs_sq * alpha_fs_sq.

Lemma alpha_fs_4_value : alpha_fs_4 == 1#352275361.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part II: Fine structure correction for hydrogen                    *)
(* ================================================================== *)

(** Fine structure correction:
    ΔE_fine(n,j) = -E_n · α² / n · (n/(j+1/2) - 3/4)

    For hydrogen E_n = -1/(2n²), so:
    ΔE_fine(n,j) = -α² / (2n³) · (n/(j+1/2) - 3/4) *)

(** Correction factor f(n,j) = n/(j+1/2) - 3/4.
    j is half-integer, represent 2j as nat for exact Q. *)
Definition fine_factor (n : positive) (two_j : positive) : Q :=
  let nq := Zpos n # 1 in
  let jq := (Zpos two_j # 1) / 2 + (1#2) in
  nq / jq - (3#4).

(** For n=2, j=1/2 (2j=1): f = 2/(1/2+1/2) - 3/4 = 2/1 - 3/4 = 5/4 *)
Lemma fine_factor_2_half : fine_factor 2 1 == 5#4.
Proof. vm_compute. reflexivity. Qed.

(** For n=2, j=3/2 (2j=3): f = 2/(3/2+1/2) - 3/4 = 2/2 - 3/4 = 1/4 *)
Lemma fine_factor_2_threehalf : fine_factor 2 3 == 1#4.
Proof. vm_compute. reflexivity. Qed.

(** Full fine structure correction *)
Definition delta_E_fine (n : positive) (two_j : positive) : Q :=
  -(alpha_fs_sq) / (2 * (Zpos n # 1) * (Zpos n # 1) * (Zpos n # 1))
  * fine_factor n two_j.

(** For n=2, j=1/2: ΔE = -α²/16 · 5/4 = -5α²/64 = -5/1201216 *)
Lemma delta_E_2_half_value : delta_E_fine 2 1 == -(5#1201216).
Proof. vm_compute. reflexivity. Qed.

(** For n=2, j=3/2: ΔE = -α²/16 · 1/4 = -α²/64 = -1/1201216 *)
Lemma delta_E_2_threehalf_value : delta_E_fine 2 3 == -(1#1201216).
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  Part III: Fine structure splitting                                 *)
(* ================================================================== *)

(** Splitting between j=1/2 and j=3/2 at n=2:
    ΔE(j=1/2) - ΔE(j=3/2) = -5/1201216 + 1/1201216 = -4/1201216 = -1/300304 *)
Definition fine_splitting_n2 : Q :=
  delta_E_fine 2 1 - delta_E_fine 2 3.

Lemma fine_splitting_n2_value : fine_splitting_n2 == -(1#300304).
Proof. vm_compute. reflexivity. Qed.

(** Splitting is small: |ΔE| < 1/100000 *)
Lemma fine_splitting_small : -(fine_splitting_n2) < 1#100000.
Proof.
  assert (H: fine_splitting_n2 == -(1#300304)) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(* ================================================================== *)
(*  Part IV: Higher-order corrections (scale estimates)                *)
(* ================================================================== *)

(** Lamb shift scale: ~α⁵·m_e·c² ~ α³ × fine_structure
    α³ = 1/(137³) = 1/2571353. Negligible at our precision. *)
Definition alpha_cubed : Q := alpha_fs * alpha_fs * alpha_fs.

Lemma alpha_cubed_value : alpha_cubed == 1#2571353.
Proof. vm_compute. reflexivity. Qed.

(** Hyperfine structure scale: ~α⁴ = 1/352275361.
    Even smaller than fine structure. *)
Lemma hyperfine_negligible : alpha_fs_4 < 1#100000000.
Proof.
  assert (H: alpha_fs_4 == 1#352275361) by (vm_compute; reflexivity).
  rewrite H. lra.
Qed.

(** Fine structure for n=1, j=1/2 (ground state):
    ΔE = -α²/2 · (1/1 - 3/4) = -α²/2 · 1/4 = -α²/8 = -1/150152 *)
Lemma delta_E_1_half_value : delta_E_fine 1 1 == -(1#150152).
Proof. vm_compute. reflexivity. Qed.

(** Ratio of n=2 splitting to n=1 correction *)
Lemma fine_ratio_n2_n1 :
  fine_splitting_n2 / delta_E_fine 1 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.
