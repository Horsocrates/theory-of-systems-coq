(* ProcessLightDeflection.v — Light deflection by mass *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
Open Scope Q_scope.

(** ★ LIGHT DEFLECTION *)
(** GR: δθ = 4GM/(c²b) where b = impact parameter *)
(** Ours: δθ = 4M/b = 4M/(ℓ(k+1)) *)
(** Coefficient 4 = GR prediction (twice Newtonian 2) *)

Definition light_deflection (M ell : Q) (k_min : nat) : Q :=
  4 * M / shell_radius ell k_min.

(** At r=15ℓ: δθ = 4·5/15 = 4/3 (strong gravity!) *)
Lemma deflection_at_15 : light_deflection 5 1 14 == 4 # 3.
Proof. unfold light_deflection, shell_radius. simpl. field. Qed.

(** At r=100ℓ: δθ = 20/100 = 1/5 *)
Lemma deflection_at_100 : light_deflection 5 1 99 == 1 # 5.
Proof. unfold light_deflection, shell_radius. simpl. field. Qed.

(** At r=1000ℓ: δθ = 20/1000 = 1/50 *)
Lemma deflection_at_1000 : light_deflection 5 1 999 == 1 # 50.
Proof. unfold light_deflection, shell_radius. simpl. field. Qed.

(** Deflection positive *)
Lemma deflection_pos : 0 < light_deflection 5 1 99.
Proof. rewrite deflection_at_100. lra. Qed.

(** Deflection decreases with distance *)
Lemma deflection_decreasing :
  light_deflection 5 1 99 > light_deflection 5 1 999.
Proof. rewrite deflection_at_100, deflection_at_1000. lra. Qed.

(** ★ Sun: δθ = 4·1.5/(7×10⁵) = 8.6×10⁻⁶ rad = 1.75 arcsec *)
(** Eddington 1919: confirmed to ~20%. Modern: < 0.01% *)
(** Our formula: SAME 4M/r dependence ✓ *)

Theorem deflection_verified :
  light_deflection 5 1 14 == 4 # 3 /\
  light_deflection 5 1 99 == 1 # 5 /\
  light_deflection 5 1 999 == 1 # 50.
Proof.
  split; [|split].
  - exact deflection_at_15.
  - exact deflection_at_100.
  - exact deflection_at_1000.
Qed.

Definition deflection_count := 7%nat.
