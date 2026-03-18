(* ProcessPostNewtonian.v — 1PN effective potential *)
From Stdlib Require Import QArith QArith_base Lia ZArith. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessSchwarzschildRegge.
Open Scope Q_scope.
(** V_eff(r) = -M/r + L²/(2r²) - ML²/r³ *)
Definition V_eff (M L ell : Q) (k : nat) : Q :=
  let r := shell_radius ell k in
  -(M) / r + L*L / (2*r*r) - M*L*L / (r*r*r).
(** The -ML²/r³ term IS the 1PN correction (precession source) *)
Definition V_newton (M L ell : Q) (k : nat) : Q :=
  let r := shell_radius ell k in -(M) / r + L*L / (2*r*r).
Definition V_1pn_correction (M L ell : Q) (k : nat) : Q :=
  let r := shell_radius ell k in -(M*L*L) / (r*r*r).
Lemma V_decomposition_20 :
  V_eff 5 10 1 19 == V_newton 5 10 1 19 + V_1pn_correction 5 10 1 19.
Proof. unfold V_eff, V_newton, V_1pn_correction, shell_radius. simpl. field. Qed.
(** Concrete: M=5, L=10, ℓ=1 *)
Lemma V_1pn_at_20 : V_1pn_correction 5 10 1 19 == -(1#16).
Proof. unfold V_1pn_correction, shell_radius. simpl. field. Qed.
(** 1PN term negative → deeper potential → tighter orbits → precession *)
Lemma V_1pn_negative : V_1pn_correction 5 10 1 19 < 0.
Proof. rewrite V_1pn_at_20. lra. Qed.
Theorem post_newtonian :
  V_eff 5 10 1 19 == V_newton 5 10 1 19 + V_1pn_correction 5 10 1 19 /\
  V_1pn_correction 5 10 1 19 < 0.
Proof. split; [exact V_decomposition_20|exact V_1pn_negative]. Qed.
Definition pn_count := 7%nat.
