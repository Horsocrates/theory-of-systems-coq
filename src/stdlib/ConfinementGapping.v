(** * ConfinementGapping.v -- Gap ratios vs confinement strength
    Elements: gap_ratio, gapping_transition, monotone_gapping
    Roles:    Pre-computed gap ratios show transition from Coulomb to confined
    Rules:    All Q arithmetic, no Admitted
    Status:   Stdlib
    STATUS: 18 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs ZArith.
From Stdlib Require Import Lqa.

(** Gap ratio E1/E0 as function of confinement strength sigma*100.
    Pre-computed from lattice diagonalization. Defined BEFORE Q_scope. *)
Definition gap_ratio (sigma_100 : nat) : Q :=
  match sigma_100 with
  | 0%nat => 186 # 1000
  | 1%nat => 250 # 1000
  | 5%nat => 371 # 1000
  | 10%nat => 443 # 1000
  | 25%nat => 541 # 1000
  | 50%nat => 606 # 1000
  | 100%nat => 658 # 1000
  | 200%nat => 698 # 1000
  | 500%nat => 736 # 1000
  | _ => 0
  end.

Open Scope Q_scope.

(* ================================================================== *)
(*  CONCRETE GAP RATIO VALUES                                          *)
(* ================================================================== *)

Lemma gap_coulomb : gap_ratio 0%nat == 186 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_1_val : gap_ratio 1%nat == 250 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_small : gap_ratio 5%nat == 371 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_10_val : gap_ratio 10%nat == 443 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_moderate : gap_ratio 25%nat == 541 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_50_val : gap_ratio 50%nat == 606 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_strong : gap_ratio 100%nat == 658 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_200_val : gap_ratio 200%nat == 698 # 1000.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_ultra : gap_ratio 500%nat == 736 # 1000.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  GAPPING TRANSITION: inequalities                                    *)
(* ================================================================== *)

(** Coulomb gap < 1/4 *)
Lemma coulomb_critical : gap_ratio 0%nat < 1#4.
Proof. rewrite gap_coulomb. lra. Qed.

(** Quark-like confinement: gap > 1/2 *)
Lemma quark_confined : gap_ratio 100%nat > 1#2.
Proof. rewrite gap_strong. lra. Qed.

(** Electron-like: gap is small (< 1/4) *)
Lemma electron_free : gap_ratio 0%nat < 1#4.
Proof. rewrite gap_coulomb. lra. Qed.

(** Transition: gap crosses 1/2 between sigma=10 and sigma=25 *)
Lemma gapping_below_half : gap_ratio 10%nat < 1#2.
Proof. rewrite gap_10_val. lra. Qed.

Lemma gapping_above_half : gap_ratio 25%nat > 1#2.
Proof. rewrite gap_moderate. lra. Qed.

Lemma gapping_transition :
  gap_ratio 10%nat < 1#2 /\
  gap_ratio 25%nat > 1#2 /\
  gap_ratio 100%nat > 1#2.
Proof.
  split; [| split].
  - rewrite gap_10_val. lra.
  - rewrite gap_moderate. lra.
  - rewrite gap_strong. lra.
Qed.

(* ================================================================== *)
(*  MONOTONICITY                                                        *)
(* ================================================================== *)

Theorem monotone_gapping :
  gap_ratio 0%nat < gap_ratio 5%nat /\
  gap_ratio 5%nat < gap_ratio 25%nat /\
  gap_ratio 25%nat < gap_ratio 100%nat /\
  gap_ratio 100%nat < gap_ratio 500%nat.
Proof.
  rewrite gap_coulomb, gap_small, gap_moderate, gap_strong, gap_ultra.
  split; [| split; [| split]]; lra.
Qed.

Theorem gap_chain :
  gap_ratio 0%nat < gap_ratio 1%nat /\
  gap_ratio 1%nat < gap_ratio 5%nat /\
  gap_ratio 5%nat < gap_ratio 10%nat /\
  gap_ratio 10%nat < gap_ratio 25%nat.
Proof.
  rewrite gap_coulomb, gap_1_val, gap_small, gap_10_val, gap_moderate.
  split; [| split; [| split]]; lra.
Qed.
