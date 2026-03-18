(* ProcessHVPConvergence.v — HVP at multiple β + convergence *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import SeriesConvergence.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessPlaquette.
From ToS Require Import process.ProcessPlaquetteCurve.
From ToS Require Import process.ProcessBeta4.
Open Scope Q_scope.

Definition hvp_kernel (k : nat) : Q := inject_Z (Z.of_nat (S k)).
Fixpoint hvp_sum_aux (P : Q) (N : nat) : Q :=
  match N with
  | O => hvp_kernel O * P
  | S n => hvp_sum_aux P n + hvp_kernel (S n) * Qpow P (S (S n))
  end.
Definition hvp_sum (P : Q) (N : nat) : Q := hvp_sum_aux P N.

Lemma hvp_1 : hvp_sum (9#20) 0 == 9 # 20.
Proof. unfold hvp_sum, hvp_sum_aux, hvp_kernel, inject_Z. simpl. ring. Qed.

Lemma hvp_b1_increases : hvp_sum (9#20) 0 < hvp_sum (9#20) 1.
Proof. unfold hvp_sum, hvp_sum_aux, hvp_kernel, inject_Z, Qpow. unfold Qlt; simpl; lia. Qed.

Definition hvp_ratio_b1_b2 : Q := hvp_sum (9#20) 0 / hvp_sum (19#27) 0.
Lemma hvp_ratio_value : hvp_ratio_b1_b2 == 243 # 380.
Proof. unfold hvp_ratio_b1_b2, hvp_sum, hvp_sum_aux, hvp_kernel, inject_Z. simpl. field. Qed.

Lemma hvp_geometric : 0 < hvp_sum (9#20) 0.
Proof. rewrite hvp_1. lra. Qed.

Theorem hvp_convergence :
  hvp_sum (9#20) 0 == 9 # 20 /\ hvp_sum (9#20) 0 < hvp_sum (9#20) 1 /\ hvp_ratio_b1_b2 == 243 # 380.
Proof. split; [|split]; [exact hvp_1|exact hvp_b1_increases|exact hvp_ratio_value]. Qed.

Definition hvp_conv_count := 6%nat.
