(* ProcessIntegration.v — Integration as process *)
From Stdlib Require Import QArith QArith_base Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.

Fixpoint riemann_sum_01 (f : Q -> Q) (K : nat) (i : nat) : Q :=
  match i with
  | O => f 0 / inject_Z (Z.of_nat (S K))
  | S i' => riemann_sum_01 f K i' +
             f (inject_Z (Z.of_nat i) / inject_Z (Z.of_nat (S K))) /
             inject_Z (Z.of_nat (S K))
  end.

Definition process_integral_01 (f : Q -> Q) (K : nat) : Q :=
  riemann_sum_01 f K K.

Lemma integral_const_0 : process_integral_01 (fun _ => 1) 0 == 1.
Proof. unfold process_integral_01, riemann_sum_01, inject_Z. vm_compute. reflexivity. Qed.

Lemma integral_const_1 : process_integral_01 (fun _ => 1) 1 == 1.
Proof. unfold process_integral_01, riemann_sum_01, inject_Z. vm_compute. reflexivity. Qed.

Lemma integral_zero_0 : process_integral_01 (fun _ => 0) 0 == 0.
Proof. unfold process_integral_01, riemann_sum_01, inject_Z. vm_compute. reflexivity. Qed.

Lemma integral_const_2 : process_integral_01 (fun _ => 1) 2 == 1.
Proof. unfold process_integral_01, riemann_sum_01, inject_Z. vm_compute. reflexivity. Qed.

Lemma integral_two : process_integral_01 (fun _ => 2) 0 == 2.
Proof. unfold process_integral_01, riemann_sum_01, inject_Z. vm_compute. reflexivity. Qed.

Theorem integration_foundation :
  process_integral_01 (fun _ => 1) 0 == 1 /\
  process_integral_01 (fun _ => 1) 1 == 1 /\
  process_integral_01 (fun _ => 0) 0 == 0.
Proof.
  split; [|split].
  - exact integral_const_0.
  - exact integral_const_1.
  - exact integral_zero_0.
Qed.

Definition integration_count := 5%nat.
