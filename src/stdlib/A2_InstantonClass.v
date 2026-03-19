From Stdlib Require Import QArith QArith_base Lia ZArith. From Stdlib Require Import Lqa.
Open Scope Q_scope.
Definition instanton_number (winding : Z) : Z := winding.
Lemma instanton_trivial : instanton_number 0 = 0%Z. Proof. reflexivity. Qed.
Lemma instanton_unit : instanton_number 1 = 1%Z. Proof. reflexivity. Qed.
Lemma instanton_anti : instanton_number (-1) = (-1)%Z. Proof. reflexivity. Qed.
Definition topological_charge (n : Z) : Q := inject_Z n.
Lemma charge_integer_0 : topological_charge 0 == 0. Proof. reflexivity. Qed.
Lemma charge_integer_1 : topological_charge 1 == 1. Proof. reflexivity. Qed.
Theorem instanton_class : instanton_number 0 = 0%Z /\ instanton_number 1 = 1%Z.
Proof. split; reflexivity. Qed.
Definition a2_inst_count := 6%nat.
