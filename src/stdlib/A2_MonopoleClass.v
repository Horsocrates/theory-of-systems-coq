From Stdlib Require Import QArith QArith_base Lia ZArith. From Stdlib Require Import Lqa.
Open Scope Q_scope.
Definition monopole_charge (n : Z) : Z := n.
Lemma dirac_quantization : forall n, monopole_charge n = n. Proof. reflexivity. Qed.
Definition magnetic_flux (n : Z) : Q := 2 * (22#7) * inject_Z n.
Lemma flux_unit : magnetic_flux 1 == 44 # 7. Proof. vm_compute. reflexivity. Qed.
Lemma flux_zero : magnetic_flux 0 == 0. Proof. vm_compute. reflexivity. Qed.
Theorem monopole_class : monopole_charge 1 = 1%Z /\ magnetic_flux 0 == 0.
Proof. split; [reflexivity | exact flux_zero]. Qed.
Definition a2_mono_count := 5%nat.
