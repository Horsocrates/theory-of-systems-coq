From Stdlib Require Import QArith QArith_base Lia. From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
Open Scope Q_scope.
Definition polyakov_loop (beta : Q) : Q :=
  if Qle_bool beta 2 then 0 else 1 - 2 / beta.
Lemma polyakov_confined : polyakov_loop 1 == 0.
Proof. unfold polyakov_loop. simpl. reflexivity. Qed.
Lemma polyakov_at_2 : polyakov_loop 2 == 0.
Proof. unfold polyakov_loop. simpl. reflexivity. Qed.
Lemma polyakov_at_4 : polyakov_loop 4 == 1 # 2.
Proof. unfold polyakov_loop. simpl. field. Qed.
Lemma polyakov_deconfined : 0 < polyakov_loop 4.
Proof. rewrite polyakov_at_4. lra. Qed.
Theorem phase_diagram : polyakov_loop 1 == 0 /\ 0 < polyakov_loop 4.
Proof. split; [exact polyakov_confined | exact polyakov_deconfined]. Qed.
Definition t2_phase_count := 5%nat.
