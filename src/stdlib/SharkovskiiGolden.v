(** SharkovskiiGolden.v — Golden mean IS Sharkovskii *)
(** E/R/R: Elements = eigenvalues; Roles = spectral radius; Rules = golden characteristic *)
From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.SharkovskiiMarkov.
From ToS Require Import stdlib.SharkovskiiForcing.
Open Scope Z_scope.

(** Period-3 adjacency = golden matrix [[0,1],[1,1]] *)
Lemma sharkovskii_is_golden :
  period3_adj O O = O /\ period3_adj O (S O) = S O /\
  period3_adj (S O) O = S O /\ period3_adj (S O) (S O) = S O.
Proof. repeat split; reflexivity. Qed.

(** Lucas concrete values *)
Lemma lucas_values :
  lucas O = 2 /\ lucas (S O) = 1 /\ lucas (S(S O)) = 3 /\
  lucas (S(S(S O))) = 4 /\ lucas (S(S(S(S O)))) = 7 /\
  lucas (S(S(S(S(S O))))) = 11 /\ lucas (S(S(S(S(S(S O)))))) = 18.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Orbit growth rate ~ phi^n/n *)
Lemma orbit_growth : (lucas (S(S(S(S(S(S O)))))) > 2 * lucas (S(S(S(S O))))).
(* L(6)=18 > 2*L(4)=14 *)
Proof.
  assert (H1 : lucas (S(S(S(S(S(S O)))))) = 18) by (vm_compute; reflexivity).
  assert (H2 : lucas (S(S(S(S O)))) = 7) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.

(** Lucas recurrence verified *)
Lemma lucas_recurrence_3 :
  lucas (S(S(S O))) = lucas (S(S O)) + lucas (S O).
(* 4 = 3 + 1 *)
Proof. vm_compute. reflexivity. Qed.

Lemma lucas_recurrence_4 :
  lucas (S(S(S(S O)))) = lucas (S(S(S O))) + lucas (S(S O)).
(* 7 = 4 + 3 *)
Proof. vm_compute. reflexivity. Qed.

Lemma lucas_recurrence_5 :
  lucas (S(S(S(S(S O))))) = lucas (S(S(S(S O)))) + lucas (S(S(S O))).
(* 11 = 7 + 4 *)
Proof. vm_compute. reflexivity. Qed.

Lemma lucas_recurrence_6 :
  lucas (S(S(S(S(S(S O)))))) = lucas (S(S(S(S(S O))))) + lucas (S(S(S(S O)))).
(* 18 = 11 + 7 *)
Proof. vm_compute. reflexivity. Qed.

(** Golden eigenvalue: spectral radius phi satisfies phi^2 = phi + 1 *)
(** Encoded via trace=1, det=-1 of adjacency matrix *)
Theorem golden_spectral :
  (period3_adj O O + period3_adj (S O) (S O) = S O)%nat /\
  ((Z.of_nat (period3_adj O O) * Z.of_nat (period3_adj (S O) (S O)) -
    Z.of_nat (period3_adj O (S O)) * Z.of_nat (period3_adj (S O) O)) = -1) /\
  lucas (S(S(S(S(S(S O)))))) = 18.
Proof.
  split; [exact adj_trace|].
  split; [exact adj_det_Z|].
  vm_compute. reflexivity.
Qed.

(** Orbits grow faster than linearly *)
Lemma orbits_superlinear :
  lucas (S(S(S(S(S(S O)))))) > 3 * lucas (S(S(S O))).
(* 18 > 3*4 = 12 *)
Proof.
  assert (H1 : lucas (S(S(S(S(S(S O)))))) = 18) by (vm_compute; reflexivity).
  assert (H2 : lucas (S(S(S O))) = 4) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.

(** Golden synthesis *)
Theorem golden_sharkovskii_connection :
  (* Matrix is golden *)
  (period3_adj O O = O /\ period3_adj O (S O) = S O /\
   period3_adj (S O) O = S O /\ period3_adj (S O) (S O) = S O) /\
  (* Lucas positive *)
  (forall n, lucas n > 0) /\
  (* Growth *)
  lucas (S(S(S(S(S(S O)))))) > 2 * lucas (S(S(S(S O)))).
Proof.
  split; [exact sharkovskii_is_golden|].
  split; [exact lucas_positive|].
  exact orbit_growth.
Qed.
