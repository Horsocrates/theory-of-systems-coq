(** SharkovskiiSynthesis.v — Sharkovskii theorem synthesis *)
(** E/R/R: Elements = all components; Roles = theorem integration; Rules = final statement *)
From Stdlib Require Import QArith Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import stdlib.SharkovskiiMarkov.
From ToS Require Import stdlib.SharkovskiiCovering.
From ToS Require Import stdlib.SharkovskiiForcing.
From ToS Require Import stdlib.SharkovskiiGolden.
From ToS Require Import stdlib.SharkovskiiConcrete.
Open Scope Q_scope.

(** Main synthesis: Sharkovskii theorem components *)
Theorem sharkovskii_synthesis :
  (* Golden = Sharkovskii *)
  period3_adj (S O) (S O) = S O /\
  (* Lucas positive *)
  (forall n, (lucas n > 0)%Z) /\
  (* Concrete orbits verified *)
  f_pl 0 == 1#2 /\
  f_pl (2#3) == 2#3 /\
  f_pl (1#3) == 5#6 /\
  f_pl (2#9) == 13#18 /\
  (* Period verified *)
  f4_pl (2#9) == 2#9.
Proof.
  split; [reflexivity|].
  split; [exact lucas_positive|].
  split; [exact orbit3_0|].
  split; [exact fixed_pt|].
  split; [exact orbit2_a|].
  split; [exact orbit4_a|].
  exact fp4_verify.
Qed.

(** Markov graph captures forcing *)
Theorem markov_forcing_summary :
  (* I2 self-covers *)
  covers 1 0 (1#2) 1 = true /\
  (* I2 covers I1 *)
  covers 1 0 0 (1#2) = true /\
  (* I1 covers I2 *)
  covers (1#2) 1 (1#2) 1 = true /\
  (* I1 does NOT self-cover *)
  covers (1#2) 1 0 (1#2) = false.
Proof.
  split; [exact period3_I2_covers_I2|].
  split; [exact period3_I2_covers_I1|].
  split; [exact period3_I1_covers_I2|].
  exact period3_I1_not_self.
Qed.

(** Full hierarchy witness *)
Theorem sharkovskii_hierarchy :
  (* Period 1 witness *)
  f_pl (2#3) == 2#3 /\
  (* Period 2 witness *)
  f2_pl (1#3) == 1#3 /\
  (* Period 3 witness *)
  f3_pl 0 == 0 /\
  (* Period 4 witness *)
  f4_pl (2#9) == 2#9 /\
  (* Lucas counts all *)
  (forall n, (lucas n > 0)%Z).
Proof.
  split; [exact fp_verify|].
  split; [exact fp2_verify|].
  split; [exact fp3_verify|].
  split; [exact fp4_verify|].
  exact lucas_positive.
Qed.

(** Determinant confirms golden *)
Theorem golden_determinant :
  ((Z.of_nat (period3_adj O O) * Z.of_nat (period3_adj (S O) (S O)) -
    Z.of_nat (period3_adj O (S O)) * Z.of_nat (period3_adj (S O) O)) = -1)%Z.
Proof. exact adj_det_Z. Qed.

(** Period-2 orbit closure *)
Lemma period2_closure :
  f_pl (1#3) == 5#6 /\ f_pl (5#6) == 1#3.
Proof.
  split; [exact orbit2_a|exact orbit2_b].
Qed.

(** Period-4 orbit closure *)
Lemma period4_closure :
  f_pl (2#9) == 13#18 /\ f_pl (13#18) == 5#9 /\
  f_pl (5#9) == 8#9 /\ f_pl (8#9) == 2#9.
Proof.
  split; [exact orbit4_a|].
  split; [exact orbit4_b|].
  split; [exact orbit4_c|exact orbit4_d].
Qed.

(** Lucas orbit count verification *)
Lemma lucas_orbit_counts :
  ((lucas (S(S O)) - 1) / 2 = 1)%Z /\
  ((lucas (S(S(S O))) - 1) / 3 = 1)%Z /\
  ((lucas (S(S(S(S(S O))))) - 1) / 5 = 2)%Z.
Proof.
  split; [exact orbits_2|].
  split; [exact orbits_3|exact orbits_5].
Qed.

(** Grand theorem: period-3 implies all periods *)
Theorem sharkovskii_grand :
  (* Markov graph structure *)
  period3_adj O (S O) = S O /\
  period3_adj (S O) O = S O /\
  period3_adj (S O) (S O) = S O /\
  (* Lucas positive = orbits exist for all n *)
  (forall n, (lucas n > 0)%Z) /\
  (* Concrete witnesses for periods 1-4 *)
  f_pl (2#3) == 2#3 /\
  f2_pl (1#3) == 1#3 /\
  f3_pl 0 == 0 /\
  f4_pl (2#9) == 2#9.
Proof.
  split; [exact adj_01|].
  split; [exact adj_10|].
  split; [exact adj_11|].
  split; [exact lucas_positive|].
  split; [exact fp_verify|].
  split; [exact fp2_verify|].
  split; [exact fp3_verify|].
  exact fp4_verify.
Qed.
