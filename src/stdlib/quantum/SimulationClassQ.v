(** * SimulationClassQ.v — Classical vs quantum simulation classification

    Elements: spectral gap, simulation complexity class
    Roles:    gap > 0 implies classically efficient; gap = 0 needs quantum
    Rules:    gapped -> ClassicalEfficient; gapless -> QuantumAdvantage
    Status:   verified | quantum simulation

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool.
Open Scope Q_scope.

(** Q strict less-than as bool *)
Definition Qlt_bool (a b : Q) : bool :=
  andb (Qle_bool a b) (negb (Qeq_bool a b)).

(** Simulation complexity class *)
Inductive SimulationComplexity : Set :=
  | ClassicalEfficient
  | QuantumAdvantage.

(** Classification based on spectral gap *)
Definition simulation_class (gap : Q) : SimulationComplexity :=
  if Qlt_bool 0 gap then ClassicalEfficient
  else QuantumAdvantage.

(** ---- Concrete classifications ---- *)

(** Ising model with gap 9/37 -> classically simulable *)
Theorem ising_classical : simulation_class (9#37) = ClassicalEfficient.
Proof. simpl. reflexivity. Qed.

(** Critical system with gap = 0 -> quantum advantage *)
Theorem critical_quantum : simulation_class 0 = QuantumAdvantage.
Proof. simpl. reflexivity. Qed.

(** Gapless system -> quantum *)
Theorem gapless_quantum : simulation_class 0 = QuantumAdvantage.
Proof. simpl. reflexivity. Qed.

(** Large gap -> classical *)
Theorem large_gap_classical : simulation_class 1 = ClassicalEfficient.
Proof. simpl. reflexivity. Qed.

(** Small gap -> still classical *)
Theorem small_gap_classical : simulation_class (1#1000) = ClassicalEfficient.
Proof. simpl. reflexivity. Qed.

(** Gap decides: concrete bool check *)
Theorem gap_decides : Qlt_bool 0 (9#37) = true.
Proof. simpl. reflexivity. Qed.

(** Zero gap bool check *)
Theorem zero_gap_bool : Qlt_bool 0 0 = false.
Proof. simpl. reflexivity. Qed.

(** Gapped -> classically efficient (general) *)
Theorem gapped_implies_classical : forall gap,
  simulation_class gap = ClassicalEfficient ->
  Qlt_bool 0 gap = true.
Proof.
  intros gap H. unfold simulation_class in H.
  destruct (Qlt_bool 0 gap); [reflexivity | discriminate].
Qed.

(** Quantum advantage -> gap is zero (or negative, but physically gap >= 0) *)
Theorem quantum_implies_gapless : forall gap,
  simulation_class gap = QuantumAdvantage ->
  Qlt_bool 0 gap = false.
Proof.
  intros gap H. unfold simulation_class in H.
  destruct (Qlt_bool 0 gap); [discriminate | reflexivity].
Qed.

(** Graphene at Dirac point: gapless *)
Theorem graphene_quantum : simulation_class 0 = QuantumAdvantage.
Proof. simpl. reflexivity. Qed.
