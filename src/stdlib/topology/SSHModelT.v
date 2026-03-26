(** * SSHModelT.v — Su-Schrieffer-Heeger model as process

    Elements: hopping amplitudes t1, t2; SSH Hamiltonian matrix entries
    Roles:    competition between t1 and t2 determines topological phase
    Rules:    t1 < t2 -> Topological; t1 > t2 -> Trivial; t1 = t2 -> Critical
    Status:   verified | 1D topological insulator

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool.
Open Scope Q_scope.

(** Q strict less-than as bool *)
Definition Qlt_bool (a b : Q) : bool :=
  andb (Qle_bool a b) (negb (Qeq_bool a b)).

(** SSH topological phases *)
Inductive SSHPhase : Set :=
  | Topological
  | Trivial
  | SSHCritical.

(** Phase classification from hopping amplitudes *)
Definition classify_ssh (t1 t2 : Q) : SSHPhase :=
  if Qlt_bool t1 t2 then Topological
  else if Qlt_bool t2 t1 then Trivial
  else SSHCritical.

(** Energy gap *)
Definition ssh_gap (t1 t2 : Q) : Q := Qabs (t1 - t2).

(** ---- Concrete classification ---- *)

Theorem ssh_topo : classify_ssh (1#2) 1 = Topological.
Proof. simpl. reflexivity. Qed.

Theorem ssh_triv : classify_ssh (3#2) 1 = Trivial.
Proof. simpl. reflexivity. Qed.

Theorem ssh_crit : classify_ssh 1 1 = SSHCritical.
Proof. simpl. reflexivity. Qed.

(** ---- Gap calculations (split Qabs) ---- *)

Lemma gap_topo_val : (1#2) - 1 == -(1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma gap_topo_abs : Qabs (-(1#2)) == 1#2.
Proof.
  unfold Qabs. simpl. vm_compute. reflexivity.
Qed.

Theorem gap_topo : ssh_gap (1#2) 1 == 1#2.
Proof.
  unfold ssh_gap.
  rewrite gap_topo_val. apply gap_topo_abs.
Qed.

Lemma gap_triv_val : (3#2) - 1 == 1#2.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_triv_abs : Qabs (1#2) == 1#2.
Proof.
  unfold Qabs. simpl. vm_compute. reflexivity.
Qed.

Theorem gap_triv : ssh_gap (3#2) 1 == 1#2.
Proof.
  unfold ssh_gap.
  rewrite gap_triv_val. apply gap_triv_abs.
Qed.

Theorem gap_crit : ssh_gap 1 1 == 0.
Proof.
  unfold ssh_gap.
  assert (H: 1 - 1 == 0) by (vm_compute; reflexivity).
  rewrite H.
  unfold Qabs. simpl. vm_compute. reflexivity.
Qed.

(** Same gap but different phases *)
Theorem same_gap_diff_phase :
  ssh_gap (1#2) 1 == ssh_gap (3#2) 1.
Proof.
  rewrite gap_topo. rewrite gap_triv. vm_compute. reflexivity.
Qed.

(** ---- SSH Hamiltonian matrix entry ---- *)

(** 4x4 SSH Hamiltonian for 2-cell chain: H_{ij} *)
Definition ssh_entry (t1 t2 : Q) (i j : nat) : Q :=
  match i, j with
  | O, S O => t1
  | S O, O => t1
  | S O, S (S O) => t2
  | S (S O), S O => t2
  | S (S O), S (S (S O)) => t1
  | S (S (S O)), S (S O) => t1
  | _, _ => 0
  end.

Theorem ssh_entry_01 : ssh_entry (1#2) 1 0%nat 1%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

Theorem ssh_entry_12 : ssh_entry (1#2) 1 1%nat 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

Theorem ssh_entry_diag : ssh_entry (1#2) 1 0%nat 0%nat == 0.
Proof. vm_compute. reflexivity. Qed.

Theorem ssh_hermitian : forall t1 t2 i j,
  ssh_entry t1 t2 i j == ssh_entry t1 t2 j i.
Proof.
  intros t1 t2 i j.
  destruct i as [|[|[|[|i']]]]; destruct j as [|[|[|[|j']]]];
    simpl; try apply Qeq_refl.
Qed.

(** Entry 23 = t1 *)
Theorem ssh_entry_23 : ssh_entry (1#2) 1 2%nat 3%nat == 1#2.
Proof. vm_compute. reflexivity. Qed.

(** Trace is zero (SSH is off-diagonal) *)
Theorem ssh_trace_zero :
  ssh_entry (1#2) 1 0%nat 0%nat +
  ssh_entry (1#2) 1 1%nat 1%nat +
  ssh_entry (1#2) 1 2%nat 2%nat +
  ssh_entry (1#2) 1 3%nat 3%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(** Phase boundary: classify at exactly t1=t2 *)
Theorem ssh_boundary : classify_ssh (1#1) (1#1) = SSHCritical.
Proof. simpl. reflexivity. Qed.
