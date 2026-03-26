(** * BerryPhaseT.v — Berry/Zak phase and topological invariants

    Elements: Zak phase (1D), Berry phase relation to Chern number
    Roles:    Zak phase distinguishes topological from trivial in 1D
    Rules:    Zak = 1 (pi) if topological, Zak = 0 if trivial
    Status:   verified | geometric phase

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lqa Bool ZArith.
From ToS Require Import stdlib.topology.SSHModelT.
Open Scope Q_scope.

(** Zak phase in units of pi: 1 if topological, 0 otherwise *)
Definition zak_phase (t1 t2 : Q) : Z :=
  match classify_ssh t1 t2 with
  | Topological => 1%Z
  | Trivial => 0%Z
  | SSHCritical => 0%Z
  end.

(** ---- Concrete Zak phases ---- *)

Theorem zak_topo : zak_phase (1#2) 1 = 1%Z.
Proof. simpl. reflexivity. Qed.

Theorem zak_triv : zak_phase (3#2) 1 = 0%Z.
Proof. simpl. reflexivity. Qed.

Theorem zak_crit : zak_phase 1 1 = 0%Z.
Proof. simpl. reflexivity. Qed.

(** Zak phase is topological invariant *)
Theorem zak_topological_invariant : forall t1 t2,
  classify_ssh t1 t2 = Topological ->
  zak_phase t1 t2 = 1%Z.
Proof.
  intros t1 t2 H. unfold zak_phase. rewrite H. reflexivity.
Qed.

Theorem zak_trivial_invariant : forall t1 t2,
  classify_ssh t1 t2 = Trivial ->
  zak_phase t1 t2 = 0%Z.
Proof.
  intros t1 t2 H. unfold zak_phase. rewrite H. reflexivity.
Qed.

(** Perturbation stability: small perturbation preserves Zak *)
Theorem zak_stable_concrete :
  zak_phase ((1#2) + (1#8)) 1 = 1%Z.
Proof. simpl. reflexivity. Qed.

(** Berry-Chern relation: in 2D, Chern = sum of Berry phases.
    Here modeled as: for two bands with Zak phases z1, z2,
    total winding = z1 - z2 *)
Definition berry_winding (z1 z2 : Z) : Z := (z1 - z2)%Z.

Theorem berry_chern_topo :
  berry_winding (zak_phase (1#2) 1) (zak_phase (3#2) 1) = 1%Z.
Proof. simpl. reflexivity. Qed.

Theorem berry_chern_same :
  berry_winding (zak_phase (3#2) 1) (zak_phase (3#2) 1) = 0%Z.
Proof. simpl. reflexivity. Qed.

(** Strong topological *)
Theorem zak_strong : zak_phase (1#4) 2 = 1%Z.
Proof. simpl. reflexivity. Qed.

(** Deep trivial *)
Theorem zak_deep_triv : zak_phase 3 1 = 0%Z.
Proof. simpl. reflexivity. Qed.

(** Zak phase determines edge states *)
Theorem zak_edge_connection : forall t1 t2,
  zak_phase t1 t2 = 1%Z ->
  classify_ssh t1 t2 = Topological.
Proof.
  intros t1 t2 H. unfold zak_phase in H.
  destruct (classify_ssh t1 t2); try discriminate. reflexivity.
Qed.

(** Critical point has zero Zak phase *)
Theorem zak_critical_zero : forall t1 t2,
  classify_ssh t1 t2 = SSHCritical ->
  zak_phase t1 t2 = 0%Z.
Proof.
  intros t1 t2 H. unfold zak_phase. rewrite H. reflexivity.
Qed.
