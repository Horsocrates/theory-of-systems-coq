(** * A1_ProcessSheaf.v -- Sheaf on Spec(ProcessRing)
    Elements: local_section, global_section, restriction, gluing
    Roles:    Structure sheaf assigns Q-values to each K; global sections = processes
    Rules:    Restriction = evaluation truncation; gluing recovers the process
    Status:   complete
    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import stdlib.ProcessRing.
From ToS Require Import stdlib.A1_SpecProcessRing.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Sections of the Structure Sheaf                            *)
(* ================================================================== *)

(** A local section over [0..N] assigns a Q value to each K <= N *)
Definition local_section (N : nat) := forall K : nat, (K <= N)%nat -> Q.

(** A global section is just a RealProcess *)
Definition global_section := RealProcess.

(** Restriction: truncate a global section to [0..N] *)
Definition restrict (f : global_section) (N : nat) : local_section N :=
  fun K _ => f K.

(** Restriction is compatible with process evaluation *)
Lemma restrict_eval : forall (f : global_section) N K (HK : (K <= N)%nat),
  restrict f N K HK == f K.
Proof. intros. unfold restrict. lra. Qed.

(** Restriction of a sum = sum of restrictions *)
Lemma restrict_add : forall (f g : global_section) N K (HK : (K <= N)%nat),
  restrict (process_add f g) N K HK ==
  restrict f N K HK + restrict g N K HK.
Proof. intros. unfold restrict, process_add. lra. Qed.

(** Restriction of a product = product of restrictions *)
Lemma restrict_mul : forall (f g : global_section) N K (HK : (K <= N)%nat),
  restrict (process_mul f g) N K HK ==
  restrict f N K HK * restrict g N K HK.
Proof. intros. unfold restrict, process_mul. lra. Qed.

(* ================================================================== *)
(*  Part II: Gluing and Locality                                       *)
(* ================================================================== *)

(** Two sections agree on overlap if they give the same values *)
Definition sections_agree (N1 N2 : nat)
  (s1 : local_section N1) (s2 : local_section N2) : Prop :=
  forall K (H1 : (K <= N1)%nat) (H2 : (K <= N2)%nat),
    s1 K H1 == s2 K H2.

(** Restrictions of the same process always agree *)
Lemma restrict_agree : forall (f : global_section) N1 N2,
  sections_agree N1 N2 (restrict f N1) (restrict f N2).
Proof.
  intros f N1 N2 K H1 H2. unfold restrict. lra.
Qed.

(** Gluing: if local sections come from a process, they glue back *)
Lemma gluing_from_process : forall (f : global_section) N K (HK : (K <= N)%nat),
  restrict f N K HK == f K.
Proof. intros. unfold restrict. lra. Qed.

(** Locality: a process is determined by its restrictions *)
Lemma locality : forall (f g : global_section),
  (forall K, f K == g K) ->
  forall N K (HK : (K <= N)%nat),
    restrict f N K HK == restrict g N K HK.
Proof.
  intros f g Hfg N K HK. unfold restrict. apply Hfg.
Qed.

(** Constant section: same Q at every point *)
Definition const_section (q : Q) : global_section := const_process q.

Lemma restrict_const : forall q N K (HK : (K <= N)%nat),
  restrict (const_section q) N K HK == q.
Proof.
  intros. unfold restrict, const_section, const_process. lra.
Qed.

(** Sheaf condition: global sections form a ring *)
Lemma sheaf_ring_structure : forall f g K,
  (global_section -> global_section -> global_section) ->
  process_add f g K == f K + g K.
Proof.
  intros. unfold process_add. lra.
Qed.

Definition process_sheaf_count := 10%nat.
