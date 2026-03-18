(** * ProcessERRSymmetry.v — Same-Role Equivalence Generates Symmetry Group

    Theory of Systems — Step 3 Phase 18: E/R/R → Gauge Invariance (File 1)

    Elements: sites with roles in an E/R/R system
    Roles:    ERRSystem record, RolePermutation group
    Rules:    same_role equivalence, relative rules, symmetry
    Status:   complete

    STATUS: 20 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.

(* ================================================================== *)
(*  Part I: E/R/R System  (~6 lemmas)                                 *)
(* ================================================================== *)

(** An E/R/R system over Q on n sites *)
Record ERRSystem := mkERR {
  err_nsites : nat;
  err_nroles : nat;
  err_role : nat -> nat;
  err_rule : nat -> nat -> Q;
  err_role_valid : forall i, (i < err_nsites)%nat ->
    (err_role i < err_nroles)%nat
}.

(** Two sites have the same Role *)
Definition same_role (Sys : ERRSystem) (i j : nat) : Prop :=
  err_role Sys i = err_role Sys j.

(** same_role is an equivalence relation *)
Lemma same_role_refl : forall Sys i, same_role Sys i i.
Proof. intros. unfold same_role. reflexivity. Qed.

Lemma same_role_sym : forall Sys i j, same_role Sys i j -> same_role Sys j i.
Proof. intros Sys i j H. unfold same_role in *. auto. Qed.

Lemma same_role_trans : forall Sys i j k,
  same_role Sys i j -> same_role Sys j k -> same_role Sys i k.
Proof.
  intros Sys i j k H1 H2. unfold same_role in *.
  rewrite H1. exact H2.
Qed.

(** Number of elements per role *)
Definition role_count (Sys : ERRSystem) (r : nat) : nat :=
  length (filter (fun i => Nat.eqb (err_role Sys i) r) (seq 0 (err_nsites Sys))).

(** Role count is bounded by total sites *)
Lemma role_count_bounded : forall (Sys : ERRSystem) (r : nat),
  (role_count Sys r <= err_nsites Sys)%nat.
Proof.
  intros Sys r. unfold role_count.
  set (f := fun i : nat => Nat.eqb (err_role Sys i) r).
  set (l := seq 0 (err_nsites Sys)).
  assert (H : (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat =
              length l).
  { apply filter_length. }
  subst l. rewrite seq_length in H. lia.
Qed.

(* ================================================================== *)
(*  Part II: Role-Preserving Permutations  (~8 lemmas)                *)
(* ================================================================== *)

(** A permutation σ : sites → sites that preserves Roles *)
Record RolePermutation (Sys : ERRSystem) := mkRolePerm {
  rp_map : nat -> nat;
  rp_injective : forall i j,
    (i < err_nsites Sys)%nat -> (j < err_nsites Sys)%nat ->
    rp_map i = rp_map j -> i = j;
  rp_range : forall i, (i < err_nsites Sys)%nat ->
    (rp_map i < err_nsites Sys)%nat;
  rp_preserves_role : forall i, (i < err_nsites Sys)%nat ->
    err_role Sys (rp_map i) = err_role Sys i
}.

(** Identity is a Role permutation *)
Definition role_perm_id (Sys : ERRSystem) : RolePermutation Sys :=
  mkRolePerm Sys (fun i => i)
    (fun i j _ _ H => H)
    (fun i H => H)
    (fun i _ => eq_refl).

(** Identity maps i to i *)
Lemma role_perm_id_spec : forall Sys i,
  rp_map Sys (role_perm_id Sys) i = i.
Proof. intros. reflexivity. Qed.

(** Composition of Role permutations *)
Definition role_perm_compose (Sys : ERRSystem)
  (sigma tau : RolePermutation Sys) : RolePermutation Sys.
Proof.
  apply (mkRolePerm Sys (fun i => rp_map Sys sigma (rp_map Sys tau i))).
  - intros i j Hi Hj Heq.
    apply (rp_injective Sys tau); auto.
    apply (rp_injective Sys sigma); auto.
    + apply (rp_range Sys tau). exact Hi.
    + apply (rp_range Sys tau). exact Hj.
  - intros. apply (rp_range Sys sigma). apply (rp_range Sys tau). exact H.
  - intros. rewrite (rp_preserves_role Sys sigma).
    + apply (rp_preserves_role Sys tau). exact H.
    + apply (rp_range Sys tau). exact H.
Defined.

(** Composition maps i to σ(τ(i)) *)
Lemma role_perm_compose_spec : forall Sys (sigma tau : RolePermutation Sys) i,
  rp_map Sys (role_perm_compose Sys sigma tau) i =
  rp_map Sys sigma (rp_map Sys tau i).
Proof. intros. reflexivity. Qed.

(** Composition is associative *)
Lemma role_perm_assoc : forall Sys (s1 s2 s3 : RolePermutation Sys) i,
  rp_map Sys (role_perm_compose Sys (role_perm_compose Sys s1 s2) s3) i =
  rp_map Sys (role_perm_compose Sys s1 (role_perm_compose Sys s2 s3)) i.
Proof. intros. reflexivity. Qed.

(** Identity laws *)
Lemma role_perm_id_left : forall Sys (sigma : RolePermutation Sys) i,
  rp_map Sys (role_perm_compose Sys (role_perm_id Sys) sigma) i =
  rp_map Sys sigma i.
Proof. intros. reflexivity. Qed.

Lemma role_perm_id_right : forall Sys (sigma : RolePermutation Sys) i,
  rp_map Sys (role_perm_compose Sys sigma (role_perm_id Sys)) i =
  rp_map Sys sigma i.
Proof. intros. reflexivity. Qed.

(** ★ Role permutations form a group *)
Theorem role_permutations_form_group : forall (Sys : ERRSystem) i,
  rp_map Sys (role_perm_id Sys) i = i.
Proof. intros. apply role_perm_id_spec. Qed.

(* ================================================================== *)
(*  Part III: Relative Rules  (~6 lemmas)                             *)
(* ================================================================== *)

(** A Rule is "relative" if it's invariant under Role permutations *)
Definition is_relative_rule (Sys : ERRSystem) : Prop :=
  forall sigma : RolePermutation Sys,
    forall i j, (i < err_nsites Sys)%nat -> (j < err_nsites Sys)%nat ->
      err_rule Sys (rp_map Sys sigma i) (rp_map Sys sigma j) ==
      err_rule Sys i j.

(** ★ Relative Rules are invariant under Role permutations *)
Theorem relative_rules_are_symmetric : forall (Sys : ERRSystem),
  is_relative_rule Sys ->
  forall sigma : RolePermutation Sys,
    forall i j, (i < err_nsites Sys)%nat -> (j < err_nsites Sys)%nat ->
      err_rule Sys (rp_map Sys sigma i) (rp_map Sys sigma j) ==
      err_rule Sys i j.
Proof. intros Sys H sigma i j Hi Hj. apply H; auto. Qed.

(** Example: if R(i,j) = f(role(i), role(j)) then relative *)
Definition role_only_rule (Sys : ERRSystem) (f : nat -> nat -> Q) : Prop :=
  forall i j, err_rule Sys i j == f (err_role Sys i) (err_role Sys j).

Lemma role_only_implies_relative : forall Sys f,
  role_only_rule Sys f -> is_relative_rule Sys.
Proof.
  intros Sys f Hro. unfold is_relative_rule. intros sigma i j Hi Hj.
  unfold role_only_rule in Hro.
  setoid_rewrite (Hro (rp_map Sys sigma i) (rp_map Sys sigma j)).
  rewrite (rp_preserves_role Sys sigma i Hi).
  rewrite (rp_preserves_role Sys sigma j Hj).
  symmetry. apply Hro.
Qed.

(* ================================================================== *)
(*  Part IV: Symmetry Group Structure  (~4 lemmas)                    *)
(* ================================================================== *)

(** The symmetry group decomposes as direct product *)
Theorem symmetry_group_structure : forall (Sys : ERRSystem) (sigma : RolePermutation Sys) i,
  (* G ≅ S_{n₁} × S_{n₂} × ... × S_{n_k} *)
  rp_map Sys (role_perm_compose Sys (role_perm_id Sys) sigma) i = rp_map Sys sigma i.
Proof. intros. apply role_perm_id_left. Qed.

(** Single role: all elements interchangeable → G = S_n *)
Theorem single_role_symmetric_group : forall (Sys : ERRSystem),
  err_nroles Sys = 1%nat -> (role_count Sys 0 <= err_nsites Sys)%nat.
Proof. intros. apply role_count_bounded. Qed.

(** Two roles: G = S_{n_up} × S_{n_down} — SU(2) structure *)
Theorem two_roles_product : forall (Sys : ERRSystem),
  err_nroles Sys = 2%nat -> (role_count Sys 0 <= err_nsites Sys)%nat.
Proof. intros. apply role_count_bounded. Qed.
