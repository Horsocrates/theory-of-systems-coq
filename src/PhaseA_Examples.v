(* ========================================================================= *)
(*           PHASE A INTEGRATION EXAMPLES                                  *)
(*  Ties together Phase A: DependentSystems, InductiveSystems,             *)
(*  CoinductiveSystems, ConstitutionChecking, ErasureTheory,               *)
(*  UniversePolymorphism with concrete examples.                           *)
(*  STATUS: 11 Qed, 0 Admitted | Author: Horsocrates | March 2026         *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import QArith.QArith.
Import ListNotations.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.
From ToS Require Import DependentSystems.
From ToS Require Import InductiveSystems.
From ToS Require Import CoinductiveSystems.
From ToS Require Import ProcessGeneral.
From ToS Require Import ConstitutionChecking.
From ToS Require Import ErasureTheory.
From ToS Require Import Roles.
From ToS Require Import UniversePolymorphism.

Open Scope nat_scope.

(* ======================== EXAMPLE 1: Nat -> Q as Pi ==================== *)

Section NatToQ.

Definition Q_system_L2 : System L2 := {|
  sys_criterion := {|
    crit_domain := Q;
    crit_predicate := fun _ => True;
    crit_level_witness := L1;
    crit_level_valid := L1_lt_L2;
  |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

Definition nat_to_Q (n : nat) : Q := inject_Z (Z.of_nat n).

(** Lemma 1: nat -> Q as constant-fiber PiSystem *)
Lemma nat_to_Q_is_pi :
  exists (f : PiSystem L2 nat_system_L2 (fun _ => Q_system_L2)),
    forall n : nat,
      pi_app L2 nat_system_L2 (fun _ => Q_system_L2) f n = nat_to_Q n.
Proof.
  exists (mkPiSystem L2 nat_system_L2 (fun _ => Q_system_L2) nat_to_Q).
  intros n. simpl. reflexivity.
Qed.

End NatToQ.

(* =================== EXAMPLE 2: (n, list) as Sigma ==================== *)

Section NatListSigma.

Definition list_nat_system_L2 : System L2 := {|
  sys_criterion := {|
    crit_domain := list nat;
    crit_predicate := fun _ => True;
    crit_level_witness := L1;
    crit_level_valid := L1_lt_L2;
  |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

(** Lemma 2: (3, [1;2;3]) as SigmaElem with correct projections *)
Lemma nat_list_is_sigma :
  exists (p : SigmaElem L2 nat_system_L2 (fun _ => list_nat_system_L2)),
    sigma_fst L2 nat_system_L2 _ p = 3%nat /\
    sigma_snd L2 nat_system_L2 _ p = [1%nat; 2%nat; 3%nat].
Proof.
  exists (mkSigmaElem L2 nat_system_L2
            (fun _ => list_nat_system_L2) 3%nat [1%nat; 2%nat; 3%nat]).
  simpl. split; reflexivity.
Qed.

End NatListSigma.

(* ============== EXAMPLE 3: Cauchy sequence as Observable =============== *)

Section CauchyObservable.

Definition recip_seq (n : nat) : Q := 1 # (Pos.of_succ_nat n).

(** Lemma 3: 1/(n+1) as Observable Q with correct values at 0 and 1 *)
Lemma cauchy_is_observable :
  exists (o : Observable Q),
    obs_at o 0 = 1 # 1 /\ obs_at o 1 = 1 # 2.
Proof.
  exists (obs_from_function recip_seq (fun _ => True)).
  split;
    unfold obs_at, obs_from_function, observe; simpl; reflexivity.
Qed.

End CauchyObservable.

(* ============= EXAMPLE 4: Even as decidable constitution =============== *)

Section EvenDecidable.

Definition is_even (n : nat) : Prop := Nat.even n = true.

(** Lemma 4: Nat.even has a decidable constitution *)
Lemma even_is_decidable : DecidableConstitution nat is_even.
Proof.
  constructor. intro e. unfold is_even.
  destruct (Nat.even e) eqn:He.
  - left. reflexivity.
  - right. intro H. discriminate.
Qed.

End EvenDecidable.

(* ================ EXAMPLE 5: Nat system with erasure =================== *)

Section NatErasure.

Definition nat_element_ac : AnnotatedComponent := mkAC Cat_Element Runtime.
Definition nat_role_ac    : AnnotatedComponent := mkAC Cat_Role CompileOnly.
Definition nat_rule_ac    : AnnotatedComponent := mkAC Cat_Rule Runtime.

Definition nat_components : list AnnotatedComponent :=
  [nat_element_ac; nat_role_ac; nat_rule_ac].

(** Lemma 5: elements survive erasure *)
Lemma nat_system_erasure : In nat_element_ac (erase nat_components).
Proof.
  unfold nat_components, erase, filter, is_runtime.
  simpl. left. reflexivity.
Qed.

(** Lemma 6: no CompileOnly components remain after erasure *)
Lemma nat_system_erasure_no_roles :
  forall ac, In ac (erase nat_components) -> ac_relevance ac = Runtime.
Proof.
  intros ac Hin.
  apply erasure_removes_compile_only in Hin. exact Hin.
Qed.

(** Lemma 7: rules also survive erasure *)
Lemma nat_system_erasure_rules : In nat_rule_ac (erase nat_components).
Proof.
  unfold nat_components, erase, filter, is_runtime.
  simpl. right. left. reflexivity.
Qed.

End NatErasure.

(* ============ EXAMPLE 6: FinitelyGenerated -> Observable =============== *)

Section FGObservable.

(** Lemma 8: any enumeration function gives an Observable *)
Lemma finitely_generated_observable :
  forall (A : Type) (enum : nat -> A) (P : A -> Prop),
    exists (o : Observable A), forall n, obs_at o n = enum n.
Proof.
  intros A enum P.
  exists (obs_from_function enum P).
  intro n. unfold obs_at, obs_from_function, observe. simpl. reflexivity.
Qed.

End FGObservable.

(* ============== EXAMPLE 7: Integration check (all-in-one) ============== *)

Section Integration.

(** Lemma 9: Pi + FinitelyGenerated + Decidability + Erasure combined *)
Lemma integration_check :
  (exists (f : PiSystem L2 nat_system_L2 (fun _ => nat_system_L2)),
     pi_app L2 nat_system_L2 (fun _ => nat_system_L2) f 0 = 0) /\
  (exists (fg : FinitelyGenerated nat), fg_depth nat fg 0 = 0) /\
  (0 = 0 \/ 0 <> 0) /\
  (In nat_element_ac (erase nat_components) /\
   ~ In nat_role_ac (erase nat_components)).
Proof.
  repeat split.
  - exists (mkPiSystem L2 nat_system_L2 (fun _ => nat_system_L2) (fun n => n)).
    simpl. reflexivity.
  - exists (mkFinitelyGenerated nat nat_depth). reflexivity.
  - left. reflexivity.
  - exact nat_system_erasure.
  - unfold nat_components, erase, filter, is_runtime. simpl.
    intros [H | [H | H]].
    + unfold nat_element_ac, nat_role_ac in H. discriminate.
    + unfold nat_rule_ac, nat_role_ac in H. discriminate.
    + exact H.
Qed.

End Integration.

(* ============== EXAMPLE 8: Level depth + prefix finiteness ============= *)

Section LevelIntegration.

(** Lemma 10: L2 has depth 2 and level_add L1 1 = L2 *)
Lemma pi_system_level_depth :
  level_depth L2 = 2 /\ level_add L1 1 = L2.
Proof. split; reflexivity. Qed.

(** Lemma 11: Observable prefix length = n, nat_depth n = n *)
Lemma observable_prefix_finite :
  forall (o : Observable nat) (n : nat),
    length (obs_prefix o n) = n /\ nat_depth n = n.
Proof.
  intros o n. split.
  - apply obs_prefix_length.
  - reflexivity.
Qed.

End LevelIntegration.

(** SUMMARY: 11 Qed, 0 Admitted.
    1.  nat_to_Q_is_pi               -- Pi: nat -> Q
    2.  nat_list_is_sigma            -- Sigma: (n, list)
    3.  cauchy_is_observable         -- Observable: 1/(n+1)
    4.  even_is_decidable            -- DecidableConstitution: even
    5.  nat_system_erasure           -- Erasure: elements survive
    6.  nat_system_erasure_no_roles  -- Erasure: no CompileOnly left
    7.  nat_system_erasure_rules     -- Erasure: rules survive
    8.  finitely_generated_observable -- FG -> Observable
    9.  integration_check            -- Pi + FG + Dec + Erasure
    10. pi_system_level_depth        -- Level: depth(L2) = 2
    11. observable_prefix_finite     -- Coinductive + Inductive link *)
