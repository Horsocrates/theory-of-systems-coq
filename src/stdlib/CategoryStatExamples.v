(** * CategoryStatExamples.v — Cross-Module Examples (Batch 4)

    Theory of Systems — Verified Standard Library (Batch 4)

    Integration examples demonstrating Category Theory, Statistics,
    and Information Theory working together.

    Elements: concrete computations across all Batch 4 modules
    Roles:    each example -> Demonstration
    Rules:    all proofs by computation or simple reasoning
    Status:   verified

    STATUS: 16 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Q_scope.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import stdlib.Category.
From ToS Require Import stdlib.Functor.
From ToS Require Import stdlib.Monad.
From ToS Require Import stdlib.Lattice.
From ToS Require Import stdlib.Distributions.
From ToS Require Import stdlib.Statistics.
From ToS Require Import stdlib.InformationTheory.
From ToS Require Import stdlib.Estimation.

(* ================================================================= *)
(*  PART I: MONAD EXAMPLES                                            *)
(* ================================================================= *)

(** 1. Option monad: bind (Some 42) (fun x => Some (x+1)) = Some 43 *)
Lemma example_option_monad_bind :
  option_bind nat nat (Some 42%nat) (fun x => Some (x + 1)%nat) = Some 43%nat.
Proof. reflexivity. Qed.

(** 2. Option monad: None bind = None *)
Lemma example_option_none_bind :
  option_bind nat nat None (fun x => Some (x + 1)%nat) = None.
Proof. reflexivity. Qed.

(** 3. Kleisli composition of option functions *)
Definition opt_succ (n : nat) : option nat := Some (S n).
Definition opt_double (n : nat) : option nat := Some (n + n)%nat.

Lemma example_kleisli_option :
  kleisli OptionMonad nat nat nat opt_succ opt_double 3%nat = Some 8%nat.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  PART II: FUNCTOR EXAMPLES                                         *)
(* ================================================================= *)

(** 4. List functor: map S [1;2;3] = [2;3;4] *)
Lemma example_list_functor_map :
  map S [1%nat; 2%nat; 3%nat] = [2%nat; 3%nat; 4%nat].
Proof. reflexivity. Qed.

(** 5. TypeCat identity is identity *)
Lemma example_TypeCat_id :
  cat_id TypeCat nat 42%nat = 42%nat.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  PART III: LATTICE EXAMPLES                                        *)
(* ================================================================= *)

(** 6. Bool lattice: meet true false = false *)
Lemma example_bool_lattice_meet :
  lat_meet bool_lattice true false = false.
Proof. reflexivity. Qed.

(** 7. Bool lattice: join false true = true *)
Lemma example_bool_lattice_join :
  lat_join bool_lattice false true = true.
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  PART IV: DISTRIBUTION EXAMPLES                                    *)
(* ================================================================= *)

(** 8. Bernoulli(1/2) mean equals 1/2 *)
Lemma half_valid : 0 <= 1#2 /\ 1#2 <= 1.
Proof. split; lra. Qed.

Definition bern_half := mkBernoulli (1#2) half_valid.

Lemma example_bernoulli_mean : bern_mean bern_half == 1#2.
Proof. unfold bern_mean, bern_half. simpl. lra. Qed.

(** 9. Qpow (1/2) 3 = 1/8 *)
Lemma example_qpow : Qpow (1#2) 3%nat == 1#8.
Proof. simpl. ring. Qed.

(* ================================================================= *)
(*  PART V: STATISTICS EXAMPLES                                       *)
(* ================================================================= *)

(** 10. Mean of [10; 20; 30] == 20 *)
Lemma example_sample_mean : mean [10; 20; 30] == 20.
Proof. unfold mean, sum_Q, length_Q. simpl. field. Qed.

(** 11. Dot product [1;2;3] . [4;5;6] == 32 *)
Lemma example_dot_product :
  dot_product [1;2;3] [4;5;6] == 32.
Proof. unfold dot_product, weighted_sum. simpl. ring. Qed.

(* ================================================================= *)
(*  PART VI: ESTIMATION EXAMPLES                                      *)
(* ================================================================= *)

(** 12. Bernoulli likelihood [1;1;0] at p=1/2 == 1/8 *)
Lemma example_bernoulli_likelihood :
  bernoulli_likelihood [1%nat; 1%nat; 0%nat] (1#2) == 1#8.
Proof. unfold bernoulli_likelihood. simpl. ring. Qed.

(** 13. Grid search finds maximum of x*x over [1/2; 1; 3/2] *)
Lemma example_grid_search :
  fst (grid_search (fun x => x * x) [1#2; 1; 3#2] 0 0) == 3#2.
Proof. vm_compute. reflexivity. Qed.

(** 14. MLE on singleton grid returns that point *)
Lemma example_mle_singleton :
  mle_grid (fun p => p * p) [(1#2)] = ((1#2), (1#2) * (1#2)).
Proof. reflexivity. Qed.

(* ================================================================= *)
(*  PART VII: INFORMATION THEORY EXAMPLE                              *)
(* ================================================================= *)

(** 15. Entropy of empty distribution is 0 — cross-module check *)
Lemma example_entropy_nil : forall log_Q,
  entropy_sum log_Q [] == 0.
Proof. intros. simpl. reflexivity. Qed.

(* ================================================================= *)
(*  Summary: 16 Qed, 0 Admitted, 0 axioms                            *)
(*    3 Monad: option_bind, none_bind, kleisli                        *)
(*    2 Functor: list_functor_map, TypeCat_id                         *)
(*    2 Lattice: bool_meet, bool_join                                 *)
(*    2 Distribution: bernoulli_mean, qpow                            *)
(*    2 Statistics: sample_mean, dot_product                          *)
(*    2 Estimation: bernoulli_likelihood, grid_search                 *)
(*    1 Estimation: mle_singleton                                     *)
(*    1 InfoTheory: entropy_nil                                       *)
(* ================================================================= *)
