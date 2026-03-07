(** * Estimation.v — Statistical Estimation as ToS System

    Theory of Systems — Verified Standard Library (Batch 4)

    Elements: parameter estimates, likelihoods, prior/posterior
    Roles:    mle -> Maximum Likelihood, map -> Maximum A Posteriori
    Rules:    grid search finds maximum, priors update via Bayes (constitution)
    Status:   estimated | unestimated | degenerate

    STATUS: 18 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lqa.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Q_scope.
From ToS Require Import TheoryOfSystems_Core_ERR.

(* ========================================================================= *)
(* PART I: GRID SEARCH — Generic Optimization over Finite Grid (3 Qed)       *)
(* ========================================================================= *)

(** Generic grid search: find element of grid maximizing f.
    Returns (best_param, best_value). *)
Fixpoint grid_search (f : Q -> Q) (grid : list Q) (best : Q) (best_val : Q) : Q * Q :=
  match grid with
  | [] => (best, best_val)
  | p :: rest =>
    let v := f p in
    if Qle_bool best_val v then grid_search f rest p v
    else grid_search f rest best best_val
  end.

(** grid_search on empty grid returns the current best *)
Lemma grid_search_nil : forall f best bv,
  grid_search f [] best bv = (best, bv).
Proof. reflexivity. Qed.

(** grid_search on a singleton list: if f(p) >= bv, update; otherwise keep *)
Lemma grid_search_singleton : forall f p best bv,
  grid_search f [p] best bv =
    if Qle_bool bv (f p) then (p, f p)
    else (best, bv).
Proof. reflexivity. Qed.

(** grid_search cons step *)
Lemma grid_search_cons : forall f p rest best bv,
  grid_search f (p :: rest) best bv =
    if Qle_bool bv (f p)
    then grid_search f rest p (f p)
    else grid_search f rest best bv.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* PART II: MLE and MAP — Maximum Likelihood / A Posteriori (3 Qed)          *)
(* ========================================================================= *)

(** MLE: maximize likelihood over parameter grid *)
Definition mle_grid (likelihood : Q -> Q) (grid : list Q) : Q * Q :=
  match grid with
  | [] => (0, 0)
  | p :: rest => grid_search likelihood rest p (likelihood p)
  end.

(** MAP: maximize likelihood * prior over parameter grid *)
Definition map_grid (likelihood : Q -> Q) (prior : Q -> Q) (grid : list Q) : Q * Q :=
  mle_grid (fun p => likelihood p * prior p) grid.

(** MLE on empty grid is (0, 0) *)
Lemma mle_grid_nil : forall f, mle_grid f [] = (0, 0).
Proof. reflexivity. Qed.

(** MLE on singleton grid returns (p, f(p)) *)
Lemma mle_grid_singleton : forall f p, mle_grid f [p] = (p, f p).
Proof. reflexivity. Qed.

(** MAP is defined as MLE of the posterior-proportional function *)
Lemma map_grid_def : forall lik prior grid,
  map_grid lik prior grid = mle_grid (fun p => lik p * prior p) grid.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* PART III: BERNOULLI LIKELIHOOD (6 Qed)                                    *)
(* ========================================================================= *)

(** Likelihood for Bernoulli data: p^(successes) * (1-p)^(failures)
    Data is a list of 0/1 as nat. *)
Fixpoint bernoulli_likelihood (data : list nat) (p : Q) : Q :=
  match data with
  | [] => 1
  | 1%nat :: rest => p * bernoulli_likelihood rest p
  | 0%nat :: rest => (1 - p) * bernoulli_likelihood rest p
  | _ :: rest => bernoulli_likelihood rest p
  end.

(** Likelihood of empty data is 1 *)
Lemma bernoulli_likelihood_nil : forall p,
  bernoulli_likelihood [] p = 1.
Proof. reflexivity. Qed.

(** Likelihood of single success is p *)
Lemma bernoulli_likelihood_one : forall p,
  bernoulli_likelihood [1%nat] p == p.
Proof. intros. simpl. lra. Qed.

(** Likelihood of single failure is 1-p *)
Lemma bernoulli_likelihood_zero : forall p,
  bernoulli_likelihood [0%nat] p == 1 - p.
Proof. intros. simpl. lra. Qed.

(** Cons 1: success multiplies by p *)
Lemma bernoulli_likelihood_cons_1 : forall data p,
  bernoulli_likelihood (1%nat :: data) p = p * bernoulli_likelihood data p.
Proof. reflexivity. Qed.

(** Cons 0: failure multiplies by 1-p *)
Lemma bernoulli_likelihood_cons_0 : forall data p,
  bernoulli_likelihood (0%nat :: data) p = (1 - p) * bernoulli_likelihood data p.
Proof. reflexivity. Qed.

(** Likelihood of [1; 0; 1] computes correctly *)
Lemma bernoulli_likelihood_example : forall p,
  bernoulli_likelihood [1%nat; 0%nat; 1%nat] p == p * ((1 - p) * p).
Proof. intros. simpl. ring. Qed.  (* ring works here: complex Q expression *)

(* ========================================================================= *)
(* PART IV: PRIORS (3 Qed)                                                   *)
(* ========================================================================= *)

(** Uniform prior: constant 1 everywhere *)
Definition uniform_prior (_ : Q) : Q := 1.

(** Point prior: 1 at target, 0 elsewhere (for concrete values) *)
Definition point_prior (target : Q) (p : Q) : Q :=
  if Qeq_bool p target then 1 else 0.

(** Uniform prior is always 1 *)
Lemma uniform_prior_const : forall p, uniform_prior p = 1.
Proof. reflexivity. Qed.

(** Point prior at a concrete target matches *)
Lemma point_prior_at_target : point_prior (1#2) (1#2) = 1.
Proof. reflexivity. Qed.

(** Point prior away from target is 0 *)
Lemma point_prior_miss : point_prior (1#2) (3#4) = 0.
Proof. reflexivity. Qed.

(* ========================================================================= *)
(* PART V: CONCRETE MLE COMPUTATION (2 Qed)                                  *)
(* ========================================================================= *)

(** Concrete MLE example: find MLE for Bernoulli [1;1;0] over grid [1/4; 1/2; 3/4].
    Likelihoods:
      1/4: (1/4)*(1/4)*(3/4) = 3/64
      1/2: (1/2)*(1/2)*(1/2) = 1/8 = 8/64
      3/4: (3/4)*(3/4)*(1/4) = 9/64
    MLE = 3/4 with value 9/64. *)
Lemma mle_grid_bernoulli_example :
  fst (mle_grid (bernoulli_likelihood [1%nat; 1%nat; 0%nat]) [(1#4); (1#2); (3#4)]) = (3#4).
Proof. vm_compute. reflexivity. Qed.

(** The MAP with uniform prior selects the same parameter as MLE
    (since uniform_prior = 1 everywhere, lik * 1 has same argmax as lik). *)
Lemma map_uniform_bernoulli_example :
  fst (map_grid (bernoulli_likelihood [1%nat; 1%nat; 0%nat])
                uniform_prior
                [(1#4); (1#2); (3#4)]) = (3#4).
Proof. vm_compute. reflexivity. Qed.

(* ========================================================================= *)
(* PART VI: FISHER INFORMATION SCAFFOLD (1 Qed)                              *)
(* ========================================================================= *)

(** Fisher information record: wraps a nonneg-annotated Q value. *)
Record FisherInfo := mkFisherInfo {
  fi_param : Q;
  fi_value : Q;
  fi_nonneg : 0 <= fi_value;
}.

(** Construct a concrete FisherInfo *)
Lemma fisher_info_example : exists (fi : FisherInfo),
  fi_param fi = (1#2) /\ fi_value fi = 4.
Proof.
  exists (mkFisherInfo (1#2) 4 ltac:(lra)).
  split; reflexivity.
Qed.

