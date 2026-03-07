(** * DiscreteMathExamples.v — Cross-Module Discrete Math Examples

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: cross-module computation examples
    Roles:    example -> Demonstration, import -> Bridge
    Rules:    computation (constitution: reflexivity-decidable results)
    Status:   verified | computed

    Connection: All Batch 3 modules

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

From ToS Require Import stdlib.Primes.
From ToS Require Import stdlib.GCD.
From ToS Require Import stdlib.ModularArith.
From ToS Require Import stdlib.Combinatorics.
From ToS Require Import stdlib.Graph.
From ToS Require Import stdlib.GraphAlgorithms.
From ToS Require Import stdlib.Automata.
From ToS Require Import stdlib.FormalLanguages.

(* ================================================================= *)
(** ** Cross-Module Examples                                          *)
(* ================================================================= *)

(** 1. Sieve produces primes: gcd of any two sieve results is 1 *)
Lemma sieve_primes_coprime_2_3 : coprime 2 3.
Proof. reflexivity. Qed.

(** 2. 5 is prime and coprime with 6 *)
Lemma prime_5_coprime_6 : is_prime_bool 5 = true /\ coprime 5 6.
Proof. split; reflexivity. Qed.

(** 3. Modular arithmetic: 7 mod 5 = 2, and 7 ≡ 2 (mod 5) *)
Lemma mod_and_congruent_7_2_5 :
  Nat.modulo 7 5 = 2 /\ congruent 7 2 5.
Proof. split; reflexivity. Qed.

(** 4. Binomial coefficient: C(5,2) = 10 = lcm(2,5) *)
Lemma binomial_eq_lcm : binomial 5 2 = lcm 2 5.
Proof. reflexivity. Qed.

(** 5. Factorial and primality: 4! = 24, and 24 is not prime *)
Lemma fact_4_not_prime : fact 4 = 24 /\ is_prime_bool 24 = false.
Proof. split; reflexivity. Qed.

(** 6. Graph: triangle has 3 edges, line has 2 edges *)
Lemma graph_edge_counts :
  num_edges graph_triangle = 3 /\ num_edges graph_line = 2.
Proof. split; reflexivity. Qed.

(** 7. BFS and DFS agree on line graph from 0 *)
Lemma bfs_dfs_agree_line :
  bfs graph_line 0 = dfs graph_line 0.
Proof. reflexivity. Qed.

(** 8. DFA: even parity DFA rejects [1] and accepts [1;1] *)
Lemma even_parity_examples :
  dfa_accepts even_parity_dfa [1] = false /\
  dfa_accepts even_parity_dfa [1; 1] = true.
Proof. split; reflexivity. Qed.

(** 9. Regexp: (0|1)* matches [0;1;0] *)
Lemma regexp_star_union :
  matches (RE_Star (RE_Union (RE_Char 0) (RE_Char 1))) [0; 1; 0].
Proof.
  replace [0; 1; 0] with ([0] ++ [1; 0]) by reflexivity.
  apply M_Star_Cons.
  - apply M_Union_L. apply M_Char.
  - replace [1; 0] with ([1] ++ [0]) by reflexivity.
    apply M_Star_Cons.
    + apply M_Union_R. apply M_Char.
    + replace [0] with ([0] ++ []) by (apply app_nil_r).
      apply M_Star_Cons.
      * apply M_Union_L. apply M_Char.
      * apply M_Star_Nil.
Qed.

(** 10. GCD divides both: gcd(12,8) = 4 divides 12 *)
Lemma gcd_divides_example : divides (gcd 12 8) 12.
Proof.
  apply gcd_divides_l.
Qed.

(** 11. Modular addition is consistent with gcd:
    3 + 4 = 7 ≡ 2 (mod 5), and gcd(2, 5) = 1 *)
Lemma zmod_add_coprime :
  zmod_add 3 4 5 = 2 /\ coprime 2 5.
Proof. split; reflexivity. Qed.

(** 12. Complete pipeline: sieve, test prime, compute gcd, check mod *)
Lemma full_pipeline_example :
  let primes := sieve 8 in
  let p1 := hd 0 primes in          (* 2 *)
  let p2 := hd 0 (tl (tl primes)) in  (* 5 *)
  is_prime_bool p1 = true /\
  is_prime_bool p2 = true /\
  gcd p1 p2 = 1 /\
  zmod_mul p1 p2 7 = 3.
Proof. simpl. repeat split; reflexivity. Qed.

(** Summary: 12 Qed, 0 Admitted, 0 axioms *)
