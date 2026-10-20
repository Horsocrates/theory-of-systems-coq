(* ========================================================================= *)
(*       DIAGONAL ARGUMENT UNIFICATION: WHERE L5 BREAKS                     *)
(*                                                                          *)
(*  THE GREAT NO-GO THEOREMS:                                               *)
(*                                                                          *)
(*    Cantor (1891)       — no surjection ℕ → 2^ℕ.                         *)
(*    Russell (1901)      — no set of all sets not containing themselves.  *)
(*    Halting (Turing)    — no decision procedure for halting.            *)
(*    Gödel (1931)        — no complete consistent arithmetic theory.    *)
(*    Tarski (1936)       — no definition of truth within the language.  *)
(*    Rice (1953)         — no decision for non-trivial program properties.*)
(*                                                                          *)
(*  THESIS OF THIS FILE:                                                    *)
(*                                                                          *)
(*    All these no-go results share the SAME structure: a DIAGONAL         *)
(*    argument that asks: what if a function/predicate applies to its      *)
(*    own code? — and constructs a witness where L5/μ FAILS.               *)
(*                                                                          *)
(*    In the project's framework: these are precisely the POINTS WHERE     *)
(*    L5/μ STOPS WORKING. Inside the L5-domain (bounded + decidable),     *)
(*    we have constructive answers. At the diagonal, we hit the           *)
(*    role-limit — the boundary beyond which L5 cannot extract a witness. *)
(*                                                                          *)
(*  THE UNIFICATION: each no-go is the same shape:                         *)
(*                                                                          *)
(*    For ANY candidate solution g, the diagonal d_g disagrees with g     *)
(*    AT THE INDEX where g is supposed to handle d_g itself.              *)
(*                                                                          *)
(*    [g does not decide its own diagonal] ⟹ no g works ⟹ role-limit.    *)
(*                                                                          *)
(*  WHAT THIS FILE PROVES:                                                  *)
(*                                                                          *)
(*    [cantor_pointwise]      — Cantor: f n disagrees with d at point n.  *)
(*    [cantor_no_surj]        — no surjection nat → (nat → bool).         *)
(*    [diag_no_id_match]      — generalized diagonal: forall extension,   *)
(*                              the diagonal escapes.                     *)
(*                                                                          *)
(*  CONNECTION TO PROJECT THESIS:                                           *)
(*                                                                          *)
(*    H1 (finitization boundary = constructivity boundary): the diagonal  *)
(*    IS the boundary. Inside finitization (bounded, decidable), L5/μ    *)
(*    extracts. At the diagonal, L5/μ would require deciding: does this  *)
(*    process halt on its own code — which is role-limit by self-       *)
(*    reference.                                                          *)
(*                                                                          *)
(*    Every project no-go (HaltingRoleLimit, DiagonalArgument_ERR,        *)
(*    Russell-style paradoxes) instantiates this template.                 *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1):  candidate decision procedure / surjection / etc.    *)
(*    Roles (L1):     the procedure's output on different inputs.        *)
(*    Rules (L2):     self-applicability (procedure applied to itself).  *)
(*    Order (L5):     the diagonal element where L5/μ search would need *)
(*                    to terminate but cannot (role-limit).               *)
(*    Process (P4):   the procedure as a P4-process — but the diagonal  *)
(*                    breaks termination guarantees.                     *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: CANTOR'S POINTWISE DIAGONAL                         *)
(* ========================================================================= *)

(** The diagonal of a function f : nat → (nat → bool). At index k,
    d_f(k) = negation of f(k)(k). *)
Definition cantor_diagonal (f : nat -> nat -> bool) : nat -> bool :=
  fun k => negb (f k k).

(** Pointwise: f n and d_f disagree at the index n. *)
Theorem cantor_pointwise : forall (f : nat -> nat -> bool) (n : nat),
  f n n <> cantor_diagonal f n.
Proof.
  intros f n. unfold cantor_diagonal.
  destruct (f n n); cbn; congruence.
Qed.

(** No function f : nat → (nat → bool) equals its own diagonal at every point. *)
Theorem cantor_no_self_diagonal : forall (f : nat -> nat -> bool),
  ~ (forall n, f n n = cantor_diagonal f n).
Proof.
  intros f Heq. specialize (Heq 0).
  apply (cantor_pointwise f 0). exact Heq.
Qed.

(** Strong form: for any candidate surjection f, the diagonal d_f is
    NOT in the image of f. *)
Theorem cantor_no_surj : forall (f : nat -> nat -> bool),
  ~ (forall g : nat -> bool, exists n, forall k, f n k = g k).
Proof.
  intros f Hsurj.
  specialize (Hsurj (cantor_diagonal f)) as [n Hn].
  specialize (Hn n).
  apply (cantor_pointwise f n). exact Hn.
Qed.

(* ========================================================================= *)
(*               PART II: GENERALIZED DIAGONAL TEMPLATE                      *)
(* ========================================================================= *)

(** Generalized diagonal: any self-applying function meets its own
    negation at the self-application point. *)
Theorem diag_no_id_match : forall (T : Type) (apply : T -> T -> bool) (neg : bool -> bool),
  (forall b, neg b <> b) ->
  forall t : T, exists (s : T) (negate : T -> T -> bool),
    (forall x y, negate x y = neg (apply x y)) /\
    negate s t <> apply s t.
Proof.
  intros T apply neg Hneg t.
  exists t, (fun x y => neg (apply x y)).
  split; [reflexivity|].
  intros Heq. apply (Hneg (apply t t)). exact Heq.
Qed.

(** Concrete instantiation for nat-indexed predicates. *)
Theorem diag_self_reference : forall (P : nat -> nat -> bool),
  ~ (exists n, forall k, P n k = negb (P k k)).
Proof.
  intros P [n Hn].
  specialize (Hn n). pose proof (cantor_pointwise P n) as Hpw.
  unfold cantor_diagonal in Hpw.
  apply Hpw. exact Hn.
Qed.

(* ========================================================================= *)
(*               PART III: WHERE L5 BREAKS                                   *)
(* ========================================================================= *)

(** STATEMENT: L5/μ requires DECIDABILITY at every index. The diagonal
    breaks this by forcing the procedure to decide "does this procedure
    halt on its own code?" — at the very index where it must halt to
    decide.

    Formally: for the diagonal d_f, computing d_f(n) requires computing
    f(n)(n), which is the value of f's n-th decision-output evaluated on
    n itself. If f is supposed to decide halting, this is the self-applied
    halting question. *)

(** Cantor in pessimistic form: no function decides its own diagonal. *)
Theorem cantor_self_undecidable : forall (decide : nat -> nat -> bool),
  ~ (forall n k, decide n k = true <-> ~ (decide k k = true)).
Proof.
  intros decide Hdecide.
  pose proof (Hdecide 0 0) as [H_fwd H_bwd].
  destruct (decide 0 0) eqn:Heq.
  - apply (H_fwd eq_refl). reflexivity.
  - specialize (H_bwd ltac:(discriminate)). discriminate.
Qed.

(* ========================================================================= *)
(*               PART IV: ERR + COMMENTARY                                   *)
(* ========================================================================= *)

(**
  THE DIAGONAL AS THE L5/μ-BOUNDARY:

  The L5/μ-machinery in the project (mu_le, mu_le_max, smallest-anything) works
  precisely on DECIDABLE predicates over BOUNDED ranges. At the diagonal,
  both conditions fail:

  (1) DECIDABILITY FAILS at the self-applied index, because deciding
      d_f(n) = ¬f(n)(n) requires knowing f(n)(n) — which is the very
      question being asked.

  (2) THE BOUND IS UNCAPPED: in the halting analog, the search for a
      halting time has no a-priori upper bound. The diagonal forces us
      to ask: does this halt EVER — an unbounded existential.

  L5/μ-SOLUBLE vs L5/μ-INSOLUBLE:

  - Inside the L5/μ-domain (bounded halting, finite divisor, finite
    pigeon): every problem has a constructive solution.
  - At the diagonal: the problem is REVERSED — its very definition
    requires an answer we don't yet have.

  THE UNIFICATION (one template, many instantiations):

  | Theorem    | Diagonal Action                       | L5/μ Failure          |
  |-----------|-----------------------------------------|-----------------------|
  | Cantor    | d(k) = negb (f k k)                     | search of f^(-1)(d)   |
  | Halting   | program H' that halts iff H says loop   | search for halt time  |
  | Gödel     | sentence: this is unprovable            | search of proof       |
  | Rice      | property: halts on input 0              | search for decider    |
  | Tarski    | sentence: this sentence is false        | search of truth fn    |

  All share: SELF-REFERENCE + NEGATION at the index where L5/μ would
  need to terminate.

  THE PROJECT'S CENTRAL THESIS:

  H1 (finitization boundary = constructivity boundary):
    L5/μ-DOMAIN = constructive math without ZFC.
    DIAGONAL = role-limit, beyond P4+L5.

  Outside the diagonal, classical math is fully reconstructed:
  finite combinatorics, decidable arithmetic, primitive recursion,
  bounded analysis. At the diagonal, classical math invokes Zorn's lemma,
  axiom of choice, completeness theorems — all of which fail constructively
  AT THE DIAGONAL.

  WHY THIS MATTERS:

  Knowing where L5/μ breaks gives a SHARP characterization of the
  constructive corpus. We don't lose math; we identify the exact
  ZFC-dependent fragments as DIAGONAL-INDUCED role-limits.

  WHAT THIS OPENS NEXT:

  - [Halting_Diagonal.v]: complete halting proof via Cantor-style diagonal.
  - [Rice_Diagonal.v]: Rice's theorem as diagonal on program properties.
  - [Gödel_Diagonal.v]: incompleteness via arithmetized diagonal.
  - [Tarski_Diagonal.v]: undefinability of truth via diagonal.
  - [Russell_Class.v]: Russell paradox in class theory via diagonal.

  All instantiate the same template. Together they exhaust the
  CONSTRUCTIVELY UNDECIDABLE / role-limit phenomena.
*)
