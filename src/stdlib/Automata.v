(** * Automata.v — Deterministic and Nondeterministic Finite Automata as ToS System

    Theory of Systems — Verified Standard Library (Batch 3)

    Elements: states (nat), alphabet symbols (nat)
    Roles:    start -> InitialState, accept -> AcceptingState,
              transition -> StateUpdate
    Rules:    DFA transition (constitution: deterministic, total)
    Status:   accepting | rejecting | unreachable

    Connection: ConstitutionChecking.v (acceptance = constitution check)
    Connection: Graph.v (DFA = labeled directed graph)

    STATUS: 20 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ================================================================= *)
(** ** DFA: Deterministic Finite Automaton *)
(* ================================================================= *)

Record DFA := mkDFA {
  dfa_num_states : nat;
  dfa_start : nat;
  dfa_accept : list nat;
  dfa_trans : nat -> nat -> nat;  (* state -> symbol -> next_state *)
}.

(** Run DFA on input word from a given state *)
Fixpoint dfa_run (d : DFA) (state : nat) (input : list nat) : nat :=
  match input with
  | [] => state
  | a :: rest => dfa_run d (dfa_trans d state a) rest
  end.

(** Check if a state is in the accept list *)
Definition in_accept (accept : list nat) (s : nat) : bool :=
  existsb (Nat.eqb s) accept.

(** Check if DFA accepts an input word *)
Definition dfa_accepts (d : DFA) (input : list nat) : bool :=
  in_accept (dfa_accept d) (dfa_run d (dfa_start d) input).

(** DFA complement: invert acceptance *)
Definition dfa_complement (d : DFA) : DFA :=
  mkDFA (dfa_num_states d) (dfa_start d)
    (filter (fun s => negb (in_accept (dfa_accept d) s))
            (seq 0 (dfa_num_states d)))
    (dfa_trans d).

(* ================================================================= *)
(** ** NFA: Nondeterministic Finite Automaton *)
(* ================================================================= *)

Record NFA := mkNFA {
  nfa_num_states : nat;
  nfa_start : list nat;
  nfa_accept : list nat;
  nfa_trans : nat -> nat -> list nat;  (* state -> symbol -> list of next states *)
}.

(** NFA step: compute next state set from current set *)
Definition nfa_step (n : NFA) (current : list nat) (symbol : nat) : list nat :=
  flat_map (fun s => nfa_trans n s symbol) current.

(** Run NFA on input word *)
Fixpoint nfa_run (n : NFA) (current : list nat) (input : list nat) : list nat :=
  match input with
  | [] => current
  | a :: rest => nfa_run n (nfa_step n current a) rest
  end.

(** Check if any final state is an accept state *)
Definition nfa_accepts (n : NFA) (input : list nat) : bool :=
  existsb (fun s => existsb (Nat.eqb s) (nfa_accept n))
          (nfa_run n (nfa_start n) input).

(* ================================================================= *)
(** ** Example: Even Parity DFA *)
(* ================================================================= *)

(** States: 0 (even, start, accept), 1 (odd)
    Alphabet: {0, 1}
    Transitions: state 0 + symbol 0 -> 0, state 0 + symbol 1 -> 1,
                 state 1 + symbol 0 -> 1, state 1 + symbol 1 -> 0 *)
Definition even_parity_trans (s a : nat) : nat :=
  match s, a with
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0
  | _, _ => 0
  end.

Definition even_parity_dfa : DFA :=
  mkDFA 2 0 [0] even_parity_trans.

(* ================================================================= *)
(** ** Example: NFA accepting words ending with 1 *)
(* ================================================================= *)

(** States: 0 (start), 1 (seen 1, accept)
    Transitions: 0 + 0 -> [0], 0 + 1 -> [0; 1], 1 + anything -> [] *)
Definition ends_with_1_trans (s a : nat) : list nat :=
  match s, a with
  | 0, 0 => [0]
  | 0, 1 => [0; 1]
  | _, _ => []
  end.

Definition ends_with_1_nfa : NFA :=
  mkNFA 2 [0] [1] ends_with_1_trans.

(* ================================================================= *)
(** ** Theorems *)
(* ================================================================= *)

(** 1. DFA run on empty word returns current state *)
Theorem dfa_run_nil : forall d s, dfa_run d s [] = s.
Proof. reflexivity. Qed.

(** 2. DFA run on cons unfolds one step *)
Theorem dfa_run_cons : forall d s a w,
  dfa_run d s (a :: w) = dfa_run d (dfa_trans d s a) w.
Proof. reflexivity. Qed.

(** 3. DFA run distributes over append *)
Theorem dfa_run_app : forall d s w1 w2,
  dfa_run d s (w1 ++ w2) = dfa_run d (dfa_run d s w1) w2.
Proof.
  intros d s w1. revert s.
  induction w1 as [|a rest IH]; intros s w2.
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(** 4. NFA run on empty word returns current states *)
Theorem nfa_run_nil : forall n c, nfa_run n c [] = c.
Proof. reflexivity. Qed.

(** 5. NFA run on cons unfolds one step *)
Theorem nfa_run_cons : forall n c a w,
  nfa_run n c (a :: w) = nfa_run n (nfa_step n c a) w.
Proof. reflexivity. Qed.

(** 6. NFA step from empty state set is empty *)
Theorem nfa_step_nil : forall n a, nfa_step n [] a = [].
Proof. reflexivity. Qed.

(** 7. NFA run distributes over append *)
Theorem nfa_run_app : forall n c w1 w2,
  nfa_run n c (w1 ++ w2) = nfa_run n (nfa_run n c w1) w2.
Proof.
  intros n c w1. revert c.
  induction w1 as [|a rest IH]; intros c w2.
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(** 8. Complement preserves start state *)
Theorem dfa_complement_start : forall d,
  dfa_start (dfa_complement d) = dfa_start d.
Proof. reflexivity. Qed.

(** 9. Complement preserves transition function *)
Theorem dfa_complement_trans : forall d,
  dfa_trans (dfa_complement d) = dfa_trans d.
Proof. reflexivity. Qed.

(** 10. Complement does not change the run *)
Theorem dfa_complement_run : forall d s w,
  dfa_run (dfa_complement d) s w = dfa_run d s w.
Proof.
  intros d s w. revert s.
  induction w as [|a rest IH]; intros s.
  - reflexivity.
  - simpl. apply IH.
Qed.

(** 11. Acceptance of empty word depends only on start state *)
Theorem dfa_accepts_empty_word : forall d,
  dfa_accepts d [] = in_accept (dfa_accept d) (dfa_start d).
Proof. unfold dfa_accepts. simpl. reflexivity. Qed.

(** 12. Even parity DFA accepts the empty word *)
Theorem even_parity_empty : dfa_accepts even_parity_dfa [] = true.
Proof. reflexivity. Qed.

(** 13. Even parity DFA rejects [0;1] (one 1 = odd) *)
Theorem even_parity_01 : dfa_accepts even_parity_dfa [0; 1] = false.
Proof. reflexivity. Qed.

(** 14. Even parity DFA accepts [0;1;1] (two 1s = even) *)
Theorem even_parity_011 : dfa_accepts even_parity_dfa [0; 1; 1] = true.
Proof. reflexivity. Qed.

(** 15. Even parity DFA rejects [1] *)
Theorem even_parity_1 : dfa_accepts even_parity_dfa [1] = false.
Proof. reflexivity. Qed.

(** 16. NFA accepts [0;1] (ends with 1) *)
Theorem nfa_ends1_accept : nfa_accepts ends_with_1_nfa [0; 1] = true.
Proof. reflexivity. Qed.

(** 17. NFA rejects [1;0] (ends with 0) *)
Theorem nfa_ends1_reject : nfa_accepts ends_with_1_nfa [1; 0] = false.
Proof. reflexivity. Qed.

(** 18. DFA run on a single symbol is one transition *)
Theorem dfa_run_single : forall d s a, dfa_run d s [a] = dfa_trans d s a.
Proof. reflexivity. Qed.

(** 19. NFA rejects the empty word (no state 1 in start) *)
Theorem nfa_ends1_empty : nfa_accepts ends_with_1_nfa [] = false.
Proof. reflexivity. Qed.

(** 20. Even parity DFA accepts [1;1] (two 1s = even) *)
Theorem even_parity_11 : dfa_accepts even_parity_dfa [1; 1] = true.
Proof. reflexivity. Qed.
