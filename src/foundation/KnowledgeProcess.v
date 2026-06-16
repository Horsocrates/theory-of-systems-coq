(** * KnowledgeProcess.v — F-39: knowledge-how = witnessing a process; anti-omniscience as a theorem

    Formalizes the derivation "Знание" (Книги/Теория Знания/Знание.md, §7+§9): knowledge of a
    process at step n is the PREFIX of observations; the target theorem is that COMPLETE
    knowledge of an unbounded process does not exist as a completed object — every stage is
    knowable, knowledge grows monotonically, but the completed totality is never an object.
    This is the epistemological copy of "Q-bar is a process, not a wall" / potential-vs-actual
    infinity, stated in ToS's process vocabulary and machine-checked, with the connections to
    the existing bricks made REAL (imported), not asserted.

    ============================== E/R/R разбор ==============================
    Rules (L5, the generative rule first):
      R2 (ground): a record arises only by PASSING the observation ladder in order —
                   knowledge_how p n := prefix p n; the horizontal Law of Order
                   (stage_in_record: position m of the record = observe p m).
      R5 (irrevocability / the L5 arrow): the record only APPENDS —
                   knowledge_how p (S n) = knowledge_how p n ++ [observe p n] (definitional);
                   the witnessed is not unmade -> a literal instance of
                   L5_Arrow.cannot_unmake_distinction (Part III).
      R4 (growing field): the field is always ahead of the records (budget_incomplete:
                   for every budget n there is an un-witnessed stage, namely n).
    Roles (L4):
      witnessed p n m = "stage m has been witnessed by budget n" (= m < |record|).  The budget
      is the width-limiter (attention: one stage per step, R3).  "Completed object of
      knowledge" known_as_object (exists N, forall m) versus "all-encompassing along the way"
      known_along_the_way (forall m, exists N) — exactly the quantifier swap.  Transfer (§6)
      = the role of a FOUNDED chain of witnessings (bridge to F-38 GroundedOrderedStructure).
    Elements (L1+P4):
      a process p : nat -> A (P4: unfolded to FINITE depth); the observation observe p n; the
      finite record (a list); the witnessed indices seq 0 n.
    P4 diagnostic (could it be otherwise under the same rules?):
      NO: with R3 (finite step) + R4 (field grows both ways) you cannot catch up BY
      CONSTRUCTION — ~ known_as_object.  "Omniscience-as-object" reifies a role-limit into an
      Element — the same category error as actualizing potential infinity.  The strict form
      survives: known_along_the_way (all-encompassing ALONG THE WAY).
    Generators: one diagonal generator negb b <> b (= circular_dep_is_paradox, Roles.v §XII)
      yields the non-transmissibility of knowledge-how — a finite record UNDERDETERMINES the
      process (finite_record_underdetermines).  The same diagonal as uncountability and halting.
    Nested: знание-о is the CONTENT; присутствие/знание-как are the two POSITIONS yielding it
      (KnowledgeInsight §8 — NOT «three kinds»); the formal weight is the contrast знание-о
      (completed-value-object, transfers by copying) vs the lived passing/прохождение (does not
      transfer, only passing-through).

    Honest scope: the anti-omniscience SKELETON is the unboundedness of nat in epistemic dress
    (forall-exists holds, exists-forall fails) — no heavy new theorem.  The load-bearing PROCESS
    content is (a) knowledge = the ordered witnessed record (stage_in_record), and (b)
    knowledge-how is not a transmissible object: a finite record underdetermines the process
    (finite_record_underdetermines, the diagonal).  House style (cf. MetaPairStrength).

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Lia Bool Setoid Relations.
Import ListNotations.
From ToS Require Import foundation.L5_Arrow.                  (* cannot_unmake_distinction, L5_pres, has_dist' — R5 *)
From ToS Require Import foundation.GroundedOrderedStructure.  (* meta_pair_demands — R6 founded transfer chain *)

(* ===================================================================== *)
(*  PART 0 — process + record primitives                                  *)
(*  (replicated verbatim from ProcessGeneral.v — same defs; avoids        *)
(*   dragging the Q/CauchyReal/Core subtree, stale-.vo safety per          *)
(*   CLAUDE.md 2026-03.)                                                    *)
(* ===================================================================== *)

Definition GenProcess (A : Type) := nat -> A.

(** Observation: read the process at step n. *)
Definition observe {A : Type} (p : GenProcess A) (n : nat) : A := p n.

(** Prefix: the first n observations, in order (the witnessed record). *)
Fixpoint prefix {A : Type} (p : GenProcess A) (n : nat) : list A :=
  match n with
  | O   => []
  | S k => prefix p k ++ [p k]
  end.

Lemma prefix_length : forall (A : Type) (p : GenProcess A) (n : nat),
  length (prefix p n) = n.
Proof.
  intros A p n. induction n as [|k IH].
  - reflexivity.
  - simpl. rewrite app_length. simpl. rewrite IH. lia.
Qed.

Lemma prefix_nth : forall (A : Type) (p : GenProcess A) (n k : nat) (d : A),
  (k < n)%nat -> nth k (prefix p n) d = p k.
Proof.
  intros A p n. induction n as [|n' IH]; intros k d Hk.
  - lia.
  - simpl. destruct (Nat.lt_ge_cases k n') as [Hlt | Hge].
    + rewrite app_nth1 by (rewrite prefix_length; lia).
      apply IH. exact Hlt.
    + assert (Heq : k = n') by lia. subst k.
      rewrite app_nth2 by (rewrite prefix_length; lia).
      rewrite prefix_length. replace (n' - n')%nat with 0%nat by lia.
      simpl. reflexivity.
Qed.

(** The record depends only on the stages STRICTLY BELOW n (used for transfer). *)
Lemma prefix_ext : forall (A : Type) (p q : GenProcess A) (n : nat),
  (forall k, (k < n)%nat -> p k = q k) -> prefix p n = prefix q n.
Proof.
  intros A p q n. induction n as [|n' IH]; intro H.
  - reflexivity.
  - simpl.
    assert (Hpre : prefix p n' = prefix q n').
    { apply IH. intros k Hk. apply H. lia. }
    assert (Hpt : p n' = q n'). { apply H. lia. }
    rewrite Hpre, Hpt. reflexivity.
Qed.

(* ===================================================================== *)
(*  PART I — knowledge-how = the witnessed record; it only grows (R2,R5)   *)
(* ===================================================================== *)

(** Knowledge-how accumulated through budget n: the witnessed record. *)
Definition knowledge_how {A : Type} (p : GenProcess A) (n : nat) : list A := prefix p n.

(** ★ R5 (the L5 arrow): the record only APPENDS — never rewritten. Definitional. *)
Lemma knowledge_grows : forall (A : Type) (p : GenProcess A) (n : nat),
  knowledge_how p (S n) = knowledge_how p n ++ [observe p n].
Proof. reflexivity. Qed.

Lemma knowledge_length : forall (A : Type) (p : GenProcess A) (n : nat),
  length (knowledge_how p n) = n.
Proof. intros. apply prefix_length. Qed.

(** R5: a later record EXTENDS an earlier one — the past is an initial segment. *)
Lemma record_is_prefix : forall (A : Type) (p : GenProcess A) (n m : nat),
  (n <= m)%nat -> exists tl, knowledge_how p m = knowledge_how p n ++ tl.
Proof.
  intros A p n m H. induction H as [|m' Hle IH].
  - exists []. rewrite app_nil_r. reflexivity.
  - destruct IH as [tl Htl]. exists (tl ++ [observe p m']).
    rewrite knowledge_grows, Htl. rewrite <- app_assoc. reflexivity.
Qed.

(** ★ R2 (passing-through): stage m, once within budget, sits at position m of the
    record — witnessing IS recording, in order. *)
Lemma stage_in_record : forall (A : Type) (p : GenProcess A) (n m : nat) (d : A),
  (m < n)%nat -> nth m (knowledge_how p n) d = observe p m.
Proof. intros. unfold knowledge_how, observe. apply prefix_nth. exact H. Qed.

(* ===================================================================== *)
(*  PART II — witnessed = recorded; R1 knowable, R4 ahead, anti-omniscience *)
(* ===================================================================== *)

(** "stage m has been witnessed by budget n": the record is long enough to hold it. *)
Definition witnessed {A : Type} (p : GenProcess A) (n m : nat) : Prop :=
  (m < length (knowledge_how p n))%nat.

Lemma witnessed_iff : forall (A : Type) (p : GenProcess A) (n m : nat),
  witnessed p n m <-> (m < n)%nat.
Proof. intros. unfold witnessed. rewrite knowledge_length. tauto. Qed.

(** R1 (knowability): every stage is witnessed at some budget (namely S m). *)
Lemma every_stage_knowable : forall (A : Type) (p : GenProcess A) (m : nat),
  witnessed p (S m) m.
Proof. intros. rewrite witnessed_iff. lia. Qed.

(** R5 (monotone, irrevocable): once witnessed, witnessed at every larger budget. *)
Lemma witnessing_monotone : forall (A : Type) (p : GenProcess A) (n m : nat),
  witnessed p n m -> forall n', (n <= n')%nat -> witnessed p n' m.
Proof. intros A p n m H n' Hle. rewrite witnessed_iff in H. rewrite witnessed_iff. lia. Qed.

(** ★ R4 (growing field): no budget has witnessed everything — the field is always ahead. *)
Lemma budget_incomplete : forall (A : Type) (p : GenProcess A) (n : nat),
  exists m, ~ witnessed p n m.
Proof. intros. exists n. rewrite witnessed_iff. lia. Qed.

(** The two ways of "knowing the whole process": along the way vs as a completed object. *)
Definition known_along_the_way {A : Type} (p : GenProcess A) : Prop :=
  forall m, exists N, witnessed p N m.
Definition known_as_object {A : Type} (p : GenProcess A) : Prop :=
  exists N, forall m, witnessed p N m.

(** All-encompassing ALONG THE WAY holds (forall-exists). *)
Lemma along_the_way_holds : forall (A : Type) (p : GenProcess A), known_along_the_way p.
Proof. intros A p m. exists (S m). apply every_stage_knowable. Qed.

(** ★★ Anti-omniscience: knowledge-how of an unbounded process is never a completed object
    (exists-forall fails). §7 of the derivation. *)
Theorem as_object_fails : forall (A : Type) (p : GenProcess A), ~ known_as_object p.
Proof. intros A p [N H]. specialize (H N). rewrite witnessed_iff in H. lia. Qed.

(** ★★★ The epistemological "process, not wall": all-encompassing along the way, yet no
    completed totality — the exact forall-exists / exists-forall asymmetry. *)
Theorem process_not_wall_epistemic : forall (A : Type) (p : GenProcess A),
  known_along_the_way p /\ ~ known_as_object p.
Proof. intros. split; [ apply along_the_way_holds | apply as_object_fails ]. Qed.

(* ===================================================================== *)
(*  PART III — R5 as an instance of the L5 arrow (cannot_unmake_distinction) *)
(* ===================================================================== *)

(** The witnessed indices through budget n, as an L5_Arrow distinction set. *)
Definition known_indices {A : Type} (p : GenProcess A) (n : nat) : DistSet' := seq 0 n.

Lemma has_dist_known : forall (A : Type) (p : GenProcess A) (n m : nat),
  has_dist' (known_indices p n) m = true <-> (m < n)%nat.
Proof.
  intros A p n m. unfold known_indices, has_dist'. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply Nat.eqb_eq in Heq. subst x.
    apply in_seq in Hin. lia.
  - intro Hm. exists m. split.
    + apply in_seq. lia.
    + apply Nat.eqb_refl.
Qed.

(** Knowledge is an L5-preserving distinction system: each step's known set <= the next. *)
Lemma known_is_L5_pres : forall (A : Type) (p : GenProcess A), L5_pres (known_indices p).
Proof.
  intros A p K. unfold dist_subset'. intros d Hd.
  rewrite has_dist_known in Hd. rewrite has_dist_known. lia.
Qed.

(** ★ Irrevocability of knowledge, exhibited AS an instance of L5_Arrow.cannot_unmake_distinction:
    once a stage is witnessed it stays witnessed at every later budget (same content as
    witnessing_monotone, but routed through the existing arrow brick — the bridge is real). *)
Theorem knowledge_irrevocable : forall (A : Type) (p : GenProcess A) (K m : nat),
  witnessed p K m -> forall K', (K <= K')%nat -> witnessed p K' m.
Proof.
  intros A p K m H K' Hle.
  assert (Hwit : has_dist' (known_indices p K) m = true)
    by (rewrite has_dist_known; rewrite witnessed_iff in H; exact H).
  pose proof (cannot_unmake_distinction (known_indices p) K m (known_is_L5_pres A p) Hwit K' Hle) as Hk'.
  rewrite has_dist_known in Hk'. rewrite witnessed_iff. exact Hk'.
Qed.

(* ===================================================================== *)
(*  PART IV — knowledge-how is NOT a transmissible object (the diagonal)   *)
(*                                                                         *)
(*  What transfer hands over is a finite record (a prefix).  Two processes *)
(*  can share the WHOLE transmitted record yet diverge immediately after — *)
(*  so the record (knowledge-THAT of the process) does not contain the     *)
(*  process (knowledge-HOW).  §6: knowledge-how is taken only by passing.   *)
(* ===================================================================== *)

(** General form: any value [a] distinct from observe p N produces a rival process
    sharing the budget-N record but differing at stage N. *)
Theorem finite_record_underdetermines :
  forall (A : Type) (p : GenProcess A) (N : nat) (a : A), a <> observe p N ->
    exists q : GenProcess A,
      knowledge_how p N = knowledge_how q N /\ observe p N <> observe q N.
Proof.
  intros A p N a Ha.
  exists (fun m => if Nat.eq_dec m N then a else p m). split.
  - unfold knowledge_how. apply prefix_ext. intros k Hk. simpl.
    destruct (Nat.eq_dec k N) as [Heq | Hne]; [ exfalso; lia | reflexivity ].
  - unfold observe. simpl. destruct (Nat.eq_dec N N) as [e | n0].
    + intro Hc. apply Ha. unfold observe. symmetry. exact Hc.
    + exfalso. apply n0. reflexivity.
Qed.

(** The project's diagonal core: negation has no fixed point.
    (= cs/HaltingRoleLimit.negb_no_fixpoint = circular_dep_is_paradox, Roles.v §XII.) *)
Lemma negb_no_fixpoint : forall b : bool, b <> negb b.
Proof. intros [] H; discriminate. Qed.

(** ★ Diagonal instance: over bool the witness is supplied with NO hypothesis — the same
    diagonal that drives uncountability and undecidability forces underdetermination here. *)
Corollary record_underdetermines_bool :
  forall (p : GenProcess bool) (N : nat),
    exists q : GenProcess bool,
      knowledge_how p N = knowledge_how q N /\ observe p N <> observe q N.
Proof.
  intros p N.
  apply (finite_record_underdetermines bool p N (negb (observe p N))).
  pose proof (negb_no_fixpoint (observe p N)) as Hb. congruence.
Qed.

(* ===================================================================== *)
(*  PART V — transfer along a FOUNDED chain (§6); that-transfers, how-not  *)
(* ===================================================================== *)

(** §6: transfer = a record made on the basis of another's record.  Its ground is a
    FOUNDED chain of witnessings — no infinite regress, no cycle, a root witnessing exists.
    Exactly the meta-pair demand (GroundedOrderedStructure / F-38). *)
Theorem founded_testimony_chain :
  forall (R : Type) (testifies : R -> R -> Prop), well_founded testifies ->
    (forall r, ~ testifies r r)                                      (* no self-grounded testimony *)
    /\ (forall r, ~ clos_trans R testifies r r)                      (* no citation cycle *)
    /\ (forall f : nat -> R, ~ (forall n, testifies (f (S n)) (f n))). (* no infinite regress: a root exists *)
Proof.
  intros R testifies WF.
  destruct (meta_pair_demands R testifies WF) as [H1 [_ [_ [H4 H5]]]].
  split; [ exact H1 | split; [ exact H4 | exact H5 ] ].
Qed.

(** Knowledge-THAT (a completed fact = a value) propagates along the chain: copied
    root -> every node.  Modeled as a value constant under the per-edge copy rule. *)
Theorem knowledge_that_transfers :
  forall (A : Type) (val : nat -> A) (v : A),
    (forall n, val (S n) = val n) ->   (* the transfer/copy rule along each edge *)
    val 0%nat = v ->
    forall n, val n = v.
Proof.
  intros A val v Hcopy H0 n. induction n as [|n IH].
  - exact H0.
  - rewrite Hcopy. exact IH.
Qed.

(** ★ The TYPE ASYMMETRY (§6): knowledge-THAT transfers (a completed value copies along a
    founded chain), knowledge-HOW does NOT (the transmitted finite record underdetermines the
    process), and the transfer chain itself is founded (no cycle). *)
Theorem transfer_asymmetry :
  (forall (A : Type) (val : nat -> A) (v : A),
      (forall n, val (S n) = val n) -> val 0%nat = v -> forall n, val n = v)
  /\ (forall (p : GenProcess bool) (N : nat),
        exists q, knowledge_how p N = knowledge_how q N /\ observe p N <> observe q N)
  /\ (forall (R : Type) (t : R -> R -> Prop), well_founded t -> forall r, ~ clos_trans R t r r).
Proof.
  split; [ exact knowledge_that_transfers | split ].
  - exact record_underdetermines_bool.
  - intros R t WF. destruct (founded_testimony_chain R t WF) as [_ [Hcyc _]]. exact Hcyc.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the four-fold structure of knowing an unbounded process     *)
(* ===================================================================== *)

(** ★★★ Knowing an unbounded process: (R1) knowable along the way; (R5) irrevocable /
    monotone; (R4) the field is always ahead; (§7) yet never a completed totality. *)
Theorem knowledge_process_capstone :
  forall (A : Type) (p : GenProcess A),
    (forall m, exists N, witnessed p N m)                                          (* R1 + §7 *)
    /\ (forall n m, witnessed p n m -> forall n', (n <= n')%nat -> witnessed p n' m) (* R5 *)
    /\ (forall n, exists m, ~ witnessed p n m)                                      (* R4 *)
    /\ ~ (exists N, forall m, witnessed p N m).                                     (* §7 *)
Proof.
  intros A p. split; [ | split; [ | split ] ].
  - apply along_the_way_holds.
  - intros n m H n' Hle. exact (knowledge_irrevocable A p n m H n' Hle).
  - apply budget_incomplete.
  - apply as_object_fails.
Qed.

Print Assumptions knowledge_process_capstone.
Print Assumptions process_not_wall_epistemic.
Print Assumptions finite_record_underdetermines.
Print Assumptions transfer_asymmetry.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  24 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Knowledge-how of a process = the witnessed record (prefix); it only       *)
(*  appends (R5, = L5_Arrow.cannot_unmake_distinction), every stage is        *)
(*  knowable (R1) but no budget completes it (R4): all-encompassing ALONG     *)
(*  THE WAY (forall-exists) holds while the completed object (exists-forall)  *)
(*  fails — the epistemological "process, not wall".  Knowledge-THAT (a       *)
(*  completed value) transfers along a FOUNDED chain (§6, = meta_pair_demands)*)
(*  but knowledge-HOW does not: a finite record underdetermines the process   *)
(*  (the project's diagonal negb b <> b).  Closes FORMALIZATION-BACKLOG F-39. *)
(* ========================================================================= *)
