(* ========================================================================= *)
(*                    COUNTABILITY OF RATIONAL NUMBERS                       *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization                           *)
(*                                                                           *)
(*  PURPOSE: Demonstrate that ℚ is countable (bijection ℕ ↔ ℚ⁺)              *)
(*  This provides CONTRAST with the non-surjectivity theorem:                *)
(*    - ℚ as a set of points is countable                                    *)
(*    - ℚ-processes (Cauchy sequences) are NOT enumerable                    *)
(*                                                                           *)
(*  METHOD: Calkin-Wilf tree enumeration                                     *)
(*                                                                           *)
(*  STATUS: 100% COMPLETE (0 Admitted, 0 axioms, fully constructive)         *)
(*                                                                           *)
(*  AXIOMS: NONE (not even classic!) - fully constructive                    *)
(*                                                                           *)
(*  Author: Horsocrates | Date: January 2026                                 *)
(* ========================================================================= *)

Require Import Coq.QArith.QArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.Pnat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope positive_scope.

(* ========================================================================= *)
(* SECTION 1: POSITIVE RATIONALS AS PAIRS                                    *)
(* ========================================================================= *)

(**
  We work with positive rationals represented as pairs (p, q) where
  p, q : positive. This avoids the complexity of signs and zero.
  
  The full bijection ℕ ↔ ℚ follows by standard techniques.
*)

Definition QPos := (positive * positive)%type.

Definition qpos_to_Q (q : QPos) : Q :=
  let (p, r) := q in (Z.pos p # r).

(* Equality on QPos is decidable *)
Definition qpos_eq_dec : forall x y : QPos, {x = y} + {x <> y}.
Proof.
  intros [p1 q1] [p2 q2].
  destruct (Pos.eq_dec p1 p2); destruct (Pos.eq_dec q1 q2); subst.
  - left. reflexivity.
  - right. intros H. injection H. auto.
  - right. intros H. injection H. auto.
  - right. intros H. injection H. auto.
Defined.

(* ========================================================================= *)
(* SECTION 2: CALKIN-WILF TREE OPERATIONS                                    *)
(* ========================================================================= *)

(**
  The Calkin-Wilf tree enumerates all positive rationals exactly once
  (in lowest terms). The tree is defined by:
  
    Root: 1/1
    Left child of a/b: a/(a+b)
    Right child of a/b: (a+b)/b
  
  KEY PROPERTY: gcd(a,b) = 1 is preserved at every node.
*)

(* Left child: a/b -> a/(a+b) *)
Definition cw_left (ab : QPos) : QPos :=
  let (a, b) := ab in (a, a + b).

(* Right child: a/b -> (a+b)/b *)
Definition cw_right (ab : QPos) : QPos :=
  let (a, b) := ab in (a + b, b).

(* The root *)
Definition cw_root : QPos := (1, 1).

(* ========================================================================= *)
(* SECTION 3: NAVIGATION VIA BINARY ENCODING                                 *)
(* ========================================================================= *)

(**
  We encode tree paths as positive numbers:
    - 1 = root
    - 2n = left child of path n  
    - 2n+1 = right child of path n
  
  This gives a bijection positive <-> tree nodes.
*)

(* Navigate to node given by positive number *)
Fixpoint cw_node (p : positive) : QPos :=
  match p with
  | xH => cw_root                           (* 1 = root *)
  | xO p' => cw_left (cw_node p')           (* 2p' = left child *)
  | xI p' => cw_right (cw_node p')          (* 2p'+1 = right child *)
  end.

(* Main enumeration: nat -> QPos *)
Definition enum_QPos (n : nat) : QPos :=
  cw_node (Pos.of_nat (S n)).

(* First few values for verification:
   enum_QPos 0 = cw_node 1 = (1,1) = 1/1
   enum_QPos 1 = cw_node 2 = cw_left (1,1) = (1,2) = 1/2
   enum_QPos 2 = cw_node 3 = cw_right (1,1) = (2,1) = 2/1
   enum_QPos 3 = cw_node 4 = cw_left (cw_node 2) = cw_left (1,2) = (1,3) = 1/3
   enum_QPos 4 = cw_node 5 = cw_right (cw_node 2) = cw_right (1,2) = (3,2) = 3/2
*)

(* ========================================================================= *)
(* SECTION 4: INVERSE - PATH FROM NODE TO ROOT                               *)
(* ========================================================================= *)

(**
  Given (a, b) with gcd = 1, find the positive p such that cw_node p = (a, b).
  
  Algorithm: trace back to root
    - If a = b = 1: return 1
    - If a < b: we are a left child, recurse on (a, b-a), then multiply by 2
    - If a > b: we are a right child, recurse on (a-b, b), then multiply by 2 and add 1
*)

Fixpoint path_to_node_fuel (fuel : nat) (a b : positive) : positive :=
  match fuel with
  | O => xH  (* fallback *)
  | S fuel' =>
      if (a =? b)%positive then xH
      else if (a <? b)%positive 
           then xO (path_to_node_fuel fuel' a (b - a))   (* left child *)
           else xI (path_to_node_fuel fuel' (a - b) b)   (* right child *)
  end.

Definition path_to_node (ab : QPos) : positive :=
  let (a, b) := ab in
  path_to_node_fuel (Pos.to_nat a + Pos.to_nat b) a b.

Definition index_of_QPos (ab : QPos) : nat :=
  Pos.to_nat (path_to_node ab) - 1.

(* ========================================================================= *)
(* SECTION 5: GCD PRESERVATION                                               *)
(* ========================================================================= *)

Lemma gcd_cw_left : forall a b,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  Z.gcd (Z.pos a) (Z.pos (a + b)) = 1%Z.
Proof.
  intros a b Hgcd.
  rewrite Pos2Z.inj_add.
  rewrite Z.add_comm.
  rewrite Z.gcd_add_diag_r.
  exact Hgcd.
Qed.

Lemma gcd_cw_right : forall a b,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  Z.gcd (Z.pos (a + b)) (Z.pos b) = 1%Z.
Proof.
  intros a b Hgcd.
  rewrite Pos2Z.inj_add.
  rewrite Z.gcd_comm.
  rewrite Z.gcd_add_diag_r.
  rewrite Z.gcd_comm.
  exact Hgcd.
Qed.

Theorem cw_node_coprime : forall p,
  let (a, b) := cw_node p in
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z.
Proof.
  induction p; simpl.
  - (* xI p = right child *)
    destruct (cw_node p) as [a b] eqn:Heq.
    apply gcd_cw_right. exact IHp.
  - (* xO p = left child *)
    destruct (cw_node p) as [a b] eqn:Heq.
    apply gcd_cw_left. exact IHp.
  - (* xH = root *)
    reflexivity.
Qed.

Corollary enum_coprime : forall n,
  let (a, b) := enum_QPos n in
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z.
Proof.
  intros n. unfold enum_QPos. apply cw_node_coprime.
Qed.

(* ========================================================================= *)
(* SECTION 6: INJECTIVITY                                                    *)
(* ========================================================================= *)

(* cw_left and cw_right are injective *)
Lemma cw_left_injective : forall x y, cw_left x = cw_left y -> x = y.
Proof.
  intros [a1 b1] [a2 b2] H.
  unfold cw_left in H. injection H as Ha Hb.
  assert (b1 = b2) by lia. subst. reflexivity.
Qed.

Lemma cw_right_injective : forall x y, cw_right x = cw_right y -> x = y.
Proof.
  intros [a1 b1] [a2 b2] H.
  unfold cw_right in H. injection H as Ha Hb.
  assert (a1 = a2) by lia. subst. reflexivity.
Qed.

(* cw_left and cw_right have disjoint ranges (except root) *)
Lemma cw_left_right_disjoint : forall x y,
  cw_left x = cw_right y -> 
  (* This can only happen in degenerate cases *)
  let (a1, b1) := x in
  let (a2, b2) := y in
  (a1 = a2 + b2 /\ a1 + b1 = b2)%positive.
Proof.
  intros [a1 b1] [a2 b2] H.
  unfold cw_left, cw_right in H.
  injection H as Ha Hb.
  split; lia.
Qed.

(* Key lemma: in a coprime node, first component determines child type *)
Lemma coprime_child_determinable : forall a b,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  (a < b)%positive \/ (b < a)%positive \/ (a = b /\ a = 1%positive).
Proof.
  intros a b Hgcd.
  destruct (Pos.compare_spec a b) as [Heq | Hlt | Hgt].
  - (* a = b *)
    right. right. split. exact Heq.
    (* gcd(a,a) = a = 1 *)
    subst. rewrite Z.gcd_diag in Hgcd.
    destruct b; simpl in Hgcd; try discriminate. reflexivity.
  - left. exact Hlt.
  - right. left. exact Hgt.
Qed.

(* cw_node is injective *)
Theorem cw_node_injective : forall p q, cw_node p = cw_node q -> p = q.
Proof.
  induction p; destruct q; simpl; intros H.
  - (* xI p, xI q *) f_equal. apply IHp. apply cw_right_injective. exact H.
  - (* xI p, xO q *) 
    exfalso.
    destruct (cw_node p) as [ap bp] eqn:Hp.
    destruct (cw_node q) as [aq bq] eqn:Hq.
    unfold cw_right, cw_left in H.
    injection H as Ha Hb.
    (* We have ap + bp = aq and bq = aq + bq, contradiction with coprimality *)
    pose proof (cw_node_coprime p) as Gp. rewrite Hp in Gp.
    pose proof (cw_node_coprime q) as Gq. rewrite Hq in Gq.
    (* ap + bp = aq, bp = aq + bq *)
    (* So bp = ap + bp + bq, hence ap + bq = 0, impossible for positive *)
    lia.
  - (* xI p, xH *)
    destruct (cw_node p) as [ap bp].
    unfold cw_right in H. injection H as Ha Hb.
    (* ap + bp = 1, bp = 1, so ap = 0, impossible *)
    lia.
  - (* xO p, xI q *)
    exfalso.
    destruct (cw_node p) as [ap bp] eqn:Hp.
    destruct (cw_node q) as [aq bq] eqn:Hq.
    unfold cw_left, cw_right in H.
    injection H as Ha Hb.
    lia.
  - (* xO p, xO q *) f_equal. apply IHp. apply cw_left_injective. exact H.
  - (* xO p, xH *)
    destruct (cw_node p) as [ap bp].
    unfold cw_left in H. injection H as Ha Hb.
    (* ap = 1, ap + bp = 1, so bp = 0, impossible *)
    lia.
  - (* xH, xI q *)
    destruct (cw_node q) as [aq bq].
    unfold cw_right in H. injection H as Ha Hb.
    lia.
  - (* xH, xO q *)
    destruct (cw_node q) as [aq bq].
    unfold cw_left in H. injection H as Ha Hb.
    lia.
  - (* xH, xH *) reflexivity.
Qed.

Theorem enum_injective : forall n m, enum_QPos n = enum_QPos m -> n = m.
Proof.
  intros n m H.
  unfold enum_QPos in H.
  apply cw_node_injective in H.
  apply Nat2Pos.inj in H; lia.
Qed.

(* ========================================================================= *)
(* SECTION 7: SURJECTIVITY                                                   *)
(* ========================================================================= *)

(* --- Helper: cw_node components are always >= 1 (trivial for positive) --- *)

Lemma cw_node_pos : forall p,
  let (a, b) := cw_node p in
  (Pos.to_nat a >= 1 /\ Pos.to_nat b >= 1)%nat.
Proof.
  intros p. destruct (cw_node p) as [a b].
  split; apply Pos2Nat.is_pos.
Qed.

(* --- Helper: path_to_node_fuel gives correct result with sufficient fuel --- *)

Lemma path_fuel_cw_node : forall p fuel,
  let (a, b) := cw_node p in
  (fuel >= Pos.to_nat a + Pos.to_nat b)%nat ->
  path_to_node_fuel fuel a b = p.
Proof.
  induction p; intros fuel.
  - (* p = xI p' : right child *)
    simpl cw_node.
    destruct (cw_node p) as [a b] eqn:Heq.
    unfold cw_right.
    intros Hfuel.
    (* fuel >= Pos.to_nat (a+b) + Pos.to_nat b, which is >= 2, so fuel = S fuel' *)
    destruct fuel as [| fuel'].
    { exfalso. rewrite Pos2Nat.inj_add in Hfuel.
      pose proof (Pos2Nat.is_pos a). pose proof (Pos2Nat.is_pos b). lia. }
    simpl path_to_node_fuel.
    (* a+b =? b is false because a > 0 *)
    destruct ((a + b =? b)%positive) eqn:E1.
    { apply Pos.eqb_eq in E1. lia. }
    (* a+b <? b is false because a+b > b *)
    destruct ((a + b <? b)%positive) eqn:E2.
    { apply Pos.ltb_lt in E2. lia. }
    (* recurse on (a+b - b, b) = (a, b) *)
    rewrite Pos.add_sub.
    f_equal.
    apply IHp.
    rewrite Pos2Nat.inj_add in Hfuel.
    pose proof (Pos2Nat.is_pos b). lia.
  - (* p = xO p' : left child *)
    simpl cw_node.
    destruct (cw_node p) as [a b] eqn:Heq.
    unfold cw_left.
    intros Hfuel.
    (* fuel >= Pos.to_nat a + Pos.to_nat (a+b), which is >= 2 *)
    destruct fuel as [| fuel'].
    { exfalso. rewrite Pos2Nat.inj_add in Hfuel.
      pose proof (Pos2Nat.is_pos a). pose proof (Pos2Nat.is_pos b). lia. }
    simpl path_to_node_fuel.
    (* a =? a+b is false because b > 0 *)
    destruct ((a =? a + b)%positive) eqn:E1.
    { apply Pos.eqb_eq in E1. lia. }
    (* a <? a+b is true *)
    destruct ((a <? a + b)%positive) eqn:E2.
    2:{ apply Pos.ltb_ge in E2. pose proof (Pos.lt_add_r a b). lia. }
    (* recurse on (a, a+b - a) = (a, b) *)
    rewrite Pos.add_comm. rewrite Pos.add_sub.
    f_equal.
    apply IHp.
    rewrite Pos2Nat.inj_add in Hfuel.
    pose proof (Pos2Nat.is_pos a). lia.
  - (* p = xH : root *)
    simpl. intros Hfuel.
    destruct fuel as [| fuel'].
    { lia. }
    simpl. reflexivity.
Qed.

(* Round-trip lemma: path_to_node inverts cw_node *)
Lemma path_cw_node_roundtrip : forall p,
  path_to_node (cw_node p) = p.
Proof.
  intros p.
  unfold path_to_node.
  pose proof (path_fuel_cw_node p (let (a, b) := cw_node p in Pos.to_nat a + Pos.to_nat b)) as H.
  destruct (cw_node p) as [a b] eqn:Heq in *.
  apply H. lia.
Qed.

(* --- Helper: reverse round-trip for coprime pairs --- *)
(* cw_node (path_to_node (a,b)) = (a,b) when gcd(a,b) = 1 *)

Lemma path_fuel_coprime_fuel_mono : forall fuel a b,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  (fuel >= Pos.to_nat a + Pos.to_nat b)%nat ->
  cw_node (path_to_node_fuel fuel a b) = (a, b).
Proof.
  induction fuel as [fuel IH] using lt_wf_ind.
  intros a b Hgcd Hfuel.
  destruct fuel as [| fuel'].
  { exfalso. pose proof (Pos2Nat.is_pos a). pose proof (Pos2Nat.is_pos b). lia. }
  simpl path_to_node_fuel.
  destruct (Pos.eqb_spec a b) as [Hab_eq | Hab_neq].
  - (* a = b: must have a = b = 1 *)
    subst. rewrite Z.gcd_diag in Hgcd.
    destruct b; simpl in Hgcd; try discriminate.
    simpl. reflexivity.
  - (* a <> b *)
    destruct (Pos.ltb_spec a b) as [Ha_lt | Ha_ge].
    + (* a < b: left child, recurse on (a, b - a) *)
      simpl cw_node. unfold cw_left.
      (* Need: cw_node (path_to_node_fuel fuel' a (b - a)) = (a', b') *)
      (* and then a' = a, a' + b' = b, i.e. b' = b - a *)
      assert (Hsub : (a + (b - a) = b)%positive).
      { rewrite Pos.add_comm. apply Pos.sub_add. exact Ha_lt. }
      (* By IH, cw_node (path_to_node_fuel fuel' a (b-a)) = (a, b-a) *)
      assert (Hgcd' : Z.gcd (Z.pos a) (Z.pos (b - a)) = 1%Z).
      { rewrite Pos2Z.inj_sub by exact Ha_lt.
        rewrite Z.gcd_sub_diag_r. exact Hgcd. }
      assert (Hfuel' : (fuel' >= Pos.to_nat a + Pos.to_nat (b - a))%nat).
      { rewrite Pos2Nat.inj_sub by exact Ha_lt.
        pose proof (Pos2Nat.is_pos a).
        pose proof (Pos2Nat.is_pos b).
        pose proof (Pos2Nat.is_pos (b - a)).
        lia. }
      rewrite (IH fuel' (Nat.lt_succ_diag_r _) a (b - a) Hgcd' Hfuel').
      rewrite Hsub. reflexivity.
    + (* a >= b, a <> b, so a > b: right child, recurse on (a - b, b) *)
      assert (Hb_lt : (b < a)%positive) by lia.
      simpl cw_node. unfold cw_right.
      assert (Hsub : (a - b + b = a)%positive).
      { apply Pos.sub_add. exact Hb_lt. }
      assert (Hgcd' : Z.gcd (Z.pos (a - b)) (Z.pos b) = 1%Z).
      { rewrite Pos2Z.inj_sub by exact Hb_lt.
        rewrite Z.gcd_comm. rewrite Z.gcd_sub_diag_r.
        rewrite Z.gcd_comm. exact Hgcd. }
      assert (Hfuel' : (fuel' >= Pos.to_nat (a - b) + Pos.to_nat b)%nat).
      { rewrite Pos2Nat.inj_sub by exact Hb_lt.
        pose proof (Pos2Nat.is_pos a).
        pose proof (Pos2Nat.is_pos b).
        lia. }
      rewrite (IH fuel' (Nat.lt_succ_diag_r _) (a - b) b Hgcd' Hfuel').
      rewrite Hsub. reflexivity.
Qed.

Lemma cw_node_path_roundtrip : forall a b,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  cw_node (path_to_node (a, b)) = (a, b).
Proof.
  intros a b Hgcd.
  unfold path_to_node.
  apply path_fuel_coprime_fuel_mono.
  - exact Hgcd.
  - lia.
Qed.

Theorem enum_surjective : forall a b : positive,
  Z.gcd (Z.pos a) (Z.pos b) = 1%Z ->
  exists n : nat, enum_QPos n = (a, b).
Proof.
  intros a b Hgcd.
  exists (index_of_QPos (a, b)).
  unfold enum_QPos, index_of_QPos.
  (* Need: cw_node (Pos.of_nat (S (Pos.to_nat (path_to_node (a,b)) - 1))) = (a,b) *)
  (* Since Pos.to_nat p >= 1, S (Pos.to_nat p - 1) = Pos.to_nat p *)
  assert (Hpos : (Pos.to_nat (path_to_node (a, b)) >= 1)%nat).
  { apply Pos2Nat.is_pos. }
  replace (S (Pos.to_nat (path_to_node (a, b)) - 1)) with
    (Pos.to_nat (path_to_node (a, b))) by lia.
  rewrite Pos2Nat.id.
  apply cw_node_path_roundtrip. exact Hgcd.
Qed.

(* ========================================================================= *)
(* SECTION 8: MAIN THEOREM                                                   *)
(* ========================================================================= *)

Theorem Q_positive_countable :
  (forall n m, enum_QPos n = enum_QPos m -> n = m) /\
  (forall a b, Z.gcd (Z.pos a) (Z.pos b) = 1%Z -> exists n, enum_QPos n = (a, b)).
Proof.
  split.
  - exact enum_injective.
  - exact enum_surjective.
Qed.

(* ========================================================================= *)
(* SECTION 9: AXIOM VERIFICATION                                             *)
(* ========================================================================= *)

Print Assumptions enum_injective.
(* Expected: Closed under the global context (NO AXIOMS!) *)

Print Assumptions enum_coprime.
(* Expected: Closed under the global context (NO AXIOMS!) *)

(* ========================================================================= *)
(* SECTION 10: THE KEY CONTRAST                                              *)
(* ========================================================================= *)

(**
  ============================================================================
  WHY THIS MATTERS FOR THE PAPER
  ============================================================================
  
  THEOREM A (this file): ℚ⁺ is countable.
    There exists a bijection enum_QPos : ℕ → {(a,b) | gcd(a,b)=1}.
    PROOF: Fully constructive, NO AXIOMS.
  
  THEOREM B (ShrinkingIntervals): ℕ → (ℕ → ℚ) is not surjective.
    For any f : ℕ → (ℕ → ℚ), there exists D : ℕ → ℚ with D ≠ f(n) for all n.
    PROOF: Uses only LEM (classic).
  
  NO CONTRADICTION because:
  
  1. A rational q ∈ ℚ is a FINITE object: a pair (numerator, denominator).
     We enumerate all such pairs.
  
  2. A Cauchy PROCESS R : ℕ → ℚ is a FUNCTION.
     Each R(k) is a rational, but R itself is not a rational.
     R is an INFINITE specification of how to compute approximations.
  
  ANALOGY:
    - Words in a finite alphabet are countable.
    - But LANGUAGES (sets of words, or functions ℕ → words) are not.
    - A language is not a word; it's a rule for generating/recognizing words.
  
  In ToS terms:
    - ℚ points = Level 1 Elements (finite objects)
    - Cauchy processes = Level 2 Products (actualized from Level 1)
    - Enumeration = Level 3 operation (mapping ℕ to Level 2)
  
  The non-surjectivity shows: Level 3 cannot capture all of Level 2.
  This is NOT about "sizes" of infinite sets (we reject that language).
  It IS about the structural impossibility of finite specifications 
  capturing all infinite processes.
  ============================================================================
*)
