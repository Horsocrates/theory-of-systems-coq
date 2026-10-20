(* ========================================================================= *)
(*                                                                          *)
(*     CYCLE EXISTENCE IN FINITE PERMUTATIONS VIA L5/mu + PIGEONHOLE        *)
(*                                                                          *)
(*  CLASSICAL THEOREM (folklore):                                           *)
(*    For any permutation sigma of [0..n-1] and any x < n, there exists     *)
(*    k with 1 <= k <= n such that sigma^k(x) = x.                          *)
(*                                                                          *)
(*  CONSTRUCTIVE PROOF (this file):                                        *)
(*    Consider the iterates sigma^0(x), sigma^1(x), ..., sigma^n(x).       *)
(*    These are n+1 values, all in [0..n-1].                                *)
(*    By PIGEONHOLE (constructive via NoDup-bounded-length), some two are   *)
(*    equal: sigma^i(x) = sigma^j(x) for some i < j.                        *)
(*    By INJECTIVITY of sigma^i (composition of injections), sigma^(j-i)(x) *)
(*    = x. So the cycle length divides j - i, and j - i in [1..n].          *)
(*                                                                          *)
(*  L5/mu ROLE:                                                             *)
(*    mu_le finds the SMALLEST such k via direct mu-search over [1..n].    *)
(*    Pigeonhole is implemented constructively via remove_one + induction. *)
(*    The whole proof is P4-finitized: every search is over [0..n].         *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1): vertices [0..n-1], iterates sigma^k(x).                *)
(*    Roles (L1):    permutation sigma, iteration, cycle.                   *)
(*    Rules (L2):    sigma is bijection on finite set.                      *)
(*    Order (L5):    smallest k >= 1 with sigma^k(x) = x via mu_le.        *)
(*    Process (P4):  bounded iteration; cycle length <= n.                  *)
(*                                                                          *)
(*    P4-DIAGNOSTIC: could it be otherwise under same rules?                *)
(*    NO: pigeonhole forces collision; injectivity forces collision to be   *)
(*    AT zero; so cycle length is well-defined and unique-minimal via L5.   *)
(*                                                                          *)
(*  CONTENT: 0 Admitted, 0 axioms.                                          *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: BOUNDED mu-SEARCH                                   *)
(* ========================================================================= *)

Fixpoint mu_le (P : nat -> bool) (K : nat) : option nat :=
  match K with
  | 0 => if P 0 then Some 0 else None
  | S K' =>
    match mu_le P K' with
    | Some k => Some k
    | None => if P K then Some K else None
    end
  end.

Lemma mu_le_sound : forall P K k,
  mu_le P K = Some k -> P k = true /\ k <= K.
Proof.
  intros P K. induction K as [|K' IH]; intros k H.
  - simpl in H. destruct (P 0) eqn:E; [|discriminate].
    injection H as <-. split; [exact E | lia].
  - simpl in H.
    case_eq (mu_le P K').
    + intros k' Em. rewrite Em in H.
      injection H as Heq. subst k'.
      destruct (IH k Em) as [Hp Hle].
      split; [exact Hp | lia].
    + intros En. rewrite En in H.
      destruct (P (S K')) eqn:E2; [|discriminate].
      injection H as <-. split; [exact E2 | lia].
Qed.

Lemma mu_le_none_all_false : forall P K,
  mu_le P K = None -> forall j, j <= K -> P j = false.
Proof.
  intros P K. induction K as [|K' IH]; intros H j Hj; simpl in H.
  - destruct (P 0) eqn:E; [discriminate|].
    assert (j = 0) by lia. subst. exact E.
  - destruct (mu_le P K') as [k|] eqn:E; [discriminate|].
    destruct (P (S K')) eqn:E2; [discriminate|].
    destruct (Nat.eqb j (S K')) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exact E2.
    + apply Nat.eqb_neq in Heq.
      apply (IH eq_refl). lia.
Qed.

Lemma mu_le_minimal : forall P K k,
  mu_le P K = Some k -> forall j, j < k -> P j = false.
Proof.
  intros P K. induction K as [|K' IH]; intros k H j Hj.
  - simpl in H. destruct (P 0) eqn:E; [|discriminate].
    injection H as <-. lia.
  - simpl in H. case_eq (mu_le P K').
    + intros k' Em. rewrite Em in H.
      injection H as Heq. subst k'.
      apply (IH k Em j Hj).
    + intros En. rewrite En in H.
      destruct (P (S K')) eqn:E2; [|discriminate].
      injection H as Heq.
      rewrite <- Heq in Hj.
      apply (mu_le_none_all_false _ _ En). lia.
Qed.

(* ========================================================================= *)
(*               PART II: REMOVE-ONE AND NODUP MACHINERY                     *)
(* ========================================================================= *)

Fixpoint remove_one (x : nat) (L : list nat) : list nat :=
  match L with
  | [] => []
  | y :: ys => if Nat.eqb x y then ys else y :: remove_one x ys
  end.

Lemma remove_one_in : forall x y L,
  In y (remove_one x L) -> In y L.
Proof.
  intros x y L Hin. induction L as [|z L' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct (Nat.eqb x z) eqn:E.
    + right. exact Hin.
    + destruct Hin as [Hyz|Hin'].
      * subst z. left. reflexivity.
      * right. apply IH. exact Hin'.
Qed.

Lemma remove_one_length_in : forall x L,
  In x L -> length (remove_one x L) = length L - 1.
Proof.
  intros x L Hin. induction L as [|y L' IH].
  - contradiction.
  - simpl. destruct (Nat.eqb x y) eqn:E.
    + simpl. lia.
    + apply Nat.eqb_neq in E.
      destruct Hin as [Hxy|Hin]; [congruence|].
      simpl. rewrite IH; [|exact Hin].
      destruct L' as [|w L'']; [contradiction | simpl; lia].
Qed.

Lemma NoDup_remove_one : forall x L,
  NoDup L -> NoDup (remove_one x L).
Proof.
  intros x L Hnd. induction L as [|y L' IH].
  - simpl. constructor.
  - simpl. destruct (Nat.eqb x y) eqn:E.
    + inversion Hnd; subst. assumption.
    + inversion Hnd; subst. constructor.
      * intros Hin. apply H1. apply remove_one_in in Hin. exact Hin.
      * apply IH. assumption.
Qed.

Lemma remove_one_in_neq : forall x y L,
  NoDup L -> In y (remove_one x L) -> y <> x.
Proof.
  intros x y L Hnd Hin Heq. subst y.
  induction L as [|z L' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct (Nat.eqb x z) eqn:E.
    + apply Nat.eqb_eq in E. subst z.
      inversion Hnd; subst. contradiction.
    + destruct Hin as [Hxz|Hin'].
      * subst z. apply Nat.eqb_neq in E. contradiction.
      * inversion Hnd; subst. apply IH; assumption.
Qed.

(* ========================================================================= *)
(*               PART III: NODUP-BOUNDED-LENGTH (PIGEONHOLE CORE)            *)
(* ========================================================================= *)

(** A NoDup list whose values are all < n has length <= n. *)
Lemma nodup_bounded_length : forall (n : nat) (L : list nat),
  NoDup L -> (forall y, In y L -> y < n) -> length L <= n.
Proof.
  intros n. induction n as [|n' IH]; intros L Hnd Hbnd.
  - destruct L as [|x rest]; [simpl; lia|].
    exfalso. assert (Hin : In x (x :: rest)) by (left; reflexivity).
    apply Hbnd in Hin. lia.
  - destruct (List.in_dec Nat.eq_dec n' L) as [Hin|Hnin].
    + assert (Hrem_nd : NoDup (remove_one n' L)) by (apply NoDup_remove_one; exact Hnd).
      assert (Hrem_bnd : forall y, In y (remove_one n' L) -> y < n').
      { intros y Hy.
        assert (Hy_neq : y <> n') by (apply (remove_one_in_neq n' y L Hnd); exact Hy).
        apply remove_one_in in Hy. apply Hbnd in Hy. lia. }
      pose proof (IH _ Hrem_nd Hrem_bnd) as Hlen.
      rewrite remove_one_length_in in Hlen; [|exact Hin].
      lia.
    + assert (Hbnd' : forall y, In y L -> y < n').
      { intros y Hy.
        assert (Hy_neq : y <> n') by (intros Heq; subst y; contradiction).
        apply Hbnd in Hy. lia. }
      pose proof (IH L Hnd Hbnd') as Hlen. lia.
Qed.

(* ========================================================================= *)
(*               PART IV: PERMUTATIONS AND ITERATES                          *)
(* ========================================================================= *)

(** A function sigma : nat -> nat is a permutation of [0..n-1] if it's
    bounded and injective on that range. (Surjectivity follows from
    injectivity on a finite set; we don't need it as a primitive.) *)
Definition is_perm (sigma : nat -> nat) (n : nat) : Prop :=
  (forall x, x < n -> sigma x < n) /\
  (forall x y, x < n -> y < n -> sigma x = sigma y -> x = y).

(** k-th iterate of sigma applied to x. *)
Fixpoint iter_sigma (sigma : nat -> nat) (k x : nat) : nat :=
  match k with
  | 0 => x
  | S k' => sigma (iter_sigma sigma k' x)
  end.

Lemma iter_bound : forall sigma n k x,
  is_perm sigma n -> x < n -> iter_sigma sigma k x < n.
Proof.
  intros sigma n k x Hperm Hx.
  induction k as [|k' IH]; simpl.
  - exact Hx.
  - destruct Hperm as [Hbnd _]. apply Hbnd. exact IH.
Qed.

Lemma iter_inj : forall sigma n k x y,
  is_perm sigma n -> x < n -> y < n ->
  iter_sigma sigma k x = iter_sigma sigma k y -> x = y.
Proof.
  intros sigma n k x y Hperm Hx Hy.
  induction k as [|k' IH]; simpl; intros Heq.
  - exact Heq.
  - apply IH.
    pose proof (iter_bound sigma n k' x Hperm Hx) as Hk_x.
    pose proof (iter_bound sigma n k' y Hperm Hy) as Hk_y.
    destruct Hperm as [_ Hinj].
    exact (Hinj _ _ Hk_x Hk_y Heq).
Qed.

Lemma iter_compose : forall sigma a b x,
  iter_sigma sigma (a + b) x = iter_sigma sigma a (iter_sigma sigma b x).
Proof.
  intros sigma a b x. induction a as [|a' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART V: ITERATES LIST AND PIGEON                            *)
(* ========================================================================= *)

(** List of iterates: [iter 0 x, iter 1 x, ..., iter n x]. *)
Definition iterates_list (sigma : nat -> nat) (n x : nat) : list nat :=
  map (fun k => iter_sigma sigma k x) (seq 0 (S n)).

Lemma iterates_list_length : forall sigma n x,
  length (iterates_list sigma n x) = S n.
Proof.
  intros. unfold iterates_list. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma iterates_list_bound : forall sigma n x,
  is_perm sigma n -> x < n ->
  forall y, In y (iterates_list sigma n x) -> y < n.
Proof.
  intros sigma n x Hperm Hx y Hy.
  unfold iterates_list in Hy.
  apply in_map_iff in Hy. destruct Hy as [k [Heq Hk_in]].
  subst y. apply iter_bound; assumption.
Qed.

(** PIGEONHOLE on iterates: among n+1 values, all in [0..n-1], collision. *)
Lemma iterates_have_dup : forall sigma n x,
  is_perm sigma n -> x < n ->
  ~ NoDup (iterates_list sigma n x).
Proof.
  intros sigma n x Hperm Hx Hnd.
  pose proof (nodup_bounded_length n (iterates_list sigma n x) Hnd
                                    (iterates_list_bound sigma n x Hperm Hx)) as Hlen.
  rewrite iterates_list_length in Hlen. lia.
Qed.

(* ========================================================================= *)
(*               PART VI: FROM DUPLICATE TO COLLISION INDICES                *)
(* ========================================================================= *)

(** Find smallest j with iter j x repeating an earlier iter i x. *)
Definition first_repeat (sigma : nat -> nat) (n x : nat) : option (nat * nat) :=
  match mu_le (fun j =>
    andb (Nat.ltb 0 j)
         (existsb (fun i => Nat.eqb (iter_sigma sigma i x) (iter_sigma sigma j x))
                  (seq 0 j))) n with
  | None => None
  | Some j =>
    match mu_le (fun i =>
      Nat.eqb (iter_sigma sigma i x) (iter_sigma sigma j x)) (j - 1) with
    | None => None
    | Some i => Some (i, j)
    end
  end.

(** If a NoDup list has positive length and contains a repeat, we get indices. *)
Lemma not_nodup_dup_indices : forall (L : list nat),
  ~ NoDup L ->
  exists i j, i < j /\ j < length L /\ nth i L 0 = nth j L 0.
Proof.
  induction L as [|x L' IH]; intros Hnnd.
  - exfalso. apply Hnnd. constructor.
  - destruct (List.in_dec Nat.eq_dec x L') as [Hin|Hnin].
    + (* x is in L', so (0, j+1) for j where L'[j] = x *)
      assert (Hex : exists j, j < length L' /\ nth j L' 0 = x).
      { clear Hnnd IH. induction L' as [|y L'' IHL].
        - contradiction.
        - simpl in Hin. destruct Hin as [Hyx|Hin].
          + exists 0. simpl. split; [lia | exact Hyx].
          + destruct (IHL Hin) as [j [Hj_lt Hj_eq]].
            exists (S j). simpl. split; [lia | exact Hj_eq]. }
      destruct Hex as [j [Hj_lt Hj_eq]].
      exists 0, (S j). split; [lia|]. split.
      * simpl. lia.
      * simpl. symmetry. exact Hj_eq.
    + (* x not in L'. Then NoDup L' iff NoDup (x :: L'). Since ~ NoDup (x :: L'), get ~ NoDup L'. *)
      assert (Hnnd_L' : ~ NoDup L').
      { intros Hnd_L'. apply Hnnd. constructor; assumption. }
      destruct (IH Hnnd_L') as [i [j [Hij [Hj_len Heq]]]].
      exists (S i), (S j). split; [lia|]. split.
      * simpl. lia.
      * simpl. exact Heq.
Qed.

(** From ~NoDup of iterates_list, extract collision indices i < j <= n. *)
Lemma iterates_collision_indices : forall sigma n x,
  is_perm sigma n -> x < n ->
  exists i j, i < j /\ j <= n /\ iter_sigma sigma i x = iter_sigma sigma j x.
Proof.
  intros sigma n x Hperm Hx.
  pose proof (iterates_have_dup sigma n x Hperm Hx) as Hnnd.
  destruct (not_nodup_dup_indices _ Hnnd) as [i [j [Hij [Hj_len Heq]]]].
  exists i, j. rewrite iterates_list_length in Hj_len.
  split; [exact Hij|]. split; [lia|].
  unfold iterates_list in Heq.
  assert (Hi_lt_Sn : i < S n) by lia.
  assert (Hj_lt_Sn : j < S n) by lia.
  rewrite (nth_indep _ 0 (iter_sigma sigma 0 x)) in Heq;
    [|rewrite length_map, length_seq; lia].
  symmetry in Heq.
  rewrite (nth_indep _ 0 (iter_sigma sigma 0 x)) in Heq;
    [|rewrite length_map, length_seq; lia].
  symmetry in Heq.
  pose proof (map_nth (fun k => iter_sigma sigma k x) (seq 0 (S n)) 0 i) as Hi_nth.
  pose proof (map_nth (fun k => iter_sigma sigma k x) (seq 0 (S n)) 0 j) as Hj_nth.
  rewrite Hi_nth, Hj_nth in Heq.
  rewrite seq_nth in Heq; [|lia].
  rewrite seq_nth in Heq; [|lia].
  simpl in Heq. exact Heq.
Qed.

(* ========================================================================= *)
(*               PART VII: MAIN THEOREM - CYCLE EXISTS                       *)
(* ========================================================================= *)

(** MAIN: every element of a finite permutation is on a cycle of length <= n. *)
Theorem cycle_exists : forall sigma n x,
  is_perm sigma n -> x < n ->
  exists k, 1 <= k /\ k <= n /\ iter_sigma sigma k x = x.
Proof.
  intros sigma n x Hperm Hx.
  destruct (iterates_collision_indices sigma n x Hperm Hx) as [i [j [Hij [Hjn Hiter_eq]]]].
  exists (j - i).
  split; [lia|]. split; [lia|].
  (* iter (j - i) x = x via injectivity of iter at i *)
  assert (Hj_eq : j = i + (j - i)) by lia.
  rewrite Hj_eq in Hiter_eq.
  rewrite iter_compose in Hiter_eq.
  (* Hiter_eq : iter i x = iter i (iter (j-i) x) *)
  symmetry.
  apply (iter_inj sigma n i x (iter_sigma sigma (j - i) x) Hperm Hx).
  - apply iter_bound; assumption.
  - exact Hiter_eq.
Qed.

(* ========================================================================= *)
(*               PART VIII: SMALLEST CYCLE LENGTH (CANONICAL)                *)
(* ========================================================================= *)

(** The cycle length: smallest k >= 1 with iter sigma k x = x. *)
Definition cycle_length (sigma : nat -> nat) (n x : nat) : option nat :=
  mu_le (fun k => andb (Nat.leb 1 k) (Nat.eqb (iter_sigma sigma k x) x)) n.

(** For elements of a permutation, cycle_length always returns Some k. *)
Theorem cycle_length_some : forall sigma n x,
  is_perm sigma n -> x < n ->
  exists k, cycle_length sigma n x = Some k /\ 1 <= k /\ k <= n /\ iter_sigma sigma k x = x.
Proof.
  intros sigma n x Hperm Hx.
  destruct (cycle_exists sigma n x Hperm Hx) as [k0 [Hk0_pos [Hk0_le Hk0_iter]]].
  unfold cycle_length.
  set (P := fun k => andb (Nat.leb 1 k) (Nat.eqb (iter_sigma sigma k x) x)).
  assert (HP_k0 : P k0 = true).
  { unfold P. apply andb_true_iff. split.
    - apply Nat.leb_le. exact Hk0_pos.
    - apply Nat.eqb_eq. exact Hk0_iter. }
  case_eq (mu_le P n).
  - intros k Em.
    pose proof (mu_le_sound P n k Em) as [HP_k Hk_le].
    unfold P in HP_k. apply andb_true_iff in HP_k as [Hk_pos Hk_iter].
    apply Nat.leb_le in Hk_pos. apply Nat.eqb_eq in Hk_iter.
    exists k. split; [reflexivity|]. split; [exact Hk_pos|]. split; [exact Hk_le | exact Hk_iter].
  - intros En.
    exfalso.
    pose proof (mu_le_none_all_false P n En k0 Hk0_le) as Hf.
    rewrite Hf in HP_k0. discriminate.
Qed.

(** Minimality: cycle_length returns the SMALLEST positive cycle length. *)
Theorem cycle_length_minimal : forall sigma n x k,
  cycle_length sigma n x = Some k ->
  forall k', 1 <= k' < k -> iter_sigma sigma k' x <> x.
Proof.
  intros sigma n x k Hcl k' [Hk'_pos Hk'_lt] Hk'_iter.
  unfold cycle_length in Hcl.
  pose proof (mu_le_minimal _ _ _ Hcl k' Hk'_lt) as Hf.
  apply andb_false_iff in Hf. destruct Hf as [Hf|Hf].
  - apply Nat.leb_nle in Hf. lia.
  - apply Nat.eqb_neq in Hf. apply Hf. exact Hk'_iter.
Qed.

(* ========================================================================= *)
(*               PART IX: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  THE L5/mu SCHEMA AT WORK:

  Cycle existence in finite permutations is the canonical L5/mu pattern:
  - The cycle length is the SMALLEST k >= 1 with sigma^k(x) = x.
  - mu_le extracts this DETERMINISTICALLY.
  - Pigeonhole ensures existence (no role-limit hit).
  - All bounded by n (no Axiom of Infinity needed).

  PIGEONHOLE AS CONSTRUCTIVE WITNESS:

  nodup_bounded_length is the constructive heart: NoDup list + values < n
  => length <= n. The proof uses remove_one to recurse on strictly shorter
  lists, which is an L5-style termination argument. Contrapositive:
  length > n with values < n => duplicate exists (forced).

  THE PIGEON IS THE INJECTIVITY-COMPLEMENT:

  Permutation = injection on finite set. Iterating an injection on the
  SAME element gives sigma^0(x), sigma^1(x), ..., sigma^n(x): n+1 values
  in n-element codomain. Forced collision => cycle.

  CYCLE LENGTH IS WELL-DEFINED:

  cycle_length sigma n x returns Some k where k is the smallest positive
  period of x. This is the canonical INVARIANT of x under sigma — a
  characteristic of x's orbit, not a contingent choice.

  CONNECTION TO PROJECT'S CENTRAL THESIS:

  H1 (finitization boundary = constructivity boundary):
    Finite permutations are inside the L5/mu-domain. Every cycle is
    constructively findable. By contrast, infinite-set permutations
    (e.g. on N) may have NO cycle through a given element (e.g. successor
    function), and the cycle-decomposition theorem becomes UNDECIDABLE in
    general.

  WHAT THIS OPENS NEXT:

  - [CycleDecomposition.v]: decompose permutation into disjoint cycles.
  - [PermutationGroup.v]: every permutation is product of transpositions.
  - [PermutationSign.v]: well-defined sign (parity of inversions).
  - [LagrangeFinite.v]: cycle length divides ord(sigma) in symmetric group.
  - [BurnsideFiniteCounting.v]: orbit-counting via fixed points.
*)
