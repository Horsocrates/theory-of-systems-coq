(* ========================================================================= *)
(*                         MOTZKIN NUMBERS                                  *)
(*                                                                          *)
(*  M_n counts lattice paths from (0,0) to (n,0) with steps:                *)
(*    MU = (+1, +1) — up                                                    *)
(*    MD = (+1, -1) — down                                                  *)
(*    MF = (+1,  0) — flat                                                  *)
(*  that never go below y = 0.                                              *)
(*                                                                          *)
(*  RECURRENCE: M_n = M_{n-1} + sum_{k=0}^{n-2} M_k * M_{n-2-k}              *)
(*  CLOSED FORM (in terms of Catalan):                                      *)
(*                                                                          *)
(*    M_n = sum_{k=0}^{floor(n/2)} C(n, 2k) * Cat_k                         *)
(*                                                                          *)
(*  where C(n, 2k) chooses positions for UD-pairs and Cat_k is the Catalan  *)
(*  number for the matching arrangement.                                    *)
(*                                                                          *)
(*  E/R/R interpretation:                                                   *)
(*    Elements (L1):  ternary step {MU, MD, MF} — first non-binary          *)
(*                    distinction in the combinatorial branch.             *)
(*    Roles (L1):     position, height (signed integer), match-pairing     *)
(*    Rules (L2):     non-negativity, closure (sum_U = sum_D),              *)
(*                    determinism, finite length.                          *)
(*                                                                          *)
(*  L5 (Order):  positions are ordered (sequence semantics).               *)
(*  P4 (Finitude): num_motzkin n counts a finite set.                      *)
(*                                                                          *)
(*  CURRENT STATE: ternary infrastructure + numerical examples + closed-   *)
(*  form definition. The full bijection between Motzkin paths and          *)
(*  (UD-position, Catalan-arrangement) pairs parallels rotation_count_     *)
(*  relation in Catalan.v and is identified as future work.                 *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

From ToS Require Import Catalan.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: TERNARY STEP TYPE                                  *)
(* ========================================================================= *)

(** Three-valued step type. *)
Inductive MStep : Set :=
  | MU : MStep   (* up *)
  | MD : MStep   (* down *)
  | MF : MStep.  (* flat *)

(** Path = sequence of ternary steps. *)
Definition MPath : Set := list MStep.

(* ========================================================================= *)
(*               PART II: COUNTS AND HEIGHT                                 *)
(* ========================================================================= *)

Fixpoint Mcount_U (p : MPath) : nat :=
  match p with
  | [] => 0
  | MU :: rest => S (Mcount_U rest)
  | _ :: rest => Mcount_U rest
  end.

Fixpoint Mcount_D (p : MPath) : nat :=
  match p with
  | [] => 0
  | MD :: rest => S (Mcount_D rest)
  | _ :: rest => Mcount_D rest
  end.

Fixpoint Mcount_F (p : MPath) : nat :=
  match p with
  | [] => 0
  | MF :: rest => S (Mcount_F rest)
  | _ :: rest => Mcount_F rest
  end.

(** Counts partition into U+D+F = length. *)
Lemma Mcount_partition : forall p,
  Mcount_U p + Mcount_D p + Mcount_F p = length p.
Proof.
  induction p as [|x rest IH]; simpl; auto.
  destruct x; simpl; lia.
Qed.

(** Signed height after k steps. *)
Definition Mheight_at (p : MPath) (k : nat) : Z :=
  (Z.of_nat (Mcount_U (firstn k p)) - Z.of_nat (Mcount_D (firstn k p)))%Z.

(** Height_at at 0 is 0. *)
Lemma Mheight_at_0 : forall p, Mheight_at p 0 = 0%Z.
Proof. intros p. unfold Mheight_at. cbn [firstn Mcount_U Mcount_D]. lia. Qed.

(* ========================================================================= *)
(*               PART III: MOTZKIN PREDICATE                                *)
(* ========================================================================= *)

(** Motzkin path: non-negative heights everywhere AND ends at 0. *)
Definition is_motzkin (p : MPath) : Prop :=
  Mcount_U p = Mcount_D p /\
  (forall k, k <= length p -> (0 <= Mheight_at p k)%Z).

(* ========================================================================= *)
(*               PART IV: ENUMERATION                                       *)
(* ========================================================================= *)

(** Enumerate all ternary paths of length n. *)
Fixpoint Mall_paths (n : nat) : list MPath :=
  match n with
  | 0 => [[]]
  | S m =>
      let prev := Mall_paths m in
      map (cons MU) prev ++ map (cons MD) prev ++ map (cons MF) prev
  end.

Lemma Mall_paths_length : forall n p, In p (Mall_paths n) -> length p = n.
Proof.
  induction n as [|n IH]; intros p Hin; simpl in Hin.
  - destruct Hin as [Heq|[]]. subst. reflexivity.
  - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + apply in_map_iff in Hin. destruct Hin as [p' [<- Hin']].
      simpl. f_equal. apply IH. exact Hin'.
    + apply in_app_or in Hin. destruct Hin as [Hin|Hin];
        apply in_map_iff in Hin; destruct Hin as [p' [<- Hin']];
        simpl; f_equal; apply IH; exact Hin'.
Qed.

(* ========================================================================= *)
(*               PART V: BOOLEAN MOTZKIN CHECK                              *)
(* ========================================================================= *)

(** Boolean check via height tracking. *)
Fixpoint is_motzkin_b_aux (p : MPath) (h : Z) : bool :=
  match p with
  | [] => Z.eqb h 0%Z
  | MU :: rest => is_motzkin_b_aux rest (h + 1)%Z
  | MD :: rest =>
      if Z.ltb (h - 1) 0%Z then false
      else is_motzkin_b_aux rest (h - 1)%Z
  | MF :: rest => is_motzkin_b_aux rest h
  end.

Definition is_motzkin_b (p : MPath) : bool := is_motzkin_b_aux p 0%Z.

(** Count of Motzkin paths of length n. *)
Definition num_motzkin (n : nat) : nat :=
  length (filter is_motzkin_b (Mall_paths n)).

(* ========================================================================= *)
(*               PART VI: CLOSED FORM (DEFINITION)                          *)
(* ========================================================================= *)

(** Sum from i = 0 to upper (inclusive). *)
Definition msum_to (f : nat -> nat) (upper : nat) : nat :=
  fold_right Nat.add 0 (map f (seq 0 (S upper))).

(** Motzkin closed form: M_n = sum_{k=0}^{floor(n/2)} C(n, 2k) * Cat_k.
    Using the cycle-lemma form (n+1) * num_dyck n = C(2n, n), so
    num_dyck k = C(2k, k) / (k+1). To express Cat_k in nat,
    we use num_dyck k as our verified Catalan value. *)
Definition motzkin_closed (n : nat) : nat :=
  msum_to (fun k => binomial n (2 * k) * num_dyck k) (n / 2).

(* ========================================================================= *)
(*               PART VII: NUMERICAL VERIFICATION                           *)
(* ========================================================================= *)

(** Base cases: M_0 = M_1 = 1, M_2 = 2, M_3 = 4. *)

Example M_0 : num_motzkin 0 = 1.
Proof. reflexivity. Qed.

Example M_1 : num_motzkin 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example M_2 : num_motzkin 2 = 2.
Proof. vm_compute. reflexivity. Qed.

Example M_3 : num_motzkin 3 = 4.
Proof. vm_compute. reflexivity. Qed.

Example M_4 : num_motzkin 4 = 9.
Proof. vm_compute. reflexivity. Qed.

(* Note: this match the Motzkin sequence 1, 1, 2, 4, 9, 21, 51, ... *)

(* ========================================================================= *)
(*               PART VIII: ERR COMMENTARY                                  *)
(* ========================================================================= *)

(**
  WHY MOTZKIN MATTERS HERE:

  Catalan in Catalan.v works on a BINARY alphabet {U, D}. Motzkin
  introduces a THIRD step MF (horizontal). This is the smallest
  non-binary E (Element) set we have encountered.

  L5 (Law of Order): MF as a "neutral" step doesn't affect height,
  so it can be inserted at any non-zero height. The L5-canonical
  arrangement is to FIRST choose where MF steps go (binomial), and
  THEN arrange the remaining UD-steps as a Dyck-like structure
  (Catalan).

  L4 (Sufficient Reason): the closed form
        M_n = sum_{k=0}^{floor(n/2)} C(n, 2k) * C_k
  has a clear combinatorial REASON — each Motzkin path is
  determined by (a) the positions of its UD-steps and (b) the
  Dyck-matching of those UD-steps.

  P4 (Process Finitude): M_n is counted via finite filter over
  Mall_paths (3^n total paths). The sequence {M_n}_{n} is a
  process, no completed infinity.

  CONNECTION TO CATALAN AS A FACTOR:
  M_n includes Cat_k (= num_dyck k in our verified setup) as a
  factor in each term. This makes the entire Catalan formalization
  REUSABLE in the Motzkin closed form.

  FUTURE WORK: prove
        num_motzkin n = motzkin_closed n
  via a bijection between Motzkin paths of length n and pairs
  (S ⊆ [n] of even size 2k, Dyck path of length 2k). Each such pair
  encodes a unique Motzkin path: place UDs at positions in S
  according to the Dyck arrangement, MFs everywhere else.
*)

(* ========================================================================= *)
(*    PART IX: num_motzkin = motzkin_closed  via the F-extraction count       *)
(*                                                                          *)
(*  A ternary path is Motzkin  <=>  its U/D-subsequence (drop F) is a Dyck   *)
(*  path (F leaves the height unchanged).  The number of ternary paths of    *)
(*  length n whose extraction is a FIXED binary b is C(n,|b|) (choose the    *)
(*  non-F positions); summing over Dyck b regroups to                        *)
(*       num_motzkin n = sum_{j=0}^n C(n,j) * #{Dyck of length j}            *)
(*                     = sum_{k=0}^{n/2} C(n,2k) * Cat_k = motzkin_closed n. *)
(* ========================================================================= *)

(** Extract the U/D subsequence as a binary (Catalan) Path. *)
Fixpoint Mextract (p : MPath) : Path :=
  match p with
  | [] => []
  | MU :: r => true  :: Mextract r
  | MD :: r => false :: Mextract r
  | MF :: r => Mextract r
  end.

(** F leaves the Z-height tracker unchanged, so the boolean Motzkin test on p
    equals the boolean Dyck test on its extraction. *)
Lemma is_motzkin_b_aux_extract : forall p h,
  is_motzkin_b_aux p h = is_dyck_b_aux (Mextract p) h.
Proof.
  induction p as [|s r IH]; intro h.
  - reflexivity.
  - destruct s; simpl; rewrite IH; reflexivity.
Qed.

Lemma is_motzkin_b_extract : forall p, is_motzkin_b p = is_dyck_b (Mextract p).
Proof. intro p. unfold is_motzkin_b, is_dyck_b. apply is_motzkin_b_aux_extract. Qed.

(** Counting handles: NP P j = #binary paths of length j satisfying P;
    count_ext P n = #ternary paths of length n whose extraction satisfies P. *)
Definition NP (P : Path -> bool) (j : nat) : nat := length (filter P (all_paths j)).
Definition count_ext (P : Path -> bool) (n : nat) : nat :=
  length (filter (fun p => P (Mextract p)) (Mall_paths n)).

Lemma num_motzkin_count_ext : forall n, num_motzkin n = count_ext is_dyck_b n.
Proof.
  intro n. unfold num_motzkin, count_ext. f_equal.
  apply filter_ext_in. intros p _. apply is_motzkin_b_extract.
Qed.

(** filter over [map (cons s) l] for ternary steps. *)
Lemma Mfilter_map_cons_length :
  forall (s : MStep) (l : list MPath) (pred : MPath -> bool),
  length (filter pred (map (cons s) l)) = length (filter (fun p => pred (s :: p)) l).
Proof.
  induction l as [|p l IH]; intros pred; simpl; auto.
  destruct (pred (s :: p)); simpl; rewrite IH; reflexivity.
Qed.

(** Binary all_paths splits by the first bit. *)
Lemma NP_S : forall P j,
  NP P (S j) = NP (fun b => P (true :: b)) j + NP (fun b => P (false :: b)) j.
Proof.
  intros P j. unfold NP. simpl all_paths.
  rewrite filter_app, length_app, !filter_map_cons_length. reflexivity.
Qed.

(** Ternary Mall_paths recurrence for count_ext (MU/MD prepend a bit; MF drops). *)
Lemma count_ext_S : forall P m,
  count_ext P (S m)
  = count_ext (fun b => P (true :: b)) m
  + count_ext (fun b => P (false :: b)) m
  + count_ext P m.
Proof.
  intros P m. unfold count_ext.
  change (Mall_paths (S m)) with
    (map (cons MU) (Mall_paths m)
       ++ map (cons MD) (Mall_paths m)
       ++ map (cons MF) (Mall_paths m)).
  rewrite !filter_app, !length_app, !Mfilter_map_cons_length.
  rewrite Nat.add_assoc. reflexivity.
Qed.

(** Binomial transform as a Fixpoint with the Pascal recurrence built in:
    binsum2 g n = sum_{j=0}^n C(n,j) * g j  (matched to the fold form later). *)
Fixpoint binsum2 (g : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => g 0
  | S m => binsum2 g m + binsum2 (fun j => g (S j)) m
  end.

Lemma binsum2_ext : forall n g1 g2,
  (forall j, g1 j = g2 j) -> binsum2 g1 n = binsum2 g2 n.
Proof.
  induction n as [|n IH]; intros g1 g2 H; simpl.
  - apply H.
  - rewrite (IH g1 g2 H).
    rewrite (IH (fun j => g1 (S j)) (fun j => g2 (S j)) (fun j => H (S j))).
    reflexivity.
Qed.

Lemma binsum2_add : forall n g1 g2,
  binsum2 (fun j => g1 j + g2 j) n = binsum2 g1 n + binsum2 g2 n.
Proof.
  induction n as [|n IH]; intros g1 g2; simpl.
  - reflexivity.
  - rewrite (IH g1 g2).
    rewrite (IH (fun j => g1 (S j)) (fun j => g2 (S j))).
    lia.
Qed.

(** ★ MAIN COUNT: ternary paths whose extraction satisfies P, counted by the
    binomial transform of the binary count NP P. *)
Lemma count_ext_binsum2 : forall n P, count_ext P n = binsum2 (NP P) n.
Proof.
  induction n as [|n IH]; intro P.
  - unfold count_ext, NP. simpl. destruct (P []); reflexivity.
  - rewrite count_ext_S.
    rewrite (IH (fun b => P (true :: b))).
    rewrite (IH (fun b => P (false :: b))).
    rewrite (IH P).
    simpl binsum2.
    rewrite (binsum2_ext n (fun j => NP P (S j))
               (fun j => NP (fun b => P (true :: b)) j
                       + NP (fun b => P (false :: b)) j)
               (NP_S P)).
    rewrite binsum2_add. lia.
Qed.

(** num_motzkin as the binomial transform of the Dyck count. *)
Corollary num_motzkin_binsum2 : forall n, num_motzkin n = binsum2 (NP is_dyck_b) n.
Proof. intro n. rewrite num_motzkin_count_ext. apply count_ext_binsum2. Qed.

(* ----- explicit fold form: binsum2 g n = sum_{j=0}^n C(n,j) * g j ----- *)

Fixpoint gsum (f : nat -> nat) (l : list nat) : nat :=
  match l with [] => 0 | x :: r => f x + gsum f r end.

Lemma gsum_app : forall f l1 l2, gsum f (l1 ++ l2) = gsum f l1 + gsum f l2.
Proof. intros f l1 l2. induction l1 as [|x l1 IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma gsum_add : forall f1 f2 l, gsum (fun i => f1 i + f2 i) l = gsum f1 l + gsum f2 l.
Proof. intros f1 f2 l. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma gsum_ext : forall f1 f2 l, (forall i, f1 i = f2 i) -> gsum f1 l = gsum f2 l.
Proof. intros f1 f2 l H. induction l as [|x l IH]; simpl; [reflexivity | rewrite H, IH; reflexivity]. Qed.

Lemma gsum_map_S : forall f l, gsum f (map S l) = gsum (fun i => f (S i)) l.
Proof. intros f l. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma seq_cons0 : forall n, seq 0 (S n) = 0 :: map S (seq 0 n).
Proof. intro n. cbn [seq]. f_equal. symmetry. apply seq_shift. Qed.

Definition fold_sum (g : nat -> nat) (n : nat) : nat :=
  gsum (fun j => binomial n j * g j) (seq 0 (S n)).

(** Peel the j=0 term: fold_sum g n = g 0 + sum_{i=0}^{n-1} C(n,S i) g(S i). *)
Lemma fold_sum_head : forall n g,
  fold_sum g n = g 0 + gsum (fun i => binomial n (S i) * g (S i)) (seq 0 n).
Proof.
  intros n g. unfold fold_sum. rewrite seq_cons0. simpl gsum.
  rewrite gsum_map_S, binomial_n_0. lia.
Qed.

(** Drop a vanishing top term of a gsum over seq. *)
Lemma gsum_seq_top_zero : forall f m,
  f m = 0 -> gsum f (seq 0 (S m)) = gsum f (seq 0 m).
Proof.
  intros f m Hf. rewrite seq_S. rewrite gsum_app. simpl. rewrite Hf. lia.
Qed.

(** ★ Pascal recurrence for the binomial-weighted sum. *)
Lemma fold_sum_S : forall g m,
  fold_sum g (S m) = fold_sum g m + fold_sum (fun j => g (S j)) m.
Proof.
  intros g m.
  rewrite (fold_sum_head (S m) g).
  rewrite (gsum_ext (fun i => binomial (S m) (S i) * g (S i))
                    (fun i => binomial m i * g (S i) + binomial m (S i) * g (S i))
                    (seq 0 (S m))).
  2:{ intro i. rewrite binomial_S_S_eq. nia. }
  rewrite gsum_add.
  assert (HT1 : gsum (fun i => binomial m i * g (S i)) (seq 0 (S m))
              = fold_sum (fun j => g (S j)) m).
  { unfold fold_sum. apply gsum_ext. intro i. reflexivity. }
  rewrite HT1.
  rewrite (gsum_seq_top_zero (fun i => binomial m (S i) * g (S i)) m).
  2:{ cbn beta. rewrite binomial_lt by lia. lia. }
  rewrite (fold_sum_head m g). lia.
Qed.

Lemma binsum2_fold : forall n g, binsum2 g n = fold_sum g n.
Proof.
  induction n as [|n IH]; intro g.
  - unfold fold_sum. simpl. lia.
  - simpl binsum2. rewrite (IH g), (IH (fun j => g (S j))).
    rewrite <- fold_sum_S. reflexivity.
Qed.

(** NP of is_dyck_b at an even index is exactly the Catalan count. *)
Lemma NP_dyck_even : forall k, NP is_dyck_b (2 * k) = num_dyck k.
Proof. intro k. unfold NP, num_dyck. reflexivity. Qed.

Lemma gsum_fold_right : forall f l, gsum f l = fold_right Nat.add 0 (map f l).
Proof. intros f l. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* ----- a true Dyck word is balanced, hence has even length ----- *)

From Stdlib Require Import Arith.Wf_nat.

Lemma is_dyck_b_aux_balance : forall p h,
  is_dyck_b_aux p h = true ->
  (h + Z.of_nat (count_U p) - Z.of_nat (count_D p))%Z = 0%Z.
Proof.
  induction p as [|s p IH]; intros h H.
  - simpl in H. apply Z.eqb_eq in H. simpl. lia.
  - destruct s.
    + simpl in H. apply IH in H. cbn [count_U count_D]. lia.
    + simpl in H. destruct (Z.ltb (h - 1) 0) eqn:E; [discriminate|].
      apply IH in H. cbn [count_U count_D]. lia.
Qed.

Lemma is_dyck_b_balanced : forall p, is_dyck_b p = true -> count_U p = count_D p.
Proof.
  intros p H. unfold is_dyck_b in H. apply is_dyck_b_aux_balance in H.
  apply Nat2Z.inj. lia.
Qed.

Lemma length_filter_all_false : forall (A:Type) (f:A->bool) (l:list A),
  (forall x, In x l -> f x = false) -> length (filter f l) = 0.
Proof.
  intros A f l H. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite H by (left; reflexivity).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma NP_dyck_odd : forall k, NP is_dyck_b (S (2 * k)) = 0.
Proof.
  intro k. unfold NP. apply length_filter_all_false.
  intros p Hp. pose proof (all_paths_length _ _ Hp) as Hlen.
  destruct (is_dyck_b p) eqn:E; [|reflexivity].
  apply is_dyck_b_balanced in E.
  pose proof (count_UD_length p) as HUD. rewrite Hlen, E in HUD. lia.
Qed.

(* ----- collapse the odd-vanishing binomial sum onto even indices ----- *)

Lemma gsum_double_peel : forall F m,
  gsum F (seq 0 (S (S m))) = F 0 + F 1 + gsum (fun i => F (S (S i))) (seq 0 m).
Proof.
  intros F m.
  rewrite seq_cons0. cbn [gsum]. rewrite gsum_map_S.
  rewrite seq_cons0. cbn [gsum]. rewrite gsum_map_S.
  cbn beta. lia.
Qed.

Lemma even_collapse : forall n F,
  (forall k, F (S (2 * k)) = 0) ->
  gsum F (seq 0 (S n)) = gsum (fun k => F (2 * k)) (seq 0 (S (n / 2))).
Proof.
  intro n. induction n as [n IH] using (well_founded_ind lt_wf). intros F Hodd.
  destruct n as [|[|n']].
  - replace (0 / 2) with 0 by reflexivity. simpl. lia.
  - replace (1 / 2) with 0 by reflexivity. simpl.
    pose proof (Hodd 0) as H1. simpl in H1. rewrite H1. lia.
  - pose proof (Hodd 0) as H1. simpl in H1.
    rewrite gsum_double_peel. rewrite H1.
    assert (HG : forall k, (fun i => F (S (S i))) (S (2 * k)) = 0).
    { intro k. cbn beta. replace (S (S (S (2 * k)))) with (S (2 * S k)) by lia. apply Hodd. }
    rewrite (IH n' ltac:(lia) (fun i => F (S (S i))) HG).
    assert (Hdiv : S (S n') / 2 = S (n' / 2)).
    { replace (S (S n')) with (n' + 1 * 2) by lia. rewrite Nat.div_add by lia. lia. }
    rewrite Hdiv. rewrite (seq_cons0 (S (n' / 2))). cbn [gsum]. rewrite gsum_map_S. cbn beta.
    rewrite (gsum_ext (fun k => F (S (S (2 * k)))) (fun k => F (2 * S k))
              (seq 0 (S (n' / 2)))).
    2:{ intro k. f_equal. lia. }
    replace (2 * 0) with 0 by reflexivity. lia.
Qed.

(* ========================================================================= *)
(*               ★★★ MAIN THEOREM: num_motzkin = motzkin_closed              *)
(* ========================================================================= *)

Theorem num_motzkin_closed : forall n, num_motzkin n = motzkin_closed n.
Proof.
  intro n.
  rewrite num_motzkin_binsum2, binsum2_fold. unfold fold_sum.
  rewrite (even_collapse n (fun j => binomial n j * NP is_dyck_b j)).
  2:{ intro k. cbn beta. rewrite NP_dyck_odd. lia. }
  unfold motzkin_closed, msum_to. rewrite <- gsum_fold_right.
  apply gsum_ext. intro k. cbn beta. rewrite NP_dyck_even. reflexivity.
Qed.

Print Assumptions num_motzkin_closed.
