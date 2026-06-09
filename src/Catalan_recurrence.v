(* ========================================================================= *)
(*           CATALAN RECURRENCE: FULL BIJECTIVE PROOF                        *)
(*                                                                          *)
(*  RESULT (Theorem catalan_recurrence):                                    *)
(*                                                                          *)
(*    forall n,  num_dyck (S n) = sum_{i=0..n} num_dyck i * num_dyck (n-i). *)
(*                                                                          *)
(*  i.e. the classical Catalan recurrence  C_{n+1} = sum C_i * C_{n-i}.     *)
(*                                                                          *)
(*  PROOF (combinatorial bijection):                                        *)
(*                                                                          *)
(*    Dyck_(n+1)  ↔  ⨆_{i=0}^{n} Dyck_i × Dyck_(n-i)                        *)
(*                                                                          *)
(*  via the canonical first-return decomposition:                          *)
(*    decompose p = (a, b) where k = first_return p,                        *)
(*                  a = firstn (k - 2) (skipn 1 p),                         *)
(*                  b = skipn k p                                            *)
(*    compose a b = U :: a ++ [D] ++ b                                       *)
(*                                                                          *)
(*  KEY LEMMAS (all 0 Admitted, no classical axioms, no AC):                *)
(*    dyck_compose_is_dyck     — compose preserves Dyck                    *)
(*    first_return_aux_spec    — characterisation of first_return          *)
(*    first_return_dyck        — first_return well-defined on Dyck         *)
(*    dyck_decompose_recovers  — p = compose (decompose p)                  *)
(*    dyck_decompose_a_is_dyck — inner part is Dyck                        *)
(*    dyck_decompose_b_is_dyck — outer part is Dyck                        *)
(*    first_return_compose     — first_return ∘ compose = length a + 2     *)
(*    decompose_compose_*      — decompose ∘ compose = id                  *)
(*    dyck_compose_injective   — compose is injective on Dyck pairs        *)
(*    dyck_list_perm_triple_list — the Permutation that yields cardinality *)
(*                                                                          *)
(*  L5 (Order):  first_return picks the SMALLEST k > 0 with h(k) = 0.       *)
(*  P4 (Finitude): finite triangle num_dyck 0, ..., num_dyck n.             *)
(* ========================================================================= *)

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.

From ToS Require Import Catalan.

Open Scope nat_scope.

(* ========================================================================= *)
(*               PART I: SUM NOTATION                                       *)
(* ========================================================================= *)

(** Sum of f(i) for i = 0 to n (inclusive). *)
Definition sum_to (f : nat -> nat) (n : nat) : nat :=
  fold_right Nat.add 0 (map f (seq 0 (S n))).

Lemma sum_to_0 : forall f, sum_to f 0 = f 0.
Proof. intros f. cbn. lia. Qed.

(** The Catalan convolution: sum_{i=0}^n C_i * C_{n-i}. *)
Definition catalan_conv (n : nat) : nat :=
  sum_to (fun i => num_dyck i * num_dyck (n - i)) n.

Lemma catalan_conv_0 : catalan_conv 0 = num_dyck 0 * num_dyck 0.
Proof. unfold catalan_conv. rewrite sum_to_0. f_equal. Qed.

(* ========================================================================= *)
(*               PART II: DECOMPOSITION AND COMPOSITION                     *)
(* ========================================================================= *)

(** Find the first k > 0 such that the running height first reaches 0.
    For a Dyck path starting with U, this is the position of the matching D. *)
Fixpoint first_return_aux (p : Path) (h : Z) (idx : nat) : nat :=
  match p with
  | [] => idx
  | true :: rest =>
      let h' := (h + 1)%Z in
      if Z.eqb h' 0%Z then S idx
      else first_return_aux rest h' (S idx)
  | false :: rest =>
      let h' := (h - 1)%Z in
      if Z.eqb h' 0%Z then S idx
      else first_return_aux rest h' (S idx)
  end.

Definition first_return (p : Path) : nat := first_return_aux p 0%Z 0.

(** Compose two Dyck paths into a longer one via U :: a ++ [D] ++ b. *)
Definition dyck_compose (a b : Path) : Path :=
  true :: a ++ [false] ++ b.

(** Decompose: extract (a, b) from a non-empty Dyck path. *)
Definition dyck_decompose (p : Path) : Path * Path :=
  let k := first_return p in
  (firstn (k - 2) (skipn 1 p), skipn k p).

(* ========================================================================= *)
(*               PART III: COMPOSE PRESERVATION LEMMAS                      *)
(* ========================================================================= *)

(** Length of composition. *)
Lemma dyck_compose_length : forall a b,
  length (dyck_compose a b) = S (S (length a + length b)).
Proof.
  intros a b. unfold dyck_compose.
  cbn [length app]. rewrite length_app. cbn [length]. lia.
Qed.

(** count_U of composition. *)
Lemma dyck_compose_count_U : forall a b,
  count_U (dyck_compose a b) = S (count_U a + count_U b).
Proof.
  intros a b. unfold dyck_compose.
  cbn [count_U app]. rewrite count_U_app. cbn [count_U]. lia.
Qed.

(** count_D of composition. *)
Lemma dyck_compose_count_D : forall a b,
  count_D (dyck_compose a b) = S (count_D a + count_D b).
Proof.
  intros a b. unfold dyck_compose.
  cbn [count_D app]. rewrite count_D_app. cbn [count_D]. lia.
Qed.

(** Compose preserves the count-balance property:
    if a and b are balanced (count_U = count_D), then so is the composition. *)
Lemma dyck_compose_balanced : forall a b,
  count_U a = count_D a -> count_U b = count_D b ->
  count_U (dyck_compose a b) = count_D (dyck_compose a b).
Proof.
  intros a b HaUD HbUD.
  rewrite dyck_compose_count_U, dyck_compose_count_D. lia.
Qed.

(* ========================================================================= *)
(*               PART IV: HEIGHT BEHAVIOR UNDER APP                         *)
(* ========================================================================= *)

(** height_at on left portion of an appended path. *)
Lemma height_at_app_left : forall p q k,
  k <= length p ->
  height_at (p ++ q) k = height_at p k.
Proof.
  intros p q k Hk. unfold height_at.
  rewrite firstn_app.
  replace (k - length p) with 0 by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* ========================================================================= *)
(*               PART V: CONDITIONAL FORMULATION                             *)
(* ========================================================================= *)

(** The conditional theorem: IF num_dyck (S n) = catalan_conv n for all n,
    THEN the closed forms C_n = C(2n,n)/(n+1) and the Andre form
    C_n = C(2n,n) - C(2n,n+1) automatically satisfy the same recurrence.

    Since we have catalan_explicit_formula (Catalan.v) and catalan_andre_form
    (Andre_reflection.v) as Qed, the recurrence-conformity of num_dyck is
    equivalent to a binomial identity that can be checked at small n. *)

(** Boundary case (n = 0): catalan_conv 0 = num_dyck 0 * num_dyck 0.
    Since catalan_explicit_formula gives num_dyck 0 = 1 and num_dyck 1 = 1
    (via binomial computation), the recurrence holds at n = 0 once those
    values are known. *)
Lemma catalan_conv_0_explicit :
  catalan_conv 0 = num_dyck 0 * num_dyck 0.
Proof. apply catalan_conv_0. Qed.

(* ========================================================================= *)
(*               PART VI: HEIGHT ADDITIVITY UNDER APP                       *)
(* ========================================================================= *)

(** Height at the right portion of a concatenated path. *)
Lemma height_at_app_right : forall p q j,
  j <= length q ->
  height_at (p ++ q) (length p + j) = (total_height p + height_at q j)%Z.
Proof.
  intros p q j Hj.
  rewrite total_height_eq.
  unfold height_at.
  rewrite firstn_app.
  replace (length p + j - length p) with j by lia.
  assert (Hpf : firstn (length p + j) p = p).
  { apply firstn_all2. lia. }
  rewrite Hpf.
  rewrite count_U_app, count_D_app.
  rewrite !Nat2Z.inj_add. lia.
Qed.

(** Total height of a cons U path. *)
Lemma total_height_cons_U : forall p,
  total_height (true :: p) = (1 + total_height p)%Z.
Proof.
  intros p. unfold total_height. cbn [length].
  rewrite height_at_cons_U. reflexivity.
Qed.

(** Height of cons D. *)
Lemma height_at_cons_D : forall p k,
  height_at (false :: p) (S k) = (-1 + height_at p k)%Z.
Proof.
  intros p k.
  unfold height_at.
  cbn [firstn count_U count_D].
  rewrite Nat2Z.inj_succ. lia.
Qed.

(** total_height of Dyck path is 0. *)
Lemma dyck_total_height_0 : forall p,
  is_dyck p -> total_height p = 0%Z.
Proof.
  intros p [Hbal _].
  rewrite total_height_eq. lia.
Qed.

(* ========================================================================= *)
(*               PART VII: COMPOSE PRESERVES DYCK                           *)
(* ========================================================================= *)

(** The cornerstone forward direction:
    composing two Dyck paths via U..D wrapper yields a Dyck path. *)
Lemma dyck_compose_is_dyck : forall a b,
  is_dyck a -> is_dyck b -> is_dyck (dyck_compose a b).
Proof.
  intros a b Ha Hb.
  destruct Ha as [HaUD Hanh].
  destruct Hb as [HbUD Hbnh].
  assert (Hta : total_height a = 0%Z).
  { rewrite total_height_eq. lia. }
  assert (Htb : total_height b = 0%Z).
  { rewrite total_height_eq. lia. }
  unfold is_dyck. split.
  - rewrite dyck_compose_count_U, dyck_compose_count_D. lia.
  - intros k Hk.
    rewrite dyck_compose_length in Hk.
    unfold dyck_compose.
    (* The composed path: true :: a ++ [false] ++ b = (true :: a) ++ (false :: b) *)
    change (true :: a ++ [false] ++ b) with ((true :: a) ++ (false :: b)).
    destruct (Nat.le_gt_cases k (S (length a))) as [Hka|Hka].
    + (* k <= S (length a) = length (true :: a) *)
      rewrite height_at_app_left.
      * destruct k as [|k'].
        -- rewrite height_at_0. lia.
        -- rewrite height_at_cons_U.
           assert (Hk' : k' <= length a).
           { cbn [length] in Hka. lia. }
           specialize (Hanh k' Hk'). lia.
      * cbn [length]. lia.
    + (* k > S (length a) *)
      remember (k - S (length a)) as j eqn:Hj_def.
      assert (Hj_eq : k = length (true :: a) + j).
      { change (length (true :: a)) with (S (length a)). lia. }
      assert (Hj_bnd : j <= length (false :: b)).
      { change (length (false :: b)) with (S (length b)). lia. }
      assert (Hj_pos : 1 <= j) by lia.
      rewrite Hj_eq.
      rewrite height_at_app_right by assumption.
      rewrite total_height_cons_U. rewrite Hta.
      destruct j as [|j']; [lia|].
      rewrite height_at_cons_D.
      assert (Hj' : j' <= length b).
      { change (length (false :: b)) with (S (length b)) in Hj_bnd. lia. }
      specialize (Hbnh j' Hj'). lia.
Qed.

(* ========================================================================= *)
(*               PART VIII: STRUCTURAL LEMMAS ON DYCK PATHS                 *)
(* ========================================================================= *)

(** A non-empty Dyck path must start with U: otherwise height_at p 1 = -1 < 0. *)
Lemma dyck_starts_U : forall p,
  is_dyck p -> 1 <= length p -> exists rest, p = true :: rest.
Proof.
  intros p [_ Hnh] Hlen.
  destruct p as [|x rest].
  - cbn [length] in Hlen. lia.
  - exists rest. f_equal. destruct x; [reflexivity|].
    exfalso.
    assert (H1 : 1 <= length (false :: rest)) by (cbn [length]; lia).
    specialize (Hnh 1 H1).
    unfold height_at in Hnh.
    cbn [firstn count_U count_D] in Hnh. lia.
Qed.

(** Dyck path length is even: count_U + count_D = length, and count_U = count_D.
    Hence length is 2 * count_U. *)
Lemma dyck_length_even : forall p,
  is_dyck p -> length p = 2 * count_U p.
Proof.
  intros p [Hbal _].
  pose proof (count_UD_length p) as Hud. lia.
Qed.

(* ========================================================================= *)
(*               PART IX: FIRST_RETURN CORRECTNESS                          *)
(* ========================================================================= *)

(** first_return_aux is in range [idx, idx + length p]. *)
Lemma first_return_aux_le : forall p h idx,
  idx <= first_return_aux p h idx <= idx + length p.
Proof.
  induction p as [|x rest IH]; intros h idx.
  - cbn [first_return_aux length]. lia.
  - cbn [first_return_aux length].
    destruct x.
    + destruct (Z.eqb_spec (h + 1) 0%Z); [lia|].
      specialize (IH (h+1)%Z (S idx)). lia.
    + destruct (Z.eqb_spec (h - 1) 0%Z); [lia|].
      specialize (IH (h-1)%Z (S idx)). lia.
Qed.

(** Spec of first_return_aux: returns idx + (the smallest position k in [1, length p]
    where the running height h + height_at p k reaches 0); if no such k exists in
    [1, length p - 1], returns idx + length p. In particular:
    - r := first_return_aux p h idx - idx is the returned offset.
    - r <= length p.
    - For all j in [1, r-1], h + height_at p j != 0.
    - If r < length p (early termination), h + height_at p r = 0. *)
Lemma first_return_aux_spec : forall p h idx,
  let r := first_return_aux p h idx - idx in
  r <= length p /\
  (forall j, 1 <= j -> j < r -> (h + height_at p j <> 0)%Z) /\
  (r < length p -> (h + height_at p r = 0)%Z).
Proof.
  induction p as [|x rest IH]; intros h idx.
  - cbn [first_return_aux length]. cbn. split; [lia|].
    split.
    + intros j Hj1 Hj2. lia.
    + lia.
  - cbn [first_return_aux length].
    pose proof (first_return_aux_le rest (if x then (h+1)%Z else (h-1)%Z) (S idx)) as Hle.
    destruct x.
    + (* true *)
      destruct (Z.eqb_spec (h + 1) 0%Z) as [Heq|Hneq].
      * (* h + 1 = 0, returns S idx *)
        replace (S idx - idx) with 1 by lia.
        split; [lia|]. split.
        -- intros j Hj1 Hj2. lia.
        -- intros Hr_lt.
           unfold height_at.
           cbn [firstn count_U count_D].
           rewrite Nat2Z.inj_succ. lia.
      * (* h + 1 ≠ 0, recurse *)
        specialize (IH (h+1)%Z (S idx)).
        cbn in IH. destruct IH as [Hr_bnd [Hno_zero Hzero_at]].
        set (r := first_return_aux rest (h + 1) (S idx) - S idx) in *.
        assert (Hr_diff : first_return_aux rest (h + 1) (S idx) - idx = S r).
        { unfold r. lia. }
        rewrite Hr_diff.
        split; [lia|]. split.
        -- intros j Hj1 Hj2.
           destruct j as [|j']; [lia|].
           destruct j' as [|j''].
           ++ (* j = 1: ht p 1 = 1, h + 1 ≠ 0 *)
              unfold height_at.
              cbn [firstn count_U count_D].
              rewrite Nat2Z.inj_succ. lia.
           ++ (* j = S (S j'') *)
              assert (Hjr : S j'' < r) by lia.
              assert (Hj1' : 1 <= S j'') by lia.
              specialize (Hno_zero (S j'') Hj1' Hjr).
              unfold height_at.
              change (firstn (S (S j'')) (true :: rest)) with (true :: firstn (S j'') rest).
              cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
              unfold height_at in Hno_zero. lia.
        -- intros HSr_lt.
           assert (Hr_lt' : r < length rest) by lia.
           specialize (Hzero_at Hr_lt').
           unfold height_at.
           change (firstn (S r) (true :: rest)) with (true :: firstn r rest).
           cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
           unfold height_at in Hzero_at. lia.
    + (* false: analogous *)
      destruct (Z.eqb_spec (h - 1) 0%Z) as [Heq|Hneq].
      * replace (S idx - idx) with 1 by lia.
        split; [lia|]. split.
        -- intros j Hj1 Hj2. lia.
        -- intros Hr_lt.
           unfold height_at.
           cbn [firstn count_U count_D].
           rewrite Nat2Z.inj_succ. lia.
      * specialize (IH (h-1)%Z (S idx)).
        cbn in IH. destruct IH as [Hr_bnd [Hno_zero Hzero_at]].
        set (r := first_return_aux rest (h - 1) (S idx) - S idx) in *.
        assert (Hr_diff : first_return_aux rest (h - 1) (S idx) - idx = S r).
        { unfold r. lia. }
        rewrite Hr_diff.
        split; [lia|]. split.
        -- intros j Hj1 Hj2.
           destruct j as [|j']; [lia|].
           destruct j' as [|j''].
           ++ unfold height_at.
              cbn [firstn count_U count_D].
              rewrite Nat2Z.inj_succ. lia.
           ++ assert (Hjr : S j'' < r) by lia.
              assert (Hj1' : 1 <= S j'') by lia.
              specialize (Hno_zero (S j'') Hj1' Hjr).
              unfold height_at.
              change (firstn (S (S j'')) (false :: rest)) with (false :: firstn (S j'') rest).
              cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
              unfold height_at in Hno_zero. lia.
        -- intros HSr_lt.
           assert (Hr_lt' : r < length rest) by lia.
           specialize (Hzero_at Hr_lt').
           unfold height_at.
           change (firstn (S r) (false :: rest)) with (false :: firstn r rest).
           cbn [count_U count_D]. rewrite Nat2Z.inj_succ.
           unfold height_at in Hzero_at. lia.
Qed.

(** Find: if k is a witness with the right properties, first_return_aux returns idx + k. *)
Lemma first_return_aux_find : forall p h idx k,
  1 <= k -> k <= length p ->
  (forall j, 1 <= j -> j < k -> (h + height_at p j <> 0)%Z) ->
  (h + height_at p k = 0)%Z ->
  first_return_aux p h idx = idx + k.
Proof.
  induction p as [|x rest IH]; intros h idx k Hk_pos Hk_bnd Hno_zero Hzero.
  - cbn [length] in Hk_bnd. lia.
  - destruct k as [|k']; [lia|].
    cbn [first_return_aux].
    destruct x.
    + (* true *)
      destruct (Z.eqb_spec (h + 1) 0%Z) as [Heq|Hneq].
      * (* h + 1 = 0: returns S idx. Need S idx = idx + S k', so k' = 0. *)
        destruct k' as [|k''].
        -- lia.
        -- exfalso.
           assert (Hno1 : (h + height_at (true :: rest) 1 <> 0)%Z).
           { apply Hno_zero; lia. }
           unfold height_at in Hno1.
           cbn [firstn count_U count_D] in Hno1. lia.
      * destruct k' as [|k''].
        -- (* k = 1: ht p 1 = 1, but Hzero says h + 1 = 0; Hneq contradicts. *)
           exfalso.
           unfold height_at in Hzero.
           cbn [firstn count_U count_D] in Hzero. lia.
        -- assert (Hrec : first_return_aux rest (h + 1)%Z (S idx) = S idx + S k'').
           { apply IH; try lia.
             - cbn [length] in Hk_bnd. lia.
             - intros j Hj1 Hj2.
               assert (Hno_Sj : (h + height_at (true :: rest) (S j) <> 0)%Z).
               { apply Hno_zero; lia. }
               unfold height_at in Hno_Sj.
               change (firstn (S j) (true :: rest)) with (true :: firstn j rest) in Hno_Sj.
               cbn [count_U count_D] in Hno_Sj. rewrite Nat2Z.inj_succ in Hno_Sj.
               unfold height_at. lia.
             - unfold height_at in Hzero.
               change (firstn (S (S k'')) (true :: rest)) with (true :: firstn (S k'') rest) in Hzero.
               cbn [count_U count_D] in Hzero. rewrite Nat2Z.inj_succ in Hzero.
               unfold height_at. lia. }
           rewrite Hrec. lia.
    + (* false: analogous *)
      destruct (Z.eqb_spec (h - 1) 0%Z) as [Heq|Hneq].
      * destruct k' as [|k''].
        -- lia.
        -- exfalso.
           assert (Hno1 : (h + height_at (false :: rest) 1 <> 0)%Z).
           { apply Hno_zero; lia. }
           unfold height_at in Hno1.
           cbn [firstn count_U count_D] in Hno1. lia.
      * destruct k' as [|k''].
        -- exfalso.
           unfold height_at in Hzero.
           cbn [firstn count_U count_D] in Hzero. lia.
        -- assert (Hrec : first_return_aux rest (h - 1)%Z (S idx) = S idx + S k'').
           { apply IH; try lia.
             - cbn [length] in Hk_bnd. lia.
             - intros j Hj1 Hj2.
               assert (Hno_Sj : (h + height_at (false :: rest) (S j) <> 0)%Z).
               { apply Hno_zero; lia. }
               unfold height_at in Hno_Sj.
               change (firstn (S j) (false :: rest)) with (false :: firstn j rest) in Hno_Sj.
               cbn [count_U count_D] in Hno_Sj. rewrite Nat2Z.inj_succ in Hno_Sj.
               unfold height_at. lia.
             - unfold height_at in Hzero.
               change (firstn (S (S k'')) (false :: rest)) with (false :: firstn (S k'') rest) in Hzero.
               cbn [count_U count_D] in Hzero. rewrite Nat2Z.inj_succ in Hzero.
               unfold height_at. lia. }
           rewrite Hrec. lia.
Qed.

(** Specialization to Dyck paths: first_return p is well-defined and finds
    the smallest k in [2, length p] where the height returns to 0. *)
Lemma first_return_dyck : forall p,
  is_dyck p -> 1 <= length p ->
  let k := first_return p in
  2 <= k <= length p /\
  (height_at p k = 0)%Z /\
  (forall j, 1 <= j -> j < k -> (1 <= height_at p j)%Z).
Proof.
  intros p Hdyck Hlen. unfold first_return.
  pose proof (first_return_aux_spec p 0%Z 0) as Hspec.
  set (r := first_return_aux p 0%Z 0 - 0) in *.
  destruct Hspec as [Hr_bnd [Hno_zero Hzero_at]].
  assert (Hr_eq : first_return_aux p 0%Z 0 = r) by (unfold r; lia).
  rewrite Hr_eq.
  destruct Hdyck as [Hbal Hnn].
  (* Show r ≥ 2 (since ht p 1 ≠ 0 for path starting with U). *)
  destruct (dyck_starts_U p (conj Hbal Hnn) Hlen) as [rest Hp_eq].
  assert (Hr_ge_1 : 1 <= r).
  { destruct r as [|r']; [|lia].
    (* r = 0: but then ht p 0 = 0, vacuously, but we need r ≥ 1 — what
       happens at r = 0? Actually r = 0 is the result if first_return_aux
       returns idx — i.e., p is empty. But p is non-empty (length ≥ 1). *)
    exfalso.
    rewrite Hp_eq in Hr_eq.
    cbn [first_return_aux] in Hr_eq.
    destruct (Z.eqb_spec (0 + 1) 0%Z) as [Heq0|Hneq0].
    - lia.
    - pose proof (first_return_aux_le rest (0+1)%Z 1) as Hle. lia. }
  (* ht p r = 0: either by Hzero_at or by Dyck closure if r = length p. *)
  assert (Hht_r : (height_at p r = 0)%Z).
  { destruct (Nat.lt_ge_cases r (length p)) as [Hlt|Hge].
    - rewrite <- (Z.add_0_l (height_at p r)). apply Hzero_at; exact Hlt.
    - assert (Hreq : r = length p) by lia.
      rewrite Hreq. pose proof (total_height_eq p) as Hth.
      change (height_at p (length p)) with (total_height p).
      rewrite Hth. lia. }
  (* Show r ≥ 2: for the path starting with U, ht p 1 = 1 ≠ 0. *)
  assert (Hr_ge_2 : 2 <= r).
  { destruct r as [|r']; [lia|].
    destruct r' as [|r'']; [|lia].
    (* r = 1: but ht p 1 = 1 (since p starts with U), contradicts Hht_r. *)
    exfalso.
    rewrite Hp_eq in Hht_r.
    unfold height_at in Hht_r.
    cbn [firstn count_U count_D] in Hht_r. lia. }
  (* Heights in [1, r-1] are >= 1 (non-zero AND non-negative). *)
  assert (Hheights_pos : forall j, 1 <= j -> j < r -> (1 <= height_at p j)%Z).
  { intros j Hj1 Hj_lt.
    assert (Hj_le : j <= length p) by lia.
    specialize (Hnn j Hj_le).
    assert (Hne : (0 + height_at p j <> 0)%Z) by (apply Hno_zero; assumption).
    lia. }
  split; [|split].
  - lia.
  - exact Hht_r.
  - exact Hheights_pos.
Qed.

(** Parity: height_at p k has same parity as k for k <= length p. *)
Lemma height_at_parity_eq : forall p k,
  k <= length p ->
  (height_at p k = 2 * Z.of_nat (count_U (firstn k p)) - Z.of_nat k)%Z.
Proof.
  intros p k Hk.
  unfold height_at.
  pose proof (count_UD_length (firstn k p)) as Hud.
  rewrite firstn_length_le in Hud by exact Hk.
  lia.
Qed.

(** First-return position is always even on a Dyck path. *)
Lemma first_return_dyck_even : forall p,
  is_dyck p -> 1 <= length p ->
  Nat.Even (first_return p).
Proof.
  intros p Hdyck Hlen.
  destruct (first_return_dyck p Hdyck Hlen) as [[Hge Hle] [Hzero _]].
  pose proof (height_at_parity_eq p (first_return p) Hle) as Hpar.
  rewrite Hzero in Hpar.
  (* 0 = 2 * cu - k, so k = 2 * cu, so k is even *)
  exists (count_U (firstn (first_return p) p)). lia.
Qed.

(* ========================================================================= *)
(*               PART X: DECOMPOSITION CORRECTNESS                          *)
(* ========================================================================= *)

(** Increment of height between consecutive positions: ±1. *)
Lemma height_at_step : forall p k,
  k < length p ->
  ((height_at p (S k) = height_at p k + 1)%Z \/
   (height_at p (S k) = height_at p k - 1)%Z).
Proof.
  intros p k Hk.
  pose proof (firstn_S_split p k Hk) as Hsplit.
  unfold height_at.
  rewrite Hsplit, count_U_app, count_D_app.
  destruct (nth k p false).
  - cbn [count_U count_D]. left. rewrite Nat2Z.inj_add. simpl. lia.
  - cbn [count_U count_D]. right. rewrite Nat2Z.inj_add. simpl. lia.
Qed.

(** Height just before first_return is 1, and the step at position (k-1) is D. *)
Lemma first_return_dyck_prev : forall p,
  is_dyck p -> 1 <= length p ->
  (height_at p (first_return p - 1) = 1)%Z.
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec.
  destruct Hspec as [[Hge Hle] [Hzero Hpos]].
  remember (first_return p) as k eqn:Hk_def.
  assert (Hk_pred_pos : 1 <= k - 1) by lia.
  assert (Hk_pred_lt : k - 1 < k) by lia.
  pose proof (Hpos (k - 1) Hk_pred_pos Hk_pred_lt) as Hpos_pred.
  pose proof (height_at_step p (k - 1)) as Hstep.
  assert (HSk_eq : S (k - 1) = k) by lia.
  rewrite HSk_eq in Hstep.
  assert (Hk_lt_p : k - 1 < length p) by lia.
  specialize (Hstep Hk_lt_p).
  destruct Hstep as [Hstep|Hstep].
  - rewrite Hzero in Hstep. exfalso. lia.
  - rewrite Hzero in Hstep. lia.
Qed.

(** The step at position (first_return p - 1) is D (false). *)
Lemma first_return_dyck_step_D : forall p,
  is_dyck p -> 1 <= length p ->
  nth (first_return p - 1) p false = false.
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec.
  destruct Hspec as [[Hge Hle] [Hzero _]].
  pose proof (first_return_dyck_prev p Hdyck Hlen) as Hprev.
  remember (first_return p) as k eqn:Hk_def.
  assert (Hk_lt : k - 1 < length p) by lia.
  pose proof (firstn_S_split p (k - 1) Hk_lt) as Hsplit.
  assert (HSk_eq : S (k - 1) = k) by lia.
  rewrite HSk_eq in Hsplit.
  destruct (nth (k - 1) p false) eqn:Hstep.
  - (* If step is true (U), height should INCREASE by 1: ht p k = ht p (k-1) + 1 = 2.
       But ht p k = 0. Contradiction. *)
    exfalso.
    assert (Hht_k : (height_at p k = height_at p (k-1) + 1)%Z).
    { unfold height_at.
      rewrite Hsplit, count_U_app, count_D_app.
      cbn [count_U count_D]. rewrite Nat2Z.inj_add. simpl. lia. }
    rewrite Hzero, Hprev in Hht_k. lia.
  - reflexivity.
Qed.

(** Recovery: p = dyck_compose a b for the decomposed parts. *)
Lemma dyck_decompose_recovers : forall p,
  is_dyck p -> 1 <= length p ->
  p = dyck_compose (firstn (first_return p - 2) (skipn 1 p))
                    (skipn (first_return p) p).
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec.
  destruct Hspec as [[Hge Hle] [Hzero _]].
  destruct (dyck_starts_U p Hdyck Hlen) as [rest Hp_eq].
  pose proof (first_return_dyck_step_D p Hdyck Hlen) as Hstep_D.
  remember (first_return p) as k eqn:Hk_def.
  unfold dyck_compose.
  rewrite Hp_eq at 1.
  f_equal.
  (* Goal: rest = firstn (k - 2) (skipn 1 p) ++ [false] ++ skipn k p *)
  rewrite Hp_eq.
  destruct k as [|k']; [lia|].
  (* Now k = S k', Hk_def : first_return p = S k', Hstep_D unchanged *)
  cbn [skipn].
  (* Goal: rest = firstn (S k' - 2) rest ++ [false] ++ skipn k' rest *)
  replace (S k' - 2) with (k' - 1) by lia.
  assert (Hk'_pos : 1 <= k') by lia.
  assert (Hk'_le : k' <= length rest).
  { rewrite Hp_eq in Hle.
    change (length (true :: rest)) with (S (length rest)) in Hle.
    lia. }
  assert (Hk'_lt : k' - 1 < length rest) by lia.
  pose proof (firstn_S_split rest (k' - 1) Hk'_lt) as Hsplit.
  (* Hsplit: firstn (S (k' - 1)) rest = firstn (k' - 1) rest ++ [nth (k' - 1) rest false] *)
  assert (Hnth_false : nth (k' - 1) rest false = false).
  { (* Hstep_D : nth (S k' - 1) p false = false (k replaced by remember+destruct).
       Replace p, simplify nth. *)
    rewrite Hp_eq in Hstep_D.
    replace (S k' - 1) with (S (k' - 1)) in Hstep_D by lia.
    cbn [nth] in Hstep_D. exact Hstep_D. }
  assert (Hsplit' : firstn k' rest = firstn (k' - 1) rest ++ [false]).
  { assert (Hkeq : k' = S (k' - 1)) by lia.
    rewrite Hkeq at 1.
    etransitivity. exact Hsplit.
    f_equal. f_equal. exact Hnth_false. }
  rewrite <- (firstn_skipn k' rest) at 1.
  rewrite Hsplit'.
  rewrite <- app_assoc. reflexivity.
Qed.

(** Length of decomposed pieces. *)
Lemma dyck_decompose_a_length : forall p,
  is_dyck p -> 1 <= length p ->
  length (firstn (first_return p - 2) (skipn 1 p)) = first_return p - 2.
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec. destruct Hspec as [[Hge Hle] _].
  rewrite firstn_length_le; [reflexivity|].
  rewrite length_skipn. lia.
Qed.

Lemma dyck_decompose_b_length : forall p,
  is_dyck p -> 1 <= length p ->
  length (skipn (first_return p) p) = length p - first_return p.
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec. destruct Hspec as [[Hge Hle] _].
  apply length_skipn.
Qed.

(** Helper: firstn (1 + j) p = firstn 1 p ++ firstn j (skipn 1 p). *)
Lemma firstn_split_at_one : forall (p : Path) (j : nat),
  1 <= length p ->
  firstn (S j) p = firstn 1 p ++ firstn j (skipn 1 p).
Proof.
  intros [|x rest] j Hlen.
  - cbn in Hlen. lia.
  - cbn [firstn skipn]. reflexivity.
Qed.

(** Height of skipn at position 0. *)
Lemma height_at_skipn_0 : forall p n,
  height_at (skipn n p) 0 = 0%Z.
Proof. intros. apply height_at_0. Qed.

(** Height under skipn: shifts by ht p n. *)
Lemma height_at_skipn : forall p n j,
  n + j <= length p ->
  height_at (skipn n p) j = (height_at p (n + j) - height_at p n)%Z.
Proof.
  intros p n j Hbnd.
  unfold height_at.
  (* firstn j (skipn n p) = elements [n, n+j) of p *)
  (* firstn (n + j) p = firstn n p ++ firstn j (skipn n p) *)
  assert (Hn_le : n <= length p) by lia.
  assert (Hdecomp : firstn (n + j) p = firstn n p ++ firstn j (skipn n p)).
  { rewrite <- (firstn_skipn n p) at 1.
    rewrite firstn_app.
    rewrite firstn_length_le by exact Hn_le.
    f_equal.
    - apply firstn_all2. rewrite firstn_length_le by exact Hn_le. lia.
    - f_equal. lia. }
  pose proof (f_equal count_U Hdecomp) as HcU.
  pose proof (f_equal count_D Hdecomp) as HcD.
  rewrite count_U_app in HcU. rewrite count_D_app in HcD.
  rewrite HcU, HcD.
  rewrite !Nat2Z.inj_add. lia.
Qed.

(** Height under firstn: equal to height_at p k for k <= n. *)
Lemma height_at_firstn : forall p n k,
  k <= n ->
  height_at (firstn n p) k = height_at p k.
Proof.
  intros p n k Hk. unfold height_at.
  rewrite firstn_firstn. rewrite Nat.min_l by exact Hk.
  reflexivity.
Qed.

(* ========================================================================= *)
(*               PART XI: DECOMPOSED PIECES ARE DYCK                        *)
(* ========================================================================= *)

(** Right piece (b) is Dyck. *)
Lemma dyck_decompose_b_is_dyck : forall p,
  is_dyck p -> 1 <= length p ->
  is_dyck (skipn (first_return p) p).
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec. destruct Hspec as [[Hge Hle] [Hzero _]].
  destruct Hdyck as [Hbal Hnn].
  remember (first_return p) as k eqn:Hk_def.
  split.
  - (* count_U b = count_D b *)
    pose proof (total_height_eq (skipn k p)) as Htot.
    pose proof (length_skipn k p) as Hlb.
    pose proof (height_at_skipn p k (length p - k) ltac:(lia)) as Hht_end.
    replace (k + (length p - k)) with (length p) in Hht_end by lia.
    rewrite Hzero in Hht_end.
    pose proof (count_UD_length p) as Hud.
    assert (Hend : (height_at p (length p) = 0)%Z).
    { unfold height_at. rewrite firstn_all_eq. lia. }
    rewrite Hend in Hht_end.
    unfold total_height in Htot.
    rewrite Hlb in Htot.
    rewrite Hht_end in Htot. lia.
  - (* heights ≥ 0 *)
    intros j Hj.
    pose proof (length_skipn k p) as Hlb.
    rewrite Hlb in Hj.
    rewrite height_at_skipn by lia.
    rewrite Hzero.
    assert (Hkj_le : k + j <= length p) by lia.
    specialize (Hnn (k + j) Hkj_le). lia.
Qed.

(** Left piece (a) is Dyck. The key fact:
    height_at a j = height_at p (S j) - 1 for j ≤ first_return p - 2. *)
Lemma dyck_decompose_a_is_dyck : forall p,
  is_dyck p -> 1 <= length p ->
  is_dyck (firstn (first_return p - 2) (skipn 1 p)).
Proof.
  intros p Hdyck Hlen.
  pose proof (first_return_dyck p Hdyck Hlen) as Hspec.
  cbn zeta in Hspec. destruct Hspec as [[Hge Hle] [Hzero Hpos]].
  pose proof (first_return_dyck_prev p Hdyck Hlen) as Hprev.
  destruct (dyck_starts_U p (* preserves Hdyck *) Hdyck Hlen) as [rest Hp_eq].
  destruct Hdyck as [Hbal_p Hnn_p].
  remember (first_return p) as k eqn:Hk_def.

  assert (Hk_2_le : k - 2 <= length p - 1).
  { lia. }
  assert (Hskipn1_len : length (skipn 1 p) = length p - 1).
  { apply length_skipn. }
  assert (Hk_2_bnd : k - 2 <= length (skipn 1 p)) by lia.

  (* Main height relationship *)
  assert (Hht_a : forall j, j <= k - 2 ->
                  (height_at (firstn (k - 2) (skipn 1 p)) j = height_at p (S j) - 1)%Z).
  { intros j Hj.
    rewrite height_at_firstn by exact Hj.
    rewrite height_at_skipn by lia.
    replace (1 + j) with (S j) by lia.
    (* Need: height_at p 1 = 1 *)
    assert (Hht1 : (height_at p 1 = 1)%Z).
    { rewrite Hp_eq.
      unfold height_at.
      cbn [firstn count_U count_D]. lia. }
    rewrite Hht1. reflexivity. }

  split.
  - (* count_U a = count_D a, via ht a (length a) = 0 *)
    pose proof (Hht_a (k - 2) (Nat.le_refl _)) as Hht_end.
    replace (S (k - 2)) with (k - 1) in Hht_end by lia.
    rewrite Hprev in Hht_end.
    pose proof (total_height_eq (firstn (k - 2) (skipn 1 p))) as Htot.
    unfold total_height in Htot.
    rewrite firstn_length_le in Htot by exact Hk_2_bnd.
    rewrite Hht_end in Htot. lia.
  - (* heights ≥ 0 *)
    intros j Hj.
    rewrite firstn_length_le in Hj by exact Hk_2_bnd.
    specialize (Hht_a j Hj).
    rewrite Hht_a.
    destruct j as [|j'].
    + (* j = 0: ht p 1 - 1 = 0 *)
      rewrite Hp_eq.
      unfold height_at.
      cbn [firstn count_U count_D]. lia.
    + (* j = S j': S (S j') in [2, k - 1] so ht p (S (S j')) >= 1 *)
      assert (HSSj_pos : 1 <= S (S j')) by lia.
      assert (HSSj_lt : S (S j') < k) by lia.
      specialize (Hpos (S (S j')) HSSj_pos HSSj_lt). lia.
Qed.

(* ========================================================================= *)
(*               PART XII: FIRST_RETURN OF COMPOSE                          *)
(* ========================================================================= *)

(** For a composition of two Dyck paths, the first return is at position
    2 + length a (right after the matching D for the initial U). *)
Lemma first_return_compose : forall a b,
  is_dyck a -> is_dyck b ->
  first_return (dyck_compose a b) = 2 + length a.
Proof.
  intros a b Ha Hb.
  pose proof (dyck_compose_is_dyck a b Ha Hb) as Hcomp_dyck.
  destruct Ha as [HaUD Hanh].
  destruct Hb as [HbUD Hbnh].
  assert (Hta : (total_height a = 0)%Z).
  { rewrite total_height_eq. lia. }
  assert (Htb : (total_height b = 0)%Z).
  { rewrite total_height_eq. lia. }
  unfold first_return.
  apply first_return_aux_find with (k := 2 + length a).
  - lia.
  - rewrite dyck_compose_length. lia.
  - (* For 1 <= j < 2 + length a, height_at compose j != 0 *)
    intros j Hj_pos Hj_lt.
    unfold dyck_compose.
    change (true :: a ++ [false] ++ b) with ((true :: a) ++ (false :: b)).
    (* j in [1, 1 + length a], so j <= S (length a), use height_at_app_left *)
    assert (Hj_le_a : j <= S (length a)) by lia.
    rewrite height_at_app_left.
    + destruct j as [|j']; [lia|].
      rewrite height_at_cons_U.
      assert (Hj'_le : j' <= length a) by (cbn [length] in Hj_le_a; lia).
      specialize (Hanh j' Hj'_le). lia.
    + cbn [length]. lia.
  - (* height_at compose (2 + length a) = 0 *)
    unfold dyck_compose.
    change (true :: a ++ [false] ++ b) with ((true :: a) ++ (false :: b)).
    change (length (true :: a)) with (S (length a)).
    replace (2 + length a) with (S (length a) + 1) by lia.
    rewrite height_at_app_right.
    + rewrite total_height_cons_U, Hta.
      change 1 with (S 0). rewrite height_at_cons_D, height_at_0. lia.
    + change (length (false :: b)) with (S (length b)). lia.
Qed.

(* ========================================================================= *)
(*               PART XIII: COMPOSE-DECOMPOSE INVERSE                       *)
(* ========================================================================= *)

(** decompose ∘ compose = identity on (Dyck a) × (Dyck b). *)
Lemma decompose_compose_a : forall a b,
  is_dyck a -> is_dyck b ->
  firstn (first_return (dyck_compose a b) - 2) (skipn 1 (dyck_compose a b)) = a.
Proof.
  intros a b Ha Hb.
  rewrite first_return_compose by assumption.
  replace (2 + length a - 2) with (length a) by lia.
  unfold dyck_compose.
  cbn [skipn].
  (* firstn (length a) (a ++ [false] ++ b) = a *)
  rewrite firstn_app.
  rewrite firstn_all_eq.
  replace (length a - length a) with 0 by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma decompose_compose_b : forall a b,
  is_dyck a -> is_dyck b ->
  skipn (first_return (dyck_compose a b)) (dyck_compose a b) = b.
Proof.
  intros a b Ha Hb.
  rewrite first_return_compose by assumption.
  unfold dyck_compose.
  (* skipn (2 + length a) (true :: a ++ [false] ++ b) *)
  replace (2 + length a) with (S (S (length a))) by lia.
  rewrite skipn_cons.
  (* Now: skipn (S (length a)) (a ++ [false] ++ b) = b *)
  rewrite skipn_app.
  rewrite skipn_all2 by lia.
  cbn [app]. replace (S (length a) - length a) with 1 by lia.
  cbn [skipn]. reflexivity.
Qed.

(** Length of dyck_compose's two pieces sums correctly. *)
Lemma dyck_compose_length_split : forall a b,
  length a + 2 + length b = length (dyck_compose a b).
Proof.
  intros a b. rewrite dyck_compose_length. lia.
Qed.

(** Compose is injective (when both arguments are Dyck). *)
Lemma dyck_compose_injective : forall a1 b1 a2 b2,
  is_dyck a1 -> is_dyck b1 -> is_dyck a2 -> is_dyck b2 ->
  dyck_compose a1 b1 = dyck_compose a2 b2 ->
  a1 = a2 /\ b1 = b2.
Proof.
  intros a1 b1 a2 b2 Ha1 Hb1 Ha2 Hb2 Heq.
  pose proof (decompose_compose_a a1 b1 Ha1 Hb1) as Ha1_eq.
  pose proof (decompose_compose_a a2 b2 Ha2 Hb2) as Ha2_eq.
  pose proof (decompose_compose_b a1 b1 Ha1 Hb1) as Hb1_eq.
  pose proof (decompose_compose_b a2 b2 Ha2 Hb2) as Hb2_eq.
  rewrite Heq in Ha1_eq, Hb1_eq.
  split.
  - transitivity (firstn (first_return (dyck_compose a2 b2) - 2)
                          (skipn 1 (dyck_compose a2 b2))).
    + symmetry. exact Ha1_eq.
    + exact Ha2_eq.
  - transitivity (skipn (first_return (dyck_compose a2 b2)) (dyck_compose a2 b2)).
    + symmetry. exact Hb1_eq.
    + exact Hb2_eq.
Qed.

(* ========================================================================= *)
(*               PART XIV: CARDINALITY VIA PERMUTATION                      *)
(* ========================================================================= *)

(** List of all Dyck paths of length 2n. *)
Definition dyck_list (n : nat) : list Path := filter is_dyck_b (all_paths (2 * n)).

Lemma dyck_list_length_eq : forall n, length (dyck_list n) = num_dyck n.
Proof. intros n. unfold dyck_list, num_dyck. reflexivity. Qed.

(** Elements of dyck_list n have length 2n and are Dyck. *)
Lemma in_dyck_list : forall n p,
  In p (dyck_list n) -> length p = 2 * n /\ is_dyck p.
Proof.
  intros n p Hin. unfold dyck_list in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hpaths Hb].
  pose proof (all_paths_length _ _ Hpaths) as Hlen.
  apply is_dyck_b_iff in Hb.
  split; [exact Hlen|].
  unfold is_dyck. destruct Hb as [Hnn Hend]. split.
  - (* count_U = count_D from height_at p (length p) = 0 *)
    pose proof (length_2n_count_U_iff_height_0 n p Hlen) as Hiff.
    apply Hiff in Hend.
    pose proof (count_UD_length p) as HUD.
    rewrite Hlen in HUD. lia.
  - exact Hnn.
Qed.

(** Conversely: any Dyck path of length 2n is in dyck_list n. *)
Lemma in_dyck_list_iff : forall n p,
  In p (dyck_list n) <-> (length p = 2 * n /\ is_dyck p).
Proof.
  intros n p. split.
  - apply in_dyck_list.
  - intros [Hlen Hdyck]. unfold dyck_list. apply filter_In.
    split.
    + apply all_paths_complete_len. exact Hlen.
    + apply is_dyck_b_iff. destruct Hdyck as [Hbal Hnn].
      split; [exact Hnn|].
      apply length_2n_count_U_iff_height_0 with (n := n).
      * exact Hlen.
      * pose proof (count_UD_length p) as HUD. rewrite Hlen in HUD. lia.
Qed.

(** List of (i, a, b) triples projected to dyck_compose values. *)
Definition triple_list (n : nat) : list Path :=
  flat_map (fun i => map (fun ab : Path * Path => dyck_compose (fst ab) (snd ab))
                          (list_prod (dyck_list i) (dyck_list (n - i))))
           (seq 0 (S n)).

(** length flat_map = sum of lengths *)
Lemma length_flat_map_seq : forall (f : nat -> list Path) start cnt,
  length (flat_map f (seq start cnt)) =
  fold_right Nat.add 0 (map (fun i => length (f i)) (seq start cnt)).
Proof.
  intros f start cnt. revert start.
  induction cnt as [|cnt' IH]; intros start; simpl.
  - reflexivity.
  - rewrite length_app, IH. reflexivity.
Qed.

(** Length of triple_list = catalan_conv n. *)
Lemma triple_list_length : forall n, length (triple_list n) = catalan_conv n.
Proof.
  intros n. unfold triple_list, catalan_conv, sum_to.
  rewrite length_flat_map_seq.
  f_equal. apply map_ext.
  intros i. rewrite length_map.
  rewrite list_prod_length_eq.
  rewrite !dyck_list_length_eq. reflexivity.
Qed.

(** For (a, b) ∈ list_prod (dyck_list i) (dyck_list j), a is Dyck of length 2i, b of length 2j. *)
Lemma in_list_prod_dyck : forall i j a b,
  In (a, b) (list_prod (dyck_list i) (dyck_list j)) ->
  length a = 2 * i /\ is_dyck a /\ length b = 2 * j /\ is_dyck b.
Proof.
  intros i j a b Hin.
  apply in_prod_iff in Hin.
  destruct Hin as [Ha Hb].
  apply in_dyck_list in Ha. apply in_dyck_list in Hb.
  destruct Ha as [Hla Hda]. destruct Hb as [Hlb Hdb].
  split; [exact Hla|].
  split; [exact Hda|].
  split; [exact Hlb| exact Hdb].
Qed.

(** Generic NoDup for flat_map over a list. *)
Lemma NoDup_flat_map_disj : forall (A B : Type) (f : A -> list B) (l : list A),
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y, In x l -> In y l -> x <> y ->
               forall e, In e (f x) -> ~ In e (f y)) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l. induction l as [|a rest IH]; intros HND HF Hdisj.
  - simpl. constructor.
  - simpl. apply NoDup_app_disj.
    + apply HF. left. reflexivity.
    + apply IH.
      * inversion HND. assumption.
      * intros x Hx. apply HF. right. exact Hx.
      * intros x y Hx Hy Hne e He.
        apply (Hdisj x y).
        -- right. exact Hx.
        -- right. exact Hy.
        -- exact Hne.
        -- exact He.
    + intros e He_a He_rest.
      apply in_flat_map in He_rest.
      destruct He_rest as [y [Hy_in Hey]].
      assert (Hne : a <> y).
      { inversion HND as [|? ? Hnotin_a _]. intros Hcontra. subst y. contradiction. }
      assert (HIa : In a (a :: rest)) by (left; reflexivity).
      assert (HIy : In y (a :: rest)) by (right; exact Hy_in).
      pose proof (Hdisj a y HIa HIy Hne e He_a) as Hnotin.
      contradiction.
Qed.

(** NoDup of triple_list n. *)
Lemma NoDup_triple_list : forall n, NoDup (triple_list n).
Proof.
  intros n. unfold triple_list.
  apply NoDup_flat_map_disj.
  - apply seq_NoDup.
  - intros i Hi_in.
    (* NoDup of map compose (list_prod ...) *)
    apply NoDup_map_inj_on.
    + intros [a1 b1] [a2 b2] Hp1 Hp2 Hcomp_eq.
      simpl in Hcomp_eq.
      pose proof (in_list_prod_dyck _ _ _ _ Hp1) as [Hla1 [Hda1 [Hlb1 Hdb1]]].
      pose proof (in_list_prod_dyck _ _ _ _ Hp2) as [Hla2 [Hda2 [Hlb2 Hdb2]]].
      destruct (dyck_compose_injective a1 b1 a2 b2 Hda1 Hdb1 Hda2 Hdb2 Hcomp_eq).
      f_equal; assumption.
    + apply NoDup_list_prod.
      * unfold dyck_list. apply NoDup_filter, NoDup_all_paths.
      * unfold dyck_list. apply NoDup_filter, NoDup_all_paths.
  - intros i j Hi_in Hj_in Hne p Hp_in_i Hp_in_j.
    (* If p = compose a1 b1 from group i, and p = compose a2 b2 from group j, then i = j. *)
    apply in_map_iff in Hp_in_i, Hp_in_j.
    destruct Hp_in_i as [[a1 b1] [Hp_eq_i Hin1]].
    destruct Hp_in_j as [[a2 b2] [Hp_eq_j Hin2]].
    simpl in Hp_eq_i, Hp_eq_j.
    pose proof (in_list_prod_dyck _ _ _ _ Hin1) as [Hla1 [Hda1 [Hlb1 Hdb1]]].
    pose proof (in_list_prod_dyck _ _ _ _ Hin2) as [Hla2 [Hda2 [Hlb2 Hdb2]]].
    rewrite <- Hp_eq_j in Hp_eq_i.
    destruct (dyck_compose_injective a1 b1 a2 b2 Hda1 Hdb1 Hda2 Hdb2 Hp_eq_i) as [Ha_eq _].
    apply Hne.
    assert (length a1 = length a2) by (rewrite Ha_eq; reflexivity).
    rewrite Hla1, Hla2 in H. lia.
Qed.

(** Compose preserves Dyck-ness and length: a witness for "p in dyck_list (S n)". *)
Lemma compose_in_dyck_list : forall n i a b,
  i <= n ->
  In a (dyck_list i) -> In b (dyck_list (n - i)) ->
  In (dyck_compose a b) (dyck_list (S n)).
Proof.
  intros n i a b Hi Ha Hb.
  apply in_dyck_list in Ha, Hb.
  destruct Ha as [Hla Hda]. destruct Hb as [Hlb Hdb].
  apply in_dyck_list_iff. split.
  - rewrite dyck_compose_length. lia.
  - apply dyck_compose_is_dyck; assumption.
Qed.

(** Forward direction: every triple gives an element of dyck_list. *)
Lemma triple_list_in_dyck_list : forall n p,
  In p (triple_list n) -> In p (dyck_list (S n)).
Proof.
  intros n p Hin.
  unfold triple_list in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [i [Hi_in Hpi]].
  apply in_seq in Hi_in. destruct Hi_in as [_ Hi_lt].
  apply in_map_iff in Hpi.
  destruct Hpi as [[a b] [Heq Hab_in]]. simpl in Heq. subst p.
  apply compose_in_dyck_list with (n := n) (i := i); [lia | |].
  - apply in_prod_iff in Hab_in. destruct Hab_in. assumption.
  - apply in_prod_iff in Hab_in. destruct Hab_in. assumption.
Qed.

(** Backward direction: every Dyck path decomposes into a triple. *)
Lemma dyck_list_in_triple_list : forall n p,
  In p (dyck_list (S n)) -> In p (triple_list n).
Proof.
  intros n p Hin.
  apply in_dyck_list in Hin. destruct Hin as [Hlen Hdyck].
  assert (Hlen_pos : 1 <= length p) by lia.
  pose proof (dyck_decompose_recovers p Hdyck Hlen_pos) as Hrec.
  pose proof (dyck_decompose_a_is_dyck p Hdyck Hlen_pos) as Ha_dyck.
  pose proof (dyck_decompose_b_is_dyck p Hdyck Hlen_pos) as Hb_dyck.
  pose proof (dyck_decompose_a_length p Hdyck Hlen_pos) as Hla.
  pose proof (dyck_decompose_b_length p Hdyck Hlen_pos) as Hlb.
  pose proof (first_return_dyck p Hdyck Hlen_pos) as Hspec.
  cbn zeta in Hspec. destruct Hspec as [[Hge Hle] _].
  pose proof (first_return_dyck_even p Hdyck Hlen_pos) as Heven.
  (* Heven gives k = 2 * m for some m, hence (k - 2) = 2 * (m - 1) *)
  destruct Heven as [m Hm].
  remember (first_return p) as k eqn:Hk_def.
  set (a := firstn (k - 2) (skipn 1 p)) in *.
  set (b := skipn k p) in *.
  (* k = 2m, so k - 2 = 2 * (m - 1). length a = k - 2 = 2 * (m - 1). *)
  (* length b = length p - k = 2 * (S n) - 2m = 2 * (S n - m) *)
  (* Hge: 2 <= k = 2m, so m >= 1. *)
  (* Hle: k <= length p = 2(S n), so 2m <= 2(S n), m <= S n. *)
  assert (Hm_ge : 1 <= m) by lia.
  assert (Hm_le : m <= S n) by lia.
  set (i := m - 1).
  unfold triple_list. apply in_flat_map.
  exists i. split.
  - apply in_seq. split; [lia|].
    unfold i. simpl. lia.
  - apply in_map_iff. exists (a, b). split.
    + simpl. symmetry. exact Hrec.
    + apply in_prod_iff. split.
      * apply in_dyck_list_iff. split.
        -- unfold i. rewrite Hla. lia.
        -- exact Ha_dyck.
      * apply in_dyck_list_iff. split.
        -- unfold i. rewrite Hlb. lia.
        -- exact Hb_dyck.
Qed.

(** Permutation between dyck_list (S n) and triple_list n. *)
Lemma dyck_list_perm_triple_list : forall n,
  Permutation (dyck_list (S n)) (triple_list n).
Proof.
  intros n. apply NoDup_Permutation.
  - unfold dyck_list. apply NoDup_filter, NoDup_all_paths.
  - apply NoDup_triple_list.
  - intros p. split.
    + apply dyck_list_in_triple_list.
    + apply triple_list_in_dyck_list.
Qed.

(* ========================================================================= *)
(*               PART XV: MAIN CATALAN RECURRENCE THEOREM                   *)
(* ========================================================================= *)

(** THE MAIN THEOREM: C_{n+1} = sum_{i=0}^n C_i * C_{n-i}.

    This is the classical Catalan recurrence, proved here constructively
    via the first-return decomposition bijection:

       Dyck_(n+1)  ↔  ⊎_{i=0}^n (Dyck_i × Dyck_{n-i})
       p = U a D b  ←→  (i, a, b) where k = first_return p, i = (k-2)/2

    No Admitted, no classical axioms, no AC. *)
Theorem catalan_recurrence : forall n,
  num_dyck (S n) = catalan_conv n.
Proof.
  intros n.
  rewrite <- (dyck_list_length_eq (S n)).
  rewrite (Permutation_length (dyck_list_perm_triple_list n)).
  apply triple_list_length.
Qed.
