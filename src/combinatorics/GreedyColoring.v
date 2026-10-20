(* ========================================================================= *)
(*                                                                          *)
(*       GREEDY GRAPH COLORING: chi(G) <= Delta^-(G) + 1 VIA L5/mu          *)
(*                                                                          *)
(*  CLASSICAL THEOREM (folklore):                                           *)
(*    Any finite graph G has chromatic number <= Delta(G) + 1, where Delta  *)
(*    is the maximum degree. Proof: greedy coloring in vertex order --      *)
(*    assign each vertex the smallest color not used by its neighbors.      *)
(*                                                                          *)
(*  STRONGER VERSION (THIS FILE):                                           *)
(*    Delta^- = max backward degree (# of edges (y,x) with y < x).          *)
(*    Greedy in order 0,1,...,n-1 uses <= Delta^- + 1 colors. Since         *)
(*    Delta^- <= Delta for symmetric graphs, classical bound follows.       *)
(*                                                                          *)
(*  CONSTRUCTIVE CONTENT:                                                   *)
(*    For each vertex x in order, assign:                                   *)
(*      c(x) := mu k <= Delta^- such that k not used by earlier neighbors   *)
(*    L5/mu extracts this smallest-k DETERMINISTICALLY.                     *)
(*    Pigeonhole shows such k exists: <= Delta^- neighbors block, K+1       *)
(*    >= Delta^- + 1 colors available.                                      *)
(*                                                                          *)
(*  WHY THIS BELONGS HERE:                                                  *)
(*    Pure L5/mu application. The coloring is a recursive process where     *)
(*    each step is a bounded mu-search over a decidable predicate, and     *)
(*    termination of the OUTER recursion is by induction on vertex index.  *)
(*                                                                          *)
(*  E/R/R DECOMPOSITION:                                                    *)
(*    Elements (L1): vertices [0..n-1], colors [0..K].                     *)
(*    Roles (L1):    backward neighbor, color assignment, forbidden set.   *)
(*    Rules (L2):    proper coloring (adj => distinct colors).             *)
(*    Order (L5):    smallest unused color via mu-search.                   *)
(*    Process (P4):  coloring as iteration over vertex index.              *)
(*                                                                          *)
(*    P4-DIAGNOSTIC: could it be otherwise under same rules?                *)
(*    NO: the algorithm is DETERMINISTIC (smallest k by mu_le) and         *)
(*    properness follows from the structure of color_ok, which is forced   *)
(*    by the proper-coloring requirement.                                  *)
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

(** mu_le P K: smallest k <= K with P k = true, or None. *)
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

Lemma mu_le_complete : forall P K k,
  k <= K -> P k = true -> exists j, mu_le P K = Some j /\ j <= k.
Proof.
  intros P K. induction K as [|K' IH]; intros k Hk HP.
  - assert (k = 0) by lia. subst. simpl. rewrite HP. exists 0. split; [reflexivity | lia].
  - case_eq (mu_le P K').
    + intros j Em.
      exists j.
      assert (Hgoal : mu_le P (S K') = Some j).
      { simpl. rewrite Em. reflexivity. }
      split; [exact Hgoal|].
      destruct (Compare_dec.le_lt_dec k K') as [Hle|Hgt].
      * destruct (IH _ Hle HP) as [j' [Hj' Hjk]].
        rewrite Em in Hj'. injection Hj' as <-. exact Hjk.
      * apply mu_le_sound in Em. destruct Em as [_ Hjb]. lia.
    + intros En.
      assert (Hkeq : k = S K').
      { destruct (Compare_dec.le_lt_dec k K') as [Hle|Hgt].
        - destruct (IH _ Hle HP) as [j' [Hj' _]]. rewrite En in Hj'. discriminate.
        - lia. }
      subst k.
      exists (S K').
      assert (Hgoal : mu_le P (S K') = Some (S K')).
      { simpl. rewrite En. rewrite HP. reflexivity. }
      split; [exact Hgoal | lia].
Qed.

(* ========================================================================= *)
(*               PART II: REMOVE-ONE HELPER                                  *)
(* ========================================================================= *)

Fixpoint remove_one (x : nat) (L : list nat) : list nat :=
  match L with
  | [] => []
  | y :: ys => if Nat.eqb x y then ys else y :: remove_one x ys
  end.

Lemma remove_one_length : forall x L,
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

Lemma remove_one_preserves : forall x y L,
  x <> y -> In y L -> In y (remove_one x L).
Proof.
  intros x y L Hxy Hin. induction L as [|z L' IH].
  - contradiction.
  - simpl. destruct (Nat.eqb x z) eqn:E.
    + apply Nat.eqb_eq in E. subst z.
      destruct Hin as [Hyx|Hin'].
      * exfalso. apply Hxy. exact Hyx.
      * exact Hin'.
    + destruct Hin as [Hyz|Hin'].
      * subst z. left. reflexivity.
      * right. apply IH. exact Hin'.
Qed.

(* ========================================================================= *)
(*               PART III: PIGEONHOLE FOR COLORS                             *)
(* ========================================================================= *)

(** If list L has length <= K, then some k <= K is NOT in L. *)
Lemma exists_color_outside_K : forall (L : list nat) (K : nat),
  length L <= K ->
  exists k, k <= K /\ ~ In k L.
Proof.
  intros L K. revert L. induction K as [|K' IH]; intros L HL.
  - destruct L as [|x L']; [|simpl in HL; lia].
    exists 0. split; [lia | intros []].
  - destruct (List.in_dec Nat.eq_dec (S K') L) as [Hin|Hnin].
    + assert (HrL : length (remove_one (S K') L) <= K').
      { rewrite remove_one_length; [|exact Hin]. lia. }
      destruct (IH _ HrL) as [k [Hk Hknin]].
      exists k. split; [lia|].
      intros Hin_L. apply Hknin.
      apply remove_one_preserves; [lia | exact Hin_L].
    + exists (S K'). split; [lia | exact Hnin].
Qed.

(* ========================================================================= *)
(*               PART IV: GRAPH AND COLOR-OK PREDICATE                       *)
(* ========================================================================= *)

Definition adj_rel := nat -> nat -> bool.

(** Colors assigned to backward neighbors of i (the "forbidden" set). *)
Definition forbidden_colors (adj : adj_rel) (prev : list nat) (i : nat) : list nat :=
  map (fun y => nth y prev 0) (filter (fun y => adj y i) (seq 0 i)).

(** color_ok prev i k: color k is permitted for vertex i given prior assignments prev. *)
Definition color_ok (adj : adj_rel) (prev : list nat) (i : nat) (k : nat) : bool :=
  forallb (fun y =>
    if adj y i
    then negb (Nat.eqb (nth y prev 0) k)
    else true) (seq 0 i).

Lemma color_ok_from_not_in : forall adj prev i k,
  ~ In k (forbidden_colors adj prev i) ->
  color_ok adj prev i k = true.
Proof.
  intros adj prev i k Hnin.
  unfold color_ok. apply forallb_forall.
  intros y Hy. apply in_seq in Hy. destruct Hy as [_ Hy].
  destruct (adj y i) eqn:Eadj.
  - apply negb_true_iff. apply Nat.eqb_neq.
    intros Heq. apply Hnin.
    unfold forbidden_colors. apply in_map_iff.
    exists y. split; [exact Heq |].
    apply filter_In. split; [apply in_seq; lia | exact Eadj].
  - reflexivity.
Qed.

Lemma color_ok_correct : forall adj prev i k y,
  color_ok adj prev i k = true ->
  y < i ->
  adj y i = true ->
  nth y prev 0 <> k.
Proof.
  intros adj prev i k y H Hy Hadj.
  unfold color_ok in H.
  apply forallb_forall with (x := y) in H; [|apply in_seq; lia].
  rewrite Hadj in H. apply negb_true_iff in H. apply Nat.eqb_neq in H. exact H.
Qed.

(* ========================================================================= *)
(*               PART V: BUILD COLORS LIST                                   *)
(* ========================================================================= *)

(** Greedy coloring: at each step i, append the smallest color k <= K
    such that color_ok adj prev i k = true; fall back to 0 if K too small. *)
Fixpoint build_colors (adj : adj_rel) (K : nat) (i : nat) : list nat :=
  match i with
  | 0 => []
  | S i' =>
    let prev := build_colors adj K i' in
    let next :=
      match mu_le (color_ok adj prev i') K with
      | Some k => k
      | None => 0
      end
    in
    prev ++ [next]
  end.

Lemma build_colors_length : forall adj K i,
  length (build_colors adj K i) = i.
Proof.
  intros adj K. induction i as [|i' IH]; simpl.
  - reflexivity.
  - destruct (mu_le _ _) as [k|];
    rewrite app_length, IH; simpl; lia.
Qed.

Lemma build_colors_step : forall adj K i,
  build_colors adj K (S i) =
    build_colors adj K i ++
    [match mu_le (color_ok adj (build_colors adj K i) i) K with
     | Some k => k | None => 0 end].
Proof. intros. reflexivity. Qed.

(** Stability: adding more vertices doesn't change colors of earlier vertices. *)
Lemma build_colors_nth_stable : forall adj K i j x,
  i <= j -> x < i ->
  nth x (build_colors adj K i) 0 = nth x (build_colors adj K j) 0.
Proof.
  intros adj K i j x Hij Hx.
  remember (j - i) as d. revert i j Hij Hx Heqd.
  induction d as [|d' IHd]; intros i j Hij Hx Hd.
  - assert (i = j) by lia. subst. reflexivity.
  - assert (HiSi : S i <= j) by lia.
    assert (Hxi : x < S i) by lia.
    transitivity (nth x (build_colors adj K (S i)) 0).
    + rewrite build_colors_step.
      rewrite app_nth1; [reflexivity | rewrite build_colors_length; exact Hx].
    + apply IHd; [lia | exact Hxi | lia].
Qed.

(* ========================================================================= *)
(*               PART VI: BACKWARD DEGREE AND COLOR EXISTENCE                *)
(* ========================================================================= *)

(** Backward degree of i: # of y < i with adj y i = true. *)
Definition back_degree (adj : adj_rel) (i : nat) : nat :=
  length (filter (fun y => adj y i) (seq 0 i)).

Lemma forbidden_colors_length_eq : forall adj prev i,
  length (forbidden_colors adj prev i) = back_degree adj i.
Proof.
  intros. unfold forbidden_colors, back_degree.
  rewrite map_length. reflexivity.
Qed.

(** Greedy step succeeds whenever K >= back_degree. *)
Lemma greedy_step_succeeds : forall adj K prev i,
  back_degree adj i <= K ->
  exists k, k <= K /\ color_ok adj prev i k = true.
Proof.
  intros adj K prev i Hdeg.
  assert (Hlen : length (forbidden_colors adj prev i) <= K).
  { rewrite forbidden_colors_length_eq. exact Hdeg. }
  destruct (exists_color_outside_K _ _ Hlen) as [k [Hk Hknin]].
  exists k. split; [exact Hk|].
  apply color_ok_from_not_in. exact Hknin.
Qed.

(* ========================================================================= *)
(*               PART VII: MAIN THEOREMS                                     *)
(* ========================================================================= *)

(** Backward degree bound: K bounds every backward degree up to n. *)
Definition back_deg_bounded (adj : adj_rel) (n K : nat) : Prop :=
  forall i, i < n -> back_degree adj i <= K.

(** PROPERNESS: for any edge (x, y) with x < y, greedy assigns distinct colors. *)
Theorem build_colors_proper : forall adj K n x y,
  back_deg_bounded adj n K ->
  y < n -> x < y -> adj x y = true ->
  nth x (build_colors adj K n) 0 <> nth y (build_colors adj K n) 0.
Proof.
  intros adj K n x y Hbound Hyn Hxy Hadj.
  rewrite <- (build_colors_nth_stable adj K (S y) n x); [|lia|lia].
  rewrite <- (build_colors_nth_stable adj K (S y) n y); [|lia|lia].
  rewrite build_colors_step.
  rewrite app_nth1; [|rewrite build_colors_length; exact Hxy].
  rewrite app_nth2; [|rewrite build_colors_length; lia].
  rewrite build_colors_length.
  replace (y - y) with 0 by lia. simpl.
  destruct (mu_le (color_ok adj (build_colors adj K y) y) K) as [k|] eqn:E.
  - apply mu_le_sound in E. destruct E as [Hok _].
    intros Heq. apply (color_ok_correct adj _ y k x Hok Hxy Hadj). exact Heq.
  - exfalso.
    destruct (greedy_step_succeeds adj K (build_colors adj K y) y (Hbound y Hyn)) as [k [Hk Hok]].
    pose proof (mu_le_none_all_false _ _ E _ Hk) as Hf.
    rewrite Hf in Hok. discriminate.
Qed.

(** BOUND: every greedy color is <= K. *)
Theorem build_colors_bounded : forall adj K n i,
  back_deg_bounded adj n K ->
  i < n ->
  nth i (build_colors adj K n) 0 <= K.
Proof.
  intros adj K n i Hbound Hin.
  rewrite <- (build_colors_nth_stable adj K (S i) n i); [|lia|lia].
  rewrite build_colors_step.
  rewrite app_nth2; [|rewrite build_colors_length; lia].
  rewrite build_colors_length.
  replace (i - i) with 0 by lia. simpl.
  destruct (mu_le (color_ok adj (build_colors adj K i) i) K) as [k|] eqn:E.
  - apply mu_le_sound in E. destruct E. assumption.
  - exfalso.
    destruct (greedy_step_succeeds adj K (build_colors adj K i) i (Hbound i Hin)) as [k [Hk Hok]].
    pose proof (mu_le_none_all_false _ _ E _ Hk) as Hf.
    rewrite Hf in Hok. discriminate.
Qed.

(* ========================================================================= *)
(*               PART VIII: COROLLARIES FOR SYMMETRIC GRAPHS                 *)
(* ========================================================================= *)

(** A function c : nat -> nat is a proper coloring of G[0..n-1]. *)
Definition is_proper_coloring (adj : adj_rel) (n : nat) (c : nat -> nat) : Prop :=
  forall x y, x < n -> y < n -> adj x y = true -> c x <> c y.

(** The greedy coloring function. *)
Definition greedy_coloring (adj : adj_rel) (K n : nat) : nat -> nat :=
  fun x => nth x (build_colors adj K n) 0.

(** For symmetric irreflexive graphs, greedy is a proper coloring. *)
Theorem greedy_proper_symmetric : forall adj K n,
  (forall x y, adj x y = adj y x) ->
  (forall x, adj x x = false) ->
  back_deg_bounded adj n K ->
  is_proper_coloring adj n (greedy_coloring adj K n).
Proof.
  intros adj K n Hsym Hirr Hbound x y Hxn Hyn Hadj.
  unfold greedy_coloring.
  destruct (Nat.compare_spec x y) as [Heq|Hlt|Hgt].
  - rewrite Heq in Hadj. rewrite Hirr in Hadj. discriminate.
  - apply build_colors_proper; assumption.
  - rewrite Hsym in Hadj.
    intros Heq. symmetry in Heq.
    apply (build_colors_proper adj K n y x Hbound Hxn Hgt Hadj). exact Heq.
Qed.

(** Greedy uses at most K+1 colors (colors in [0..K]). *)
Theorem greedy_uses_at_most_K_plus_1_colors : forall adj K n x,
  back_deg_bounded adj n K -> x < n ->
  greedy_coloring adj K n x <= K.
Proof.
  intros adj K n x Hbound Hin.
  unfold greedy_coloring. apply build_colors_bounded; assumption.
Qed.

(* ========================================================================= *)
(*               PART IX: EXAMPLES                                          *)
(* ========================================================================= *)

(** Empty graph (no edges) has back_degree 0 everywhere. *)
Example empty_graph_back_deg_0 :
  forall n, back_deg_bounded (fun _ _ => false) n 0.
Proof.
  intros n i _.
  unfold back_degree.
  assert (Hf : filter (fun y => (fun _ _ : nat => false) y i) (seq 0 i) = []).
  { induction (seq 0 i) as [|h t IH]; [reflexivity | simpl; exact IH]. }
  rewrite Hf. simpl. lia.
Qed.

(** Empty graph: greedy uses at most 1 color (color 0). *)
Corollary empty_graph_chromatic :
  forall n x,
    x < n ->
    greedy_coloring (fun _ _ => false) 0 n x <= 0.
Proof.
  intros n x Hx.
  apply greedy_uses_at_most_K_plus_1_colors; [|exact Hx].
  apply empty_graph_back_deg_0.
Qed.

(* ========================================================================= *)
(*               PART X: COMMENTARY                                         *)
(* ========================================================================= *)

(**
  THE L5/mu SCHEMA AT WORK:

  Greedy coloring exhibits the canonical L5/mu pattern:
  - Outer recursion: bounded by n (vertex index).
  - Inner search: bounded mu_le over color values [0..K].
  - Both are P4-finitized -- every step terminates in finite time.

  PIGEONHOLE AS WITNESS-EXTRACTOR:

  exists_color_outside_K is pigeonhole in disguise: K+1 colors
  vs. <= K forbidden values ==> at least one allowed. The constructive
  proof uses remove_one to recurse on a strictly smaller list, which
  is itself an L5-style termination argument.

  WHY THIS BOUND IS TIGHT (FOR Delta^-):

  Consider the complete graph K_{K+2} on vertices [0..K+1] with all
  adj. Then back_degree of vertex i is i, so Delta^- = K+1. Greedy uses
  colors 0,1,...,K+1, totaling K+2 colors = Delta^-+1. This matches our
  bound K+1 (where K = Delta^-). So the bound is tight.

  FOR THE CLASSICAL Delta-BOUND:

  Since back_degree(i) <= degree(i) for symmetric graphs, having
  Delta <= K ==> back_deg_bounded n K. So greedy uses <= Delta+1 colors --
  the classical Brooks-style bound's easy direction.

  Brooks' theorem (chi <= Delta EXCEPT for K_n and odd cycles) requires
  more delicate analysis (alternating paths, contractions) and is
  outside this file's scope.

  CONNECTION TO PROJECT'S CENTRAL THESIS:

  H1 (finitization boundary = constructivity boundary):
    Greedy coloring is fully L5/mu-soluble. Every step is a bounded
    mu-search; total termination is by induction on n. This is
    constructive math without ZFC.

  By contrast, the chromatic number chi(G) for INFINITE graphs is
  undecidable (and even uses choice in many cases). The finite case
  is the L5/mu-domain.

  WHAT THIS OPENS NEXT:

  - [GreedyColoringBrooks.v]: full Brooks' theorem.
  - [VizingTheorem.v]: edge coloring (chi' <= Delta+1).
  - [BipartiteColoring.v]: bipartite graphs are 2-colorable (via greedy).
  - [PerfectGraphs.v]: chi = omega for perfect graphs.
  - [PlanarColoring.v]: 6-color theorem for planar (constructive),
    5-color theorem, eventually 4CT via formal proof.
*)
