(** * ProcessTopConnected.v — Path-Connectedness via Linear Interpolation
    Elements: path parameter t ∈ [0,1] ∩ Q, linear interpolation
    Roles:    path as process, connectedness as reachability
    Rules:    linear path stays in interval, Lipschitz continuity
    Status:   complete
    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS TOPOLOGY CONNECTED — Path-Connectedness over Q            *)
(*                                                                           *)
(*  Q is totally disconnected (topologically).                              *)
(*  But Q IS path-connected via rational linear interpolation:              *)
(*    gamma(t) = a + t * (b - a)  for t ∈ [0,1] ∩ Q                       *)
(*  This is the correct notion under P4.                                    *)
(*                                                                           *)
(*  STATUS: 21 Qed, 0 Admitted                                              *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs QArith.Qround Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.

(* ================================================================== *)
(*  Part I: Linear Path  (~7 lemmas)                                   *)
(* ================================================================== *)

(** Linear interpolation from a to b *)
Definition linear_path (a b t : Q) : Q := a + t * (b - a).

(** At t=0, path is at a *)
Lemma linear_path_at_0 : forall a b,
  linear_path a b 0 == a.
Proof. intros a b. unfold linear_path. lra. Qed.

(** At t=1, path is at b *)
Lemma linear_path_at_1 : forall a b,
  linear_path a b 1 == b.
Proof. intros a b. unfold linear_path. lra. Qed.

(** Linear path stays in [a,b] when 0 <= t <= 1 and a <= b *)
Lemma linear_path_in_interval : forall a b t,
  a <= b -> 0 <= t -> t <= 1 ->
  a <= linear_path a b t /\ linear_path a b t <= b.
Proof.
  intros a b t Hab Ht0 Ht1. unfold linear_path. split.
  - assert (H : 0 <= t * (b - a)) by (apply Qmult_le_0_compat; lra). lra.
  - assert (H : t * (b - a) <= 1 * (b - a)) by (apply Qmult_le_compat_r; lra). lra.
Qed.

(** Linear path is Lipschitz in t *)
Lemma linear_path_lipschitz : forall a b s t,
  Qabs (linear_path a b s - linear_path a b t) == Qabs (b - a) * Qabs (s - t).
Proof.
  intros a b s t. unfold linear_path.
  assert (Heq : a + s * (b - a) - (a + t * (b - a)) == (b - a) * (s - t)) by lra.
  rewrite Heq.
  destruct (Qlt_le_dec (b - a) 0) as [Hn | Hp].
  - destruct (Qlt_le_dec (s - t) 0) as [Hn2 | Hp2].
    + rewrite (Qabs_neg (b - a)); [| lra].
      rewrite (Qabs_neg (s - t)); [| lra].
      assert (Hprod : (b - a) * (s - t) == (-(b-a)) * (-(s-t))) by lra.
      rewrite Hprod. rewrite Qabs_pos; [lra |]. apply Qmult_le_0_compat; lra.
    + rewrite (Qabs_neg (b - a)); [| lra].
      rewrite (Qabs_pos (s - t)); [| lra].
      assert (Hprod : (b - a) * (s - t) <= 0).
      { assert (H : 0 <= (-(b-a)) * (s - t)) by (apply Qmult_le_0_compat; lra). lra. }
      rewrite (Qabs_neg ((b-a)*(s-t))); [| lra]. lra.
  - destruct (Qlt_le_dec (s - t) 0) as [Hn2 | Hp2].
    + rewrite (Qabs_pos (b - a)); [| lra].
      rewrite (Qabs_neg (s - t)); [| lra].
      assert (Hprod : (b - a) * (s - t) <= 0).
      { assert (H : 0 <= (b - a) * (-(s-t))) by (apply Qmult_le_0_compat; lra). lra. }
      rewrite (Qabs_neg ((b-a)*(s-t))); [| lra]. lra.
    + rewrite (Qabs_pos (b - a)); [| lra].
      rewrite (Qabs_pos (s - t)); [| lra].
      rewrite (Qabs_pos ((b-a)*(s-t))); [| apply Qmult_le_0_compat; lra]. lra.
Qed.

(** Constant path *)
Lemma const_path : forall a t, linear_path a a t == a.
Proof. intros a t. unfold linear_path. lra. Qed.

(** Reverse path: swap a and b, use 1-t *)
Lemma reverse_path : forall a b t,
  linear_path b a t == linear_path a b (1 - t).
Proof. intros a b t. unfold linear_path. lra. Qed.

(* ================================================================== *)
(*  Part II: Path-Connectedness  (~7 lemmas)                           *)
(* ================================================================== *)

(** A path in S from a to b *)
Definition PathIn (S : Q -> Prop) (gamma : Q -> Q) (a b : Q) : Prop :=
  gamma 0 == a /\
  gamma 1 == b /\
  forall t, 0 <= t -> t <= 1 -> S (gamma t).

(** S is path-connected if any two points are linked by a path in S *)
Definition is_path_connected (S : Q -> Prop) : Prop :=
  forall a b, S a -> S b ->
    exists gamma, PathIn S gamma a b.

(** Open interval is path-connected *)
Theorem interval_path_connected : forall lo hi,
  lo < hi -> is_path_connected (fun x => lo <= x /\ x <= hi).
Proof.
  intros lo hi Hlt a b [Halo Hahi] [Hblo Hbhi].
  exists (linear_path a b). unfold PathIn. split; [| split].
  - apply linear_path_at_0.
  - apply linear_path_at_1.
  - intros t Ht0 Ht1.
    destruct (Qlt_le_dec a b) as [Hab | Hab].
    + destruct (linear_path_in_interval a b t ltac:(lra) Ht0 Ht1) as [H1 H2].
      split; lra.
    + (* b <= a case *)
      unfold linear_path.
      assert (Hba : b - a <= 0) by lra.
      assert (H1 : 0 <= t * (-(b-a))) by (apply Qmult_le_0_compat; lra).
      assert (H2 : t * (b - a) <= 0) by lra.
      assert (H3 : 0 <= (1-t) * (-(b-a))) by (apply Qmult_le_0_compat; lra).
      assert (H4 : 1 * (b - a) <= t * (b - a)) by lra.
      split; lra.
Qed.

(** Q-density in interval *)
Lemma q_dense_in_interval : forall a b : Q,
  a < b -> exists q : Q, a < q /\ q < b.
Proof.
  intros a b Hab. exists ((a + b) * (1#2)). split; lra.
Qed.

(** Path-connected set is nonempty if it contains a point *)
Lemma path_connected_nonempty : forall S a,
  is_path_connected S -> S a ->
  forall b, S b -> exists gamma, PathIn S gamma a b.
Proof. intros S a Hpc Ha b Hb. exact (Hpc a b Ha Hb). Qed.

(** Linear path for the full rational line *)
Lemma full_Q_path_connected : is_path_connected (fun _ => True).
Proof.
  intros a b _ _. exists (linear_path a b).
  unfold PathIn. split; [| split].
  - apply linear_path_at_0.
  - apply linear_path_at_1.
  - intros _ _ _. exact I.
Qed.

(** Concatenation: paths can be joined *)
Lemma concat_paths : forall S gamma1 gamma2 a b c,
  PathIn S gamma1 a b ->
  PathIn S gamma2 b c ->
  exists gamma, PathIn S gamma a c.
Proof.
  intros S gamma1 gamma2 a b c [Hg10 [Hg11 Hg1in]] [Hg20 [Hg21 Hg2in]].
  exists (fun t => if Qlt_le_dec t (1#2) then gamma1 (2 * t) else gamma2 (2 * t - 1)).
  unfold PathIn. split; [| split].
  - destruct (Qlt_le_dec 0 (1#2)) as [H | H]; [| lra].
    change (2 * 0)%Q with 0%Q. exact Hg10.
  - destruct (Qlt_le_dec 1 (1#2)) as [H | H]; [lra |].
    change (2 * 1 - 1)%Q with 1%Q. exact Hg21.
  - intros t Ht0 Ht1.
    destruct (Qlt_le_dec t (1#2)) as [Hlt | Hge].
    + apply Hg1in; lra.
    + apply Hg2in; lra.
Qed.

(* ================================================================== *)
(*  Part III: Process Path  (~6 lemmas)                                *)
(* ================================================================== *)

(** Process walking from a toward b: at step n, parameter t = n/(n+1) *)
Definition process_path (a b : Q) : RealProcess :=
  fun n => linear_path a b (inject_Z (Z.of_nat n) * / (inject_Z (Z.of_nat n) + 1)).

(** Process path at step 0 *)
Lemma process_path_at_0 : forall a b,
  process_path a b 0%nat == a.
Proof.
  intros a b. unfold process_path.
  change (inject_Z (Z.of_nat 0)) with 0.
  unfold linear_path. lra.
Qed.

(** Helper: n/(n+1) is in [0,1] for natural n *)
Lemma nat_frac_in_01 : forall n : nat,
  0 <= inject_Z (Z.of_nat n) * / (inject_Z (Z.of_nat n) + 1) /\
  inject_Z (Z.of_nat n) * / (inject_Z (Z.of_nat n) + 1) <= 1.
Proof.
  intros n.
  assert (Hn : 0 <= inject_Z (Z.of_nat n)) by (unfold Qle; simpl; lia).
  assert (Hn1 : 0 < inject_Z (Z.of_nat n) + 1) by (unfold Qlt; simpl; lia).
  split.
  - apply Qle_shift_div_l; [exact Hn1 |]. lra.
  - apply Qle_shift_div_r; [exact Hn1 |]. lra.
Qed.

(** Process path stays in [a,b] when a <= b *)
Lemma process_path_in_interval : forall a b n,
  a <= b -> a <= process_path a b n /\ process_path a b n <= b.
Proof.
  intros a b n Hab. unfold process_path.
  apply linear_path_in_interval; [exact Hab | |];
  apply (nat_frac_in_01 n).
Qed.

(** Helper: Qceiling bound for Archimedean witness *)
Lemma archimedean_witness : forall (D eps : Q),
  0 < D -> 0 < eps ->
  exists N : nat, forall k : nat, (N <= k)%nat ->
    D * / (inject_Z (Z.of_nat k) + 1) < eps.
Proof.
  intros D eps HD Heps.
  set (bv := D * / eps + 1).
  assert (Hbv : 0 < bv).
  { unfold bv. assert (Hnn := Qabs_nonneg (0 : Q)).
    assert (H0 : 0 <= D * / eps).
    { apply Qle_shift_div_l; [exact Heps |]. lra. }
    lra. }
  assert (Hceil_nn : (0 <= Qceiling bv)%Z).
  { assert (Hc := Qle_ceiling bv).
    assert (Hle : 0 <= inject_Z (Qceiling bv)) by lra.
    unfold Qle in Hle. simpl in Hle. lia. }
  exists (S (Z.to_nat (Qceiling bv))).
  intros k Hk.
  assert (Hk1 : 0 < inject_Z (Z.of_nat k) + 1) by (unfold Qlt; simpl; lia).
  apply Qlt_shift_div_r; [exact Hk1 |].
  (* D < eps * (k+1) because k >= S(to_nat(ceil(bv))) > D/eps *)
  assert (Hceil : bv <= inject_Z (Qceiling bv)) by apply Qle_ceiling.
  assert (Hto : inject_Z (Z.of_nat (Z.to_nat (Qceiling bv))) == inject_Z (Qceiling bv)).
  { unfold Qeq. simpl. rewrite Z2Nat.id; [lia | exact Hceil_nn]. }
  assert (HkN : inject_Z (Z.of_nat (S (Z.to_nat (Qceiling bv)))) <= inject_Z (Z.of_nat k)).
  { unfold Qle. simpl. lia. }
  assert (Hge : bv < inject_Z (Z.of_nat k) + 1).
  { assert (Hstep : inject_Z (Z.of_nat (S (Z.to_nat (Qceiling bv)))) ==
                     inject_Z (Z.of_nat (Z.to_nat (Qceiling bv))) + 1).
    { unfold Qeq. simpl. lia. }
    rewrite Hto in Hstep. lra. }
  unfold bv in Hge.
  (* D/eps + 1 < k+1, so D/eps < k, so D < eps * k <= eps * (k+1) *)
  assert (Hdiveps : D * / eps < inject_Z (Z.of_nat k)) by lra.
  (* D < eps * k: multiply both sides by eps *)
  assert (Hgoal : D < eps * (inject_Z (Z.of_nat k) + 1)).
  { assert (Hde : D * / eps * eps < inject_Z (Z.of_nat k) * eps).
    { apply Qmult_lt_compat_r; [exact Heps | exact Hdiveps]. }
    assert (Hde2 : D * / eps * eps == D) by (field; lra).
    lra. }
  exact Hgoal.
Qed.

(** Process path is Cauchy (converges to b) *)
Lemma process_path_cauchy : forall a b,
  is_Cauchy (process_path a b).
Proof.
  intros a b eps Heps.
  destruct (Qeq_dec a b) as [Hab | Hab].
  - (* a == b: path is constant *)
    exists 0%nat. intros m n _ _.
    unfold process_path, linear_path.
    assert (H : b - a == 0) by lra.
    assert (Hd : a + inject_Z (Z.of_nat m) * / (inject_Z (Z.of_nat m) + 1) * (b - a) -
                 (a + inject_Z (Z.of_nat n) * / (inject_Z (Z.of_nat n) + 1) * (b - a)) == 0)
      by (rewrite H; lra).
    rewrite Hd. rewrite Qabs_pos; lra.
  - (* a ≠ b: use Archimedean witness *)
    assert (Habs_pos : 0 < Qabs (a - b)).
    { destruct (Qlt_le_dec (a - b) 0); [rewrite Qabs_neg | rewrite Qabs_pos]; lra. }
    destruct (archimedean_witness (Qabs (a - b)) (eps * (1#2)) Habs_pos ltac:(lra))
      as [N HN].
    exists N. intros m n Hm Hn.
    assert (Hm1 : 0 < inject_Z (Z.of_nat m) + 1) by (unfold Qlt; simpl; lia).
    assert (Hn1 : 0 < inject_Z (Z.of_nat n) + 1) by (unfold Qlt; simpl; lia).
    assert (Hinvm : 0 < / (inject_Z (Z.of_nat m) + 1)) by (apply Qinv_lt_0_compat; exact Hm1).
    assert (Hinvn : 0 < / (inject_Z (Z.of_nat n) + 1)) by (apply Qinv_lt_0_compat; exact Hn1).
    (* path(k) - b = (a-b)/(k+1) *)
    assert (Hdm : process_path a b m - b == (a - b) * / (inject_Z (Z.of_nat m) + 1)).
    { unfold process_path, linear_path. field. lra. }
    assert (Hdn : process_path a b n - b == (a - b) * / (inject_Z (Z.of_nat n) + 1)).
    { unfold process_path, linear_path. field. lra. }
    (* |path(m) - b| = |a-b|/(m+1) *)
    assert (Habsm : Qabs (process_path a b m - b) == Qabs (a - b) * / (inject_Z (Z.of_nat m) + 1)).
    { setoid_rewrite Hdm. rewrite Qabs_Qmult.
      rewrite (Qabs_pos (/ (inject_Z (Z.of_nat m) + 1))); lra. }
    assert (Habsn : Qabs (process_path a b n - b) == Qabs (a - b) * / (inject_Z (Z.of_nat n) + 1)).
    { setoid_rewrite Hdn. rewrite Qabs_Qmult.
      rewrite (Qabs_pos (/ (inject_Z (Z.of_nat n) + 1))); lra. }
    (* Triangle: |path(m) - path(n)| <= |path(m) - b| + |b - path(n)| *)
    assert (Htri := Qabs_triangle (process_path a b m - b) (b - process_path a b n)).
    assert (Hsimp : process_path a b m - b + (b - process_path a b n) ==
                    process_path a b m - process_path a b n) by lra.
    assert (Hle : Qabs (process_path a b m - process_path a b n) <=
                  Qabs (process_path a b m - b) + Qabs (b - process_path a b n)).
    { assert (Htri2 : Qabs (process_path a b m - process_path a b n) <=
                       Qabs (process_path a b m - b) + Qabs (b - process_path a b n)).
      { setoid_rewrite <- Hsimp. exact Htri. }
      exact Htri2. }
    (* |b - path(n)| = |path(n) - b| *)
    assert (Hsym : Qabs (b - process_path a b n) == Qabs (process_path a b n - b)).
    { assert (Heq : b - process_path a b n == -(process_path a b n - b)) by lra.
      setoid_rewrite Heq.
      destruct (Qlt_le_dec (process_path a b n - b) 0).
      - rewrite (Qabs_pos (-(process_path a b n - b))); [| lra].
        rewrite (Qabs_neg (process_path a b n - b)); lra.
      - rewrite (Qabs_neg (-(process_path a b n - b))); [| lra].
        rewrite (Qabs_pos (process_path a b n - b)); lra. }
    (* Each term < eps/2 *)
    assert (Hm_half := HN m Hm).
    assert (Hn_half := HN n Hn).
    lra.
Qed.

(* ================================================================== *)
(*  Part VI: what the path notion really says (Nov 2026)                *)
(* ================================================================== *)

(** Without any continuity requirement [is_path_connected] holds for EVERY
    set: the path may jump from a to b at the last parameter value.  So
    [interval_path_connected] says nothing about the interval; the content
    is in the Lipschitz notion below. *)
Lemma any_set_path_connected : forall S : Q -> Prop, is_path_connected S.
Proof.
  intros S a b Ha Hb.
  exists (fun t => if Qlt_le_dec t 1 then a else b).
  unfold PathIn. split; [| split].
  - destruct (Qlt_le_dec 0 1) as [H | H]; [reflexivity | lra].
  - destruct (Qlt_le_dec 1 1) as [H | H]; [lra | reflexivity].
  - intros t _ _. destruct (Qlt_le_dec t 1); assumption.
Qed.

(** A path with a Lipschitz parametrization. *)
Definition LipPathIn (S : Q -> Prop) (gamma : Q -> Q) (a b : Q) : Prop :=
  PathIn S gamma a b /\
  exists K : Q, 0 <= K /\ forall s t : Q, Qabs (gamma s - gamma t) <= K * Qabs (s - t).

Definition is_lip_path_connected (S : Q -> Prop) : Prop :=
  forall a b, S a -> S b -> exists gamma, LipPathIn S gamma a b.

(** The interval is connected by Lipschitz paths (the linear one). *)
Theorem interval_lip_path_connected : forall lo hi,
  lo < hi -> is_lip_path_connected (fun x => lo <= x /\ x <= hi).
Proof.
  intros lo hi Hlt a b Ha Hb.
  exists (linear_path a b). split.
  - unfold PathIn. split; [apply linear_path_at_0 | split; [apply linear_path_at_1 |]].
    intros t Ht0 Ht1. destruct Ha as [Halo Hahi]. destruct Hb as [Hblo Hbhi].
    destruct (Qlt_le_dec a b) as [Hab | Hab].
    + destruct (linear_path_in_interval a b t ltac:(lra) Ht0 Ht1) as [H1 H2]. split; lra.
    + unfold linear_path.
      assert (H1 : 0 <= t * (-(b-a))) by (apply Qmult_le_0_compat; lra).
      assert (H3 : 0 <= (1-t) * (-(b-a))) by (apply Qmult_le_0_compat; lra).
      split; lra.
  - exists (Qabs (b - a)). split; [apply Qabs_nonneg|].
    intros s t. rewrite linear_path_lipschitz. apply Qle_refl.
Qed.

(** A Lipschitz path with values in {0, 1} cannot leave 0: on a grid finer
    than 1/K neighbouring values differ by less than 1. *)
Lemma lip_no_jump : forall (g : Q -> Q) (K : Q) (n : nat),
  0 <= K -> K < inject_Z (Z.of_nat (S n)) ->
  (forall s t : Q, Qabs (g s - g t) <= K * Qabs (s - t)) ->
  (forall t, 0 <= t -> t <= 1 -> g t == 0 \/ g t == 1) ->
  g 0 == 0 ->
  forall k : nat, (k <= S n)%nat ->
    g (inject_Z (Z.of_nat k) / inject_Z (Z.of_nat (S n))) == 0.
Proof.
  intros g K n HK HKn Hlip Hval H0 k.
  assert (HN : 0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia).
  induction k as [|k IH]; intro Hk.
  - assert (E : inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n)) == 0).
    { unfold Qdiv. change (inject_Z (Z.of_nat 0)) with 0. ring. }
    pose proof (Hlip (inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n))) 0) as HL.
    assert (E2 : inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n)) - 0 == 0) by (rewrite E; ring).
    rewrite (Qabs_wd _ _ E2) in HL. simpl (Qabs 0) in HL.
    assert (HL2 : Qabs (g (inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n))) - g 0) <= 0) by lra.
    pose proof (Qabs_nonneg (g (inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n))) - g 0)) as Hnn.
    pose proof (Qle_Qabs (g (inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n))) - g 0)) as Hle.
    pose proof (Qle_Qabs (- (g (inject_Z (Z.of_nat 0) / inject_Z (Z.of_nat (S n))) - g 0))) as Hle2.
    rewrite Qabs_opp in Hle2. lra.
  - assert (IH' := IH ltac:(lia)).
    set (tk := inject_Z (Z.of_nat k) / inject_Z (Z.of_nat (S n))) in *.
    set (tk1 := inject_Z (Z.of_nat (S k)) / inject_Z (Z.of_nat (S n))).
    assert (Hstep : tk1 - tk == 1 / inject_Z (Z.of_nat (S n))).
    { unfold tk1, tk. rewrite (Nat2Z.inj_succ k).
      assert (Es : inject_Z (Z.succ (Z.of_nat k)) == inject_Z (Z.of_nat k) + 1).
      { unfold Z.succ. rewrite inject_Z_plus. reflexivity. }
      rewrite Es. field. lra. }
    assert (Hpos : 0 < 1 / inject_Z (Z.of_nat (S n))).
    { apply Qlt_shift_div_l; [exact HN | lra]. }
    assert (Htk1_0 : 0 <= tk1).
    { unfold tk1. apply Qle_shift_div_l; [exact HN|].
      assert (0 <= inject_Z (Z.of_nat (S k))) by (unfold Qle; simpl; lia). lra. }
    assert (Htk1_1 : tk1 <= 1).
    { unfold tk1. apply Qle_shift_div_r; [exact HN|].
      assert (inject_Z (Z.of_nat (S k)) <= inject_Z (Z.of_nat (S n))).
      { rewrite <- Zle_Qle. lia. }
      lra. }
    destruct (Hval tk1 Htk1_0 Htk1_1) as [Hz | Ho]; [exact Hz | exfalso].
    pose proof (Hlip tk1 tk) as HL.
    rewrite (Qabs_wd _ _ Hstep) in HL.
    rewrite (Qabs_pos (1 / inject_Z (Z.of_nat (S n)))) in HL by lra.
    assert (Ed : g tk1 - g tk == 1) by (rewrite Ho, IH'; ring).
    rewrite (Qabs_wd _ _ Ed) in HL. simpl (Qabs 1) in HL.
    assert (Hlt : K * (1 / inject_Z (Z.of_nat (S n))) < 1).
    { assert (E : K * (1 / inject_Z (Z.of_nat (S n))) == K / inject_Z (Z.of_nat (S n))) by (field; lra).
      rewrite E. apply Qlt_shift_div_r; [exact HN | lra]. }
    lra.
Qed.

(** The two-point set {0, 1} is NOT connected by Lipschitz paths: the
    Lipschitz notion tells an interval from a pair of points. *)
Theorem two_points_not_lip_path_connected :
  ~ is_lip_path_connected (fun x => x == 0 \/ x == 1).
Proof.
  intro H.
  destruct (H 0 1 (or_introl (Qeq_refl 0)) (or_intror (Qeq_refl 1))) as [g [[Hg0 [Hg1 Hin]] [K [HK Hlip]]]].
  destruct (Qarchimedean K) as [p Hp].
  set (n := Pos.to_nat p).
  assert (HKn : K < inject_Z (Z.of_nat (S n))).
  { apply Qlt_le_trans with (inject_Z (Z.pos p)); [exact Hp|].
    rewrite <- Zle_Qle. unfold n. lia. }
  pose proof (lip_no_jump g K n HK HKn Hlip Hin Hg0 (S n) (le_n _)) as Hend.
  assert (HN : 0 < inject_Z (Z.of_nat (S n))) by (unfold Qlt; simpl; lia).
  assert (E1 : inject_Z (Z.of_nat (S n)) / inject_Z (Z.of_nat (S n)) - 1 == 0) by (field; lra).
  pose proof (Hlip (inject_Z (Z.of_nat (S n)) / inject_Z (Z.of_nat (S n))) 1) as HL.
  rewrite (Qabs_wd _ _ E1) in HL. simpl (Qabs 0) in HL.
  assert (Ed : g (inject_Z (Z.of_nat (S n)) / inject_Z (Z.of_nat (S n))) - g 1 == -1)
    by (rewrite Hend, Hg1; ring).
  rewrite (Qabs_wd _ _ Ed) in HL. simpl (Qabs (-1)) in HL. lra.
Qed.

(** The process of the path converges to b (until Nov 2026 only its Cauchy
    property was stated; the limit stood in a comment). *)
Lemma process_path_converges : forall a b eps, 0 < eps ->
  exists N : nat, forall n : nat, (N <= n)%nat -> Qabs (process_path a b n - b) < eps.
Proof.
  intros a b eps Heps.
  destruct (Qeq_dec a b) as [Hab | Hab].
  - exists 0%nat. intros n _.
    assert (E : process_path a b n - b == 0).
    { unfold process_path, linear_path. rewrite Hab. ring. }
    rewrite (Qabs_wd _ _ E). simpl. exact Heps.
  - assert (Habs_pos : 0 < Qabs (a - b)).
    { destruct (Qlt_le_dec (a - b) 0); [rewrite Qabs_neg | rewrite Qabs_pos]; lra. }
    destruct (archimedean_witness (Qabs (a - b)) eps Habs_pos Heps) as [N HN].
    exists N. intros n Hn.
    assert (Hn1 : 0 < inject_Z (Z.of_nat n) + 1) by (unfold Qlt; simpl; lia).
    assert (Hinv : 0 < / (inject_Z (Z.of_nat n) + 1)) by (apply Qinv_lt_0_compat; exact Hn1).
    assert (Hd : process_path a b n - b == (a - b) * / (inject_Z (Z.of_nat n) + 1)).
    { unfold process_path, linear_path. field. lra. }
    rewrite (Qabs_wd _ _ Hd). rewrite Qabs_Qmult.
    rewrite (Qabs_pos (/ (inject_Z (Z.of_nat n) + 1))) by lra.
    exact (HN n Hn).
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check linear_path. Check linear_path_at_0. Check linear_path_at_1.
Check linear_path_in_interval. Check linear_path_lipschitz.
Check const_path. Check reverse_path.
Check PathIn. Check is_path_connected.
Check interval_path_connected. Check q_dense_in_interval.
Check path_connected_nonempty. Check full_Q_path_connected. Check concat_paths.
Check process_path. Check process_path_at_0.
Check nat_frac_in_01. Check process_path_in_interval.
Check archimedean_witness. Check process_path_cauchy.
