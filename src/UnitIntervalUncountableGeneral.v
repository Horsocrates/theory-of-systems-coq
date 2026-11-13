(** * UnitIntervalUncountableGeneral.v — [0,1] is not exhausted by ANY enumeration:
      the rate of convergence and its price

    Elements: an enumeration E of processes with values in [0,1]; for every
              member E n, a rate of convergence (a modulus mu n : nat -> nat).
    Roles:    the rate plays one of three roles --
              GIVEN (it is part of the data);
              EXISTING AND UNIQUE (the least rate, fixed by the statement itself);
              EXISTING, ONE AMONG MANY (some rate, taken arbitrarily).
    Rules:    resample every member along its rate (regularize) -> a regular
              enumeration -> the trisection theorem of ShrinkingIntervals_ERR
              -> the apartness found for the resampled member transfers back
              to the original one (not_equiv_transfer).
    P4 diagnostic ("could it be otherwise?"): a given rate is finite data, the
              construction adds nothing.  When only existence is known, the
              LEAST rate is still determined by the statement, so extracting
              it is not a choice; an ARBITRARY rate is one.

    What is proved (assumptions by Print Assumptions):
      unit_interval_uncountable_modulated          -- rate GIVEN: closed
      unit_interval_uncountable_general_definite   -- any Cauchy enumeration,
          from two PREMISES (excluded middle; extraction of the unique
          witness): closed
      unit_interval_uncountable_general            -- any Cauchy enumeration,
          arbitrary rate: L4_witness alone (no classic)
      unit_interval_uncountable_general_L3_L4      -- the instance of the
          *_definite theorem at classic and L4_definite: classic + L4_witness

    The theorem of ShrinkingIntervals_ERR (regular enumerations, rate
    1/m + 1/k) is the special case mu n k = 2k (regular_is_modulated).

    STATUS: 12 Qed, 0 Admitted, no axioms of its own
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith PeanoNat Lqa Wf_nat.
From Stdlib Require Import PArith.Pnat.
From ToS Require Import ToS_Axioms.
From ToS Require Import ShrinkingIntervals_ERR.

Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(* 0. small arithmetic                                                 *)
(* ------------------------------------------------------------------ *)

Lemma inv_nat_small : forall e : Q, 0 < e ->
  exists K : nat, (K > 0)%nat /\ forall m : nat, (m >= K)%nat -> (1 # Pos.of_nat m) <= e.
Proof.
  intros [p q] He.
  assert (Hp : (0 < p)%Z).
  { unfold Qlt in He. simpl in He. lia. }
  exists (Pos.to_nat q). split.
  - apply Pos2Nat.is_pos.
  - intros m Hm.
    assert (Hm0 : (m <> 0)%nat) by (pose proof (Pos2Nat.is_pos q); lia).
    unfold Qle. simpl.
    assert (E1 : Z.pos (Pos.of_nat m) = Z.of_nat m).
    { rewrite <- positive_nat_Z. rewrite Nat2Pos.id by exact Hm0. reflexivity. }
    assert (E2 : Z.pos q = Z.of_nat (Pos.to_nat q)).
    { rewrite positive_nat_Z. reflexivity. }
    rewrite E1.
    assert (Hle : (Z.pos q <= Z.of_nat m)%Z) by (rewrite E2; lia).
    assert (Hmul : (1 * Z.of_nat m <= p * Z.of_nat m)%Z).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    lia.
Qed.

Lemma tri3 : forall x y z w : Q,
  Qabs (x - w) <= Qabs (x - y) + Qabs (y - z) + Qabs (z - w).
Proof.
  intros x y z w.
  setoid_replace (x - w) with ((x - y) + (y - z) + (z - w)) by ring.
  eapply Qle_trans; [apply Qabs_triangle |].
  apply Qplus_le_compat; [apply Qabs_triangle | apply Qle_refl].
Qed.

(* ------------------------------------------------------------------ *)
(* 1. the gap of not_equiv is stable when both processes are Cauchy    *)
(* ------------------------------------------------------------------ *)

(* not_equiv says: the gap is met arbitrarily late.  For Cauchy processes
   this is the same as: from some index on the gap holds at EVERY index. *)
Lemma not_equiv_stable_gap : forall D R : RealProcess,
  is_Cauchy D -> is_Cauchy R -> not_equiv D R ->
  exists eps, eps > 0 /\ exists N, forall m, (m > N)%nat -> Qabs (D m - R m) >= eps.
Proof.
  intros D R HD HR [eps [Heps Hne]].
  assert (He4 : eps * (1 # 4) > 0) by lra.
  destruct (HD (eps * (1 # 4)) He4) as [N1 HN1].
  destruct (HR (eps * (1 # 4)) He4) as [N2 HN2].
  destruct (Hne (Nat.max N1 N2)) as [m0 [Hm0 Hge0]].
  exists (eps * (1 # 2)). split; [lra |].
  exists (Nat.max N1 N2). intros m Hm.
  assert (A : Qabs (D m0 - D m) < eps * (1 # 4)) by (apply HN1; lia).
  assert (B : Qabs (R m - R m0) < eps * (1 # 4)) by (apply HN2; lia).
  pose proof (tri3 (D m0) (D m) (R m) (R m0)) as T.
  set (a := Qabs (D m0 - D m)) in *.
  set (b := Qabs (R m - R m0)) in *.
  set (c := Qabs (D m - R m)) in *.
  set (d := Qabs (D m0 - R m0)) in *.
  lra.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. enumerations with a GIVEN rate of convergence (closed)           *)
(* ------------------------------------------------------------------ *)

(** mu is a rate (modulus) of R: beyond index mu k the values stay within 1/k. *)
Definition modulus_for (R : RealProcess) (mu : nat -> nat) : Prop :=
  forall k a b : nat, (k > 0)%nat -> (a > mu k)%nat -> (b > mu k)%nat ->
    Qabs (R a - R b) <= 1 # Pos.of_nat k.

(** every enumerated process comes with its rate, and lies in [0,1] *)
Definition valid_modulated_enumeration (E : Enumeration) (mu : nat -> nat -> nat) : Prop :=
  forall n, modulus_for (E n) (mu n) /\ (forall m, 0 <= E n m <= 1).

(** resampling along the rate *)
Definition regularize (E : Enumeration) (mu : nat -> nat -> nat) : Enumeration :=
  fun n k => E n (S (mu n k)).

Lemma regularize_regular : forall E mu,
  valid_modulated_enumeration E mu -> valid_regular_enumeration (regularize E mu).
Proof.
  intros E mu H n. destruct (H n) as [Hmod Hb]. split.
  - unfold is_Regular_Cauchy, regularize. intros m k Hm Hk.
    set (t := S (Nat.max (mu n m) (mu n k))).
    assert (H1 : Qabs (E n (S (mu n m)) - E n t) <= 1 # Pos.of_nat m)
      by (apply Hmod; unfold t; lia).
    assert (H2 : Qabs (E n t - E n (S (mu n k))) <= 1 # Pos.of_nat k)
      by (apply Hmod; unfold t; lia).
    setoid_replace (E n (S (mu n m)) - E n (S (mu n k)))
      with ((E n (S (mu n m)) - E n t) + (E n t - E n (S (mu n k)))) by ring.
    eapply Qle_trans; [apply Qabs_triangle |].
    apply Qplus_le_compat; assumption.
  - intro m. unfold regularize. apply Hb.
Qed.

(** a process apart from the resampled one is apart from the original *)
Lemma not_equiv_transfer : forall (D R : RealProcess) (mu : nat -> nat),
  is_Cauchy D -> modulus_for R mu ->
  not_equiv D (fun k => R (S (mu k))) -> not_equiv D R.
Proof.
  intros D R mu HD Hmod [eps [Heps Hne]].
  assert (He4 : eps * (1 # 4) > 0) by lra.
  destruct (HD (eps * (1 # 4)) He4) as [N1 HN1].
  destruct (inv_nat_small (eps * (1 # 4)) He4) as [K [HK0 HK]].
  exists (eps * (1 # 2)). split; [lra |].
  intro N.
  destruct (Hne (Nat.max N (Nat.max N1 K))) as [m [Hm Hge]].
  exists (S (Nat.max m (mu m))). split; [lia |].
  set (m' := S (Nat.max m (mu m))).
  assert (A : Qabs (D m - D m') < eps * (1 # 4)) by (apply HN1; unfold m'; lia).
  assert (B : Qabs (R m' - R (S (mu m))) <= eps * (1 # 4)).
  { apply Qle_trans with (1 # Pos.of_nat m).
    - apply Hmod; unfold m'; lia.
    - apply HK. lia. }
  pose proof (tri3 (D m) (D m') (R m') (R (S (mu m)))) as T.
  cbv beta in Hge.
  set (a := Qabs (D m - D m')) in *.
  set (b := Qabs (R m' - R (S (mu m)))) in *.
  set (c := Qabs (D m' - R m')) in *.
  set (d := Qabs (D m - R (S (mu m)))) in *.
  lra.
Qed.

(** [0,1] is not exhausted by any enumeration whose rates of convergence are given. *)
Theorem unit_interval_uncountable_modulated :
  forall (E : Enumeration) (mu : nat -> nat -> nat),
    valid_modulated_enumeration E mu ->
    exists D : RealProcess,
      is_Cauchy D /\ (forall m, 0 <= D m <= 1) /\ (forall n, not_equiv D (E n)).
Proof.
  intros E mu H.
  destruct (unit_interval_uncountable_trisect_v2 (regularize E mu)
              (regularize_regular E mu H)) as [D [HC [HU HN]]].
  exists D. split; [exact HC |]. split; [exact HU |].
  intro n.
  apply (not_equiv_transfer D (E n) (mu n) HC (proj1 (H n))).
  exact (HN n).
Qed.

(** a regular enumeration is a modulated one: the theorem above contains the
    theorem of ShrinkingIntervals_ERR *)
Lemma regular_is_modulated : forall E,
  valid_regular_enumeration E ->
  valid_modulated_enumeration E (fun _ k => (2 * k)%nat).
Proof.
  intros E H n. destruct (H n) as [Hreg Hb]. split; [| exact Hb].
  intros k a b Hk Ha Hb'.
  assert (Ha0 : (a > 0)%nat) by lia. assert (Hb0 : (b > 0)%nat) by lia.
  eapply Qle_trans; [apply (Hreg a b Ha0 Hb0) |].
  assert (Ia : (1 # Pos.of_nat a) <= 1 # Pos.of_nat (2 * k)).
  { unfold Qle. simpl. apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite !Nat2Pos.id by lia. lia. }
  assert (Ib : (1 # Pos.of_nat b) <= 1 # Pos.of_nat (2 * k)).
  { unfold Qle. simpl. apply Pos2Z.pos_le_pos. apply Pos2Nat.inj_le.
    rewrite !Nat2Pos.id by lia. lia. }
  assert (Hh : (1 # Pos.of_nat (2 * k)) + (1 # Pos.of_nat (2 * k)) == 1 # Pos.of_nat k).
  { replace (Pos.of_nat (2 * k)) with (2 * Pos.of_nat k)%positive.
    - unfold Qeq, Qplus. simpl. lia.
    - rewrite Nat2Pos.inj_mul by lia. reflexivity. }
  rewrite <- Hh. apply Qplus_le_compat; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. arbitrary Cauchy enumerations: the rate has to be extracted      *)
(* ------------------------------------------------------------------ *)

(* the property "N is a rate of E n at precision 1/k" *)
Definition rate_at (E : Enumeration) (n k N : nat) : Prop :=
  forall a b : nat, (a > N)%nat -> (b > N)%nat ->
    Qabs (E n a - E n b) < 1 # Pos.of_nat k.

Lemma rate_exists : forall E, valid_enumeration E ->
  forall n k : nat, exists N : nat, rate_at E n k N.
Proof.
  intros E H n k. destruct (H n) as [HC _].
  unfold rate_at. apply HC. reflexivity.
Qed.

(* 3a. With excluded middle the LEAST rate exists and is unique: extracting
       it is extraction of a unique witness. *)

Lemma least_witness_exists :
  (forall P : Prop, P \/ ~ P) ->
  forall P : nat -> Prop, (exists n, P n) ->
  exists! n, P n /\ forall m, (m < n)%nat -> ~ P m.
Proof.
  intros EM P [n Hn].
  assert (H : forall k, (exists m, (m <= k)%nat /\ P m) ->
                        exists l, P l /\ forall m, (m < l)%nat -> ~ P m).
  { induction k as [k IH] using lt_wf_ind. intros [m [Hmk Hm]].
    destruct (EM (exists m', (m' < m)%nat /\ P m')) as [[m' [Hlt Hm']] | Hno].
    - apply (IH m'); [lia |]. exists m'. split; [lia | exact Hm'].
    - exists m. split; [exact Hm |].
      intros m0 Hm0 HP. apply Hno. exists m0. split; assumption. }
  destruct (H n (ex_intro _ n (conj (le_n n) Hn))) as [l [Hl Hmin]].
  exists l. split; [split; assumption |].
  intros l' [Hl' Hmin'].
  destruct (Nat.lt_trichotomy l l') as [Hlt | [Heq | Hgt]].
  - exfalso. exact (Hmin' l Hlt Hl).
  - exact Heq.
  - exfalso. exact (Hmin l' Hgt Hl').
Qed.

(** [0,1] is not exhausted by ANY enumeration of Cauchy processes -- from
    excluded middle and extraction of the unique witness, taken as premises. *)
Theorem unit_interval_uncountable_general_definite :
  (forall P : Prop, P \/ ~ P) ->
  (forall (T : Type) (P : T -> Prop), (exists! x, P x) -> {x : T | P x}) ->
  forall E : Enumeration,
    valid_enumeration E ->
    exists D : RealProcess,
      is_Cauchy D /\ (forall m, 0 <= D m <= 1) /\ (forall n, not_equiv D (E n)).
Proof.
  intros EM DD E H.
  set (least := fun n k =>
         DD nat _ (least_witness_exists EM (rate_at E n k) (rate_exists E H n k))).
  set (mu := fun n k => proj1_sig (least n k)).
  apply (unit_interval_uncountable_modulated E mu).
  intro n. split.
  - intros k a b Hk Ha Hb. apply Qlt_le_weak.
    exact (proj1 (proj2_sig (least n k)) a b Ha Hb).
  - exact (proj2 (H n)).
Qed.

(** The same under the two logical assumptions of the formalization. *)
Theorem unit_interval_uncountable_general_L3_L4 : forall E : Enumeration,
  valid_enumeration E ->
  exists D : RealProcess,
    is_Cauchy D /\ (forall m, 0 <= D m <= 1) /\ (forall n, not_equiv D (E n)).
Proof.
  exact (unit_interval_uncountable_general_definite classic (@L4_definite)).
Qed.

(* 3b. Without excluded middle: SOME rate, taken arbitrarily -- L4_witness in
       its full strength, and nothing else. *)

Theorem unit_interval_uncountable_general : forall E : Enumeration,
  valid_enumeration E ->
  exists D : RealProcess,
    is_Cauchy D /\ (forall m, 0 <= D m <= 1) /\ (forall n, not_equiv D (E n)).
Proof.
  intros E H.
  set (some := fun n k => @L4_witness nat _ (rate_exists E H n k)).
  set (mu := fun n k => proj1_sig (some n k)).
  apply (unit_interval_uncountable_modulated E mu).
  intro n. split.
  - intros k a b Hk Ha Hb. apply Qlt_le_weak.
    exact (proj2_sig (some n k) a b Ha Hb).
  - exact (proj2 (H n)).
Qed.

(* Axiom audit (expected output in comments). *)
Print Assumptions unit_interval_uncountable_modulated.        (* Closed under the global context *)
Print Assumptions regular_is_modulated.                       (* Closed under the global context *)
Print Assumptions unit_interval_uncountable_general_definite. (* Closed under the global context *)
Print Assumptions unit_interval_uncountable_general_L3_L4.    (* classic + L4_witness *)
Print Assumptions unit_interval_uncountable_general.          (* L4_witness *)
