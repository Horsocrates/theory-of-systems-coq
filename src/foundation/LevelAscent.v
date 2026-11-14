(** * LevelAscent.v — The hierarchical path: the depth of a level counts from
      one, LS gives the NEXT level, there is no top, and every hierarchy
      is numbered the same way

    E/R/R reading (done before coding; audit of Part II of the Mathematics
    volume, chapter II.3, places 3.1-3.5, 2026-11-13):

    Elements: levels — the values of the type Level (L1, LS l) of
              TheoryOfSystems_Core_ERR.v.
    Roles:    the depth of a level — its number, counted from one; the base
              L1 — the first level; LS l — the next level over l.
    Rules:    every level is the base or is built over a level; LS adds
              exactly one to the depth; the order << is the order of depths.
    Proved:   (1) the step lemma of the chapter: the depth of LS l is the
                  depth of l plus one;
              (2) the depth is a one-to-one correspondence between the
                  levels and the POSITIVE numbers; it carries L1 to 1, LS to
                  S and << to <;
              (3) descent: every level is the base or lies above the base;
                  every level is the base with LS applied (depth - 1) times;
                  there is no infinite descending sequence of levels;
              (4) ascent: LS l is the NEXT level over l — it is above l, and
                  every level above l is LS l or lies above LS l; nothing
                  lies strictly between; there is no top level;
              (5) every hierarchy: a structure with a base and a step, where
                  the step is injective, the base is not a value of the step
                  and induction holds, is numbered by the levels one-to-one,
                  the base by L1 and the step by LS — hence by the depths
                  counted from one;
              (6) induction over the levels and induction over nat are
                  carried into each other by the isomorphism.
    P4 diagnostic ("could it be otherwise?"): every statement is about
              finite levels. Forced: (1)-(6). NOT claimed: that the
              hierarchy of levels is derived from the law L5 — the type
              Level is an inductive declaration; that counting from one is
              forced against counting from zero — level_depth (from 1) and
              LevelNatIso.level_to_nat (from 0) are two definitions on the
              same type and differ by one (LevelNatIso.level_depth_eq); that
              the transfer of (6) gives induction over the levels
              independently of Level_ind — the round-trip lemma it uses is
              itself proved by induction on the level.

    STATUS: 26 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: November 2026
*)

From Stdlib Require Import Arith Lia.

From ToS Require Import TheoryOfSystems_Core_ERR.
(* Require WITHOUT Import: several of these files declare the same names. *)
From ToS Require UniversePolymorphism.
From ToS Require foundation.LevelNatIso.
From ToS Require foundation.MetaPairStrength.
From ToS Require foundation.TransfiniteInductionLevel.

(* ========================================================================= *)
(*  1. THE DEPTH COUNTS FROM ONE                                             *)
(* ========================================================================= *)

(** The step lemma, as it stands on the page of the chapter (section 3.4). *)
Lemma level_depth_LS : forall l,
  level_depth (LS l) = S (level_depth l).
Proof. reflexivity. Qed.

Lemma level_depth_ge_one : forall l : Level, 1 <= level_depth l.
Proof. intro l. rewrite LevelNatIso.level_depth_eq. lia. Qed.

(** The level of a given depth: the inverse of level_depth on the positive
    numbers. *)
Definition level_of_depth (n : nat) : Level := LevelNatIso.nat_to_level (pred n).

Lemma level_of_depth_depth : forall l, level_of_depth (level_depth l) = l.
Proof.
  intro l. unfold level_of_depth. rewrite LevelNatIso.level_depth_eq. simpl.
  apply LevelNatIso.level_nat_level.
Qed.

Lemma depth_level_of_depth : forall n, 1 <= n -> level_depth (level_of_depth n) = n.
Proof.
  intros n Hn. unfold level_of_depth. rewrite LevelNatIso.level_depth_eq.
  rewrite LevelNatIso.nat_level_nat. lia.
Qed.

Lemma level_of_depth_one : level_of_depth 1 = L1.
Proof. reflexivity. Qed.

Lemma level_of_depth_succ : forall n, 1 <= n ->
  level_of_depth (S n) = LS (level_of_depth n).
Proof.
  intros n Hn. unfold level_of_depth. destruct n as [| k]; [lia | reflexivity].
Qed.

(** The order of the levels is the order of their depths — in both
    directions. *)
Lemma level_lt_iff_depth_lt : forall l1 l2,
  l1 << l2 <-> level_depth l1 < level_depth l2.
Proof.
  intros l1 l2. rewrite (LevelNatIso.level_lt_iff_nat_lt l1 l2).
  rewrite !LevelNatIso.level_depth_eq. lia.
Qed.

(** The left column of the table of the chapter in one statement: the levels
    and the positive numbers are one arrangement "a base and a step",
    counted from one. *)
Theorem level_depth_counts_from_one :
  (forall l, 1 <= level_depth l)
  /\ (forall l, level_of_depth (level_depth l) = l)
  /\ (forall n, 1 <= n -> level_depth (level_of_depth n) = n)
  /\ level_depth L1 = 1
  /\ (forall l, level_depth (LS l) = S (level_depth l))
  /\ (forall l1 l2, l1 << l2 <-> level_depth l1 < level_depth l2).
Proof.
  split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - exact level_depth_ge_one.
  - exact level_of_depth_depth.
  - exact depth_level_of_depth.
  - reflexivity.
  - exact level_depth_LS.
  - exact level_lt_iff_depth_lt.
Qed.

(** Every positive number is the depth of exactly one level. *)
Theorem positive_number_is_depth_of_one_level : forall n,
  1 <= n -> exists l : Level, level_depth l = n /\
                              forall l', level_depth l' = n -> l' = l.
Proof.
  intros n Hn. exists (level_of_depth n). split.
  - exact (depth_level_of_depth n Hn).
  - intros l' H. rewrite <- H. symmetry. apply level_of_depth_depth.
Qed.

(** Zero is not a depth: the base is a level that is present. *)
Theorem zero_is_not_a_depth : forall l : Level, level_depth l <> 0.
Proof. intro l. pose proof (level_depth_ge_one l). lia. Qed.

(* ========================================================================= *)
(*  2. DESCENT: FINITE FROM BELOW                                            *)
(* ========================================================================= *)

(** Every level is the base or lies above the base. *)
Lemma base_below_every_other_level : forall l : Level, l = L1 \/ L1 << l.
Proof.
  induction l as [| l' IH].
  - left. reflexivity.
  - right. destruct IH as [E | Lt].
    + subst. simpl. left. reflexivity.
    + simpl. right. exact Lt.
Qed.

(** Every level is the base with LS applied finitely many times, and the
    number of applications is the depth minus one. *)
Lemma level_is_iterated_LS : forall l : Level,
  l = Nat.iter (pred (level_depth l)) LS L1.
Proof.
  induction l as [| l' IH].
  - reflexivity.
  - rewrite level_depth_LS. simpl.
    pose proof (level_depth_ge_one l') as Hge.
    destruct (level_depth l') as [| k] eqn:E; [lia | ].
    simpl in IH. simpl. f_equal. exact IH.
Qed.

(** The general statement in the words of the chapter: there is no function
    f : nat -> Level with f (n+1) << f n for all n. (The theorem itself is
    MetaPairStrength.no_infinite_level_regress.) *)
Theorem no_descending_sequence_of_levels :
  ~ exists f : nat -> Level, forall n, f (S n) << f n.
Proof.
  intros [f Hf]. exact (MetaPairStrength.no_infinite_level_regress f Hf).
Qed.

(** Finite from below, in one statement. *)
Theorem hierarchy_is_finite_from_below :
  (forall l : Level, ~ (l << L1))
  /\ (forall l : Level, l = L1 \/ L1 << l)
  /\ (forall l : Level, l = Nat.iter (pred (level_depth l)) LS L1)
  /\ ~ (exists f : nat -> Level, forall n, f (S n) << f n).
Proof.
  split; [exact UniversePolymorphism.L1_minimal | split; [ | split]].
  - exact base_below_every_other_level.
  - exact level_is_iterated_LS.
  - exact no_descending_sequence_of_levels.
Qed.

(* ========================================================================= *)
(*  3. ASCENT: LS GIVES THE NEXT LEVEL; NO TOP                               *)
(* ========================================================================= *)

(** LS l is the NEXT level over l: a level lies above l exactly when it is
    LS l or lies above LS l. *)
Theorem LS_is_next_level : forall l m : Level,
  l << m <-> (m = LS l \/ LS l << m).
Proof.
  intros l m. split.
  - intro H. apply level_lt_iff_depth_lt in H.
    destruct (Nat.eq_dec (level_depth m) (S (level_depth l))) as [E | NE].
    + left. apply UniversePolymorphism.level_depth_injective.
      rewrite level_depth_LS. exact E.
    + right. apply level_lt_iff_depth_lt. rewrite level_depth_LS. lia.
  - intros [E | H].
    + subst m. apply UniversePolymorphism.level_lt_LS.
    + apply (level_lt_trans l (LS l) m);
        [apply UniversePolymorphism.level_lt_LS | exact H].
Qed.

(** Nothing lies strictly between a level and the level built over it. *)
Theorem no_level_between : forall l m : Level, ~ (l << m /\ m << LS l).
Proof.
  intros l m [H1 H2].
  apply level_lt_iff_depth_lt in H1. apply level_lt_iff_depth_lt in H2.
  rewrite level_depth_LS in H2. lia.
Qed.

(** Over every level there is a level, and it is unique as the next one. *)
Theorem every_level_has_next : forall l : Level,
  exists l' : Level,
    l << l' /\ (forall m, l << m -> m = l' \/ l' << m) /\
    (forall l'', (l << l'' /\ forall m, l << m -> m = l'' \/ l'' << m) -> l'' = l').
Proof.
  intro l. exists (LS l). split; [apply UniversePolymorphism.level_lt_LS | split].
  - intros m H. exact (proj1 (LS_is_next_level l m) H).
  - intros l'' [Hab Hmin].
    destruct (proj1 (LS_is_next_level l l'') Hab) as [E | Lt]; [exact E | ].
    destruct (Hmin (LS l) (UniversePolymorphism.level_lt_LS l)) as [E | Lt'].
    + symmetry. exact E.
    + exfalso. apply (level_lt_irrefl l'').
      exact (level_lt_trans l'' (LS l) l'' Lt' Lt).
Qed.

(** The ascent does not run into a highest level. (The two theorems are
    TransfiniteInductionLevel.level_no_top and no_universal_level.) *)
Theorem ascent_has_no_top :
  (forall l : Level, l << LS l)
  /\ (forall M : Level, exists L : Level, ~ (L << M \/ L = M))
  /\ ~ (exists Top : Level, forall L : Level, L << Top \/ L = Top).
Proof.
  split; [exact UniversePolymorphism.level_lt_LS | split].
  - exact TransfiniteInductionLevel.level_no_top.
  - exact TransfiniteInductionLevel.no_universal_level.
Qed.

(* ========================================================================= *)
(*  4. EVERY HIERARCHY IS NUMBERED BY THE LEVELS                             *)
(* ========================================================================= *)

Section AnyHierarchy.
  (** A structure "a base and a step": the step is injective, the base is
      not a value of the step, and induction holds. *)
  Variable X : Type.
  Variable base : X.
  Variable step : X -> X.
  Hypothesis step_injective : forall x y, step x = step y -> x = y.
  Hypothesis base_not_step : forall x, base <> step x.
  Hypothesis X_induction :
    forall P : X -> Prop, P base -> (forall x, P x -> P (step x)) -> forall x, P x.

  Fixpoint of_level (l : Level) : X :=
    match l with
    | L1 => base
    | LS l' => step (of_level l')
    end.

  Lemma of_level_injective : forall l1 l2, of_level l1 = of_level l2 -> l1 = l2.
  Proof.
    induction l1 as [| l1' IH]; destruct l2 as [| l2']; simpl; intro H.
    - reflexivity.
    - exfalso. exact (base_not_step _ H).
    - exfalso. exact (base_not_step _ (eq_sym H)).
    - f_equal. apply IH. apply step_injective. exact H.
  Qed.

  Lemma of_level_surjective : forall x : X, exists l : Level, of_level l = x.
  Proof.
    apply X_induction.
    - exists L1. reflexivity.
    - intros x [l Hl]. exists (LS l). simpl. rewrite Hl. reflexivity.
  Qed.

  (** The levels number the structure one-to-one, the base by L1 and the
      step by LS. *)
  Theorem every_hierarchy_is_the_level_series :
    of_level L1 = base
    /\ (forall l, of_level (LS l) = step (of_level l))
    /\ (forall l1 l2, of_level l1 = of_level l2 -> l1 = l2)
    /\ (forall x : X, exists l : Level, of_level l = x).
  Proof.
    split; [reflexivity | split; [intro l; reflexivity | split]].
    - exact of_level_injective.
    - exact of_level_surjective.
  Qed.

  (** Hence every element has exactly one number, counted from one. *)
  Theorem every_hierarchy_is_numbered_from_one :
    forall x : X, exists n : nat,
      (1 <= n /\ exists l : Level, of_level l = x /\ level_depth l = n)
      /\ (forall n', (exists l : Level, of_level l = x /\ level_depth l = n') -> n' = n).
  Proof.
    intro x. destruct (of_level_surjective x) as [l Hl].
    exists (level_depth l). split.
    - split; [apply level_depth_ge_one | ].
      exists l. split; [exact Hl | reflexivity].
    - intros n' [l' [Hl' Hn]].
      assert (E : l' = l) by (apply of_level_injective; rewrite Hl, Hl'; reflexivity).
      subst l'. symmetry. exact Hn.
  Qed.
End AnyHierarchy.

(** The standard nat with 0 and S is such a structure: the levels number it
    one-to-one (L1 goes to 0 — the technical indexing of the chapter). *)
Theorem nat_is_numbered_by_levels :
  (forall l1 l2, of_level nat 0 S l1 = of_level nat 0 S l2 -> l1 = l2)
  /\ (forall n : nat, exists l : Level, of_level nat 0 S l = n).
Proof.
  split.
  - apply (of_level_injective nat 0 S).
    + intros x y H. injection H. intro E. exact E.
    + intros x H. discriminate H.
  - apply (of_level_surjective nat 0 S). exact nat_ind.
Qed.

(* ========================================================================= *)
(*  5. THE TWO INDUCTIONS ARE CARRIED INTO EACH OTHER                        *)
(* ========================================================================= *)

(** Induction over the levels obtained from nat_ind through the mutually
    inverse maps. (The round-trip lemma level_nat_level used here is itself
    proved by induction on the level.) *)
Lemma level_induction_from_nat_ind :
  forall P : Level -> Prop,
    P L1 -> (forall l, P l -> P (LS l)) -> forall l, P l.
Proof.
  intros P H1 HS l.
  rewrite <- (LevelNatIso.level_nat_level l).
  generalize (LevelNatIso.level_to_nat l). intro n.
  apply (nat_ind (fun n => P (LevelNatIso.nat_to_level n))).
  - exact H1.
  - intros k Hk. simpl. apply HS. exact Hk.
Qed.

(** The transfer back: induction over nat from Level_ind. *)
Lemma nat_induction_from_Level_ind :
  forall P : nat -> Prop,
    P 0 -> (forall n, P n -> P (S n)) -> forall n, P n.
Proof.
  intros P H0 HS n.
  rewrite <- (LevelNatIso.nat_level_nat n).
  generalize (LevelNatIso.nat_to_level n). intro l.
  apply (Level_ind (fun l => P (LevelNatIso.level_to_nat l))).
  - exact H0.
  - intros l' Hl'. simpl. apply HS. exact Hl'.
Qed.

(** Induction over the depths: counted from one. *)
Theorem depth_induction_from_one :
  forall P : nat -> Prop,
    P 1 -> (forall n, P n -> P (S n)) -> forall l : Level, P (level_depth l).
Proof.
  intros P H1 HS l. induction l as [| l' IH].
  - exact H1.
  - rewrite level_depth_LS. apply HS. exact IH.
Qed.
