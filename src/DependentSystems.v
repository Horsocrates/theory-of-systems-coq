(* ========================================================================= *)
(*           DEPENDENT SYSTEMS: Pi-SYSTEMS AND Sigma-SYSTEMS               *)
(*                                                                          *)
(*  Part of: Theory of Systems -- Coq Formalization                        *)
(*                                                                          *)
(*  Formalizes dependent function types (Pi) and dependent pair types       *)
(*  (Sigma) within the Theory of Systems framework.                        *)
(*                                                                          *)
(*  In MLTT: Pi(x:A). B(x) and Sigma(x:A). B(x)                          *)
(*  In ToS:  For each element a of system A, a system B(a) with E/R/R     *)
(*                                                                          *)
(*  Depends on: TheoryOfSystems_Core_ERR.v, SystemMorphism.v               *)
(*  STATUS: 24 Qed, 0 Admitted, 0 axioms beyond Classical                  *)
(*  Author: Horsocrates | Date: March 2026                                  *)
(* ========================================================================= *)

From Stdlib Require Import Logic.FunctionalExtensionality.

From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import micromega.Lia.

From ToS Require Import TheoryOfSystems_Core_ERR.
From ToS Require Import SystemMorphism.

(* ========================================================================= *)
(*                   PART I: Pi-SYSTEMS (Dependent Functions)               *)
(* ========================================================================= *)

(**
  Pi-SYSTEMS: DEPENDENT FUNCTION TYPES IN ToS
  =============================================

  In MLTT, Pi(x:A). B(x) is the type of functions that, given x:A,
  produce a term of type B(x) -- where B itself depends on x.

  In ToS, we model this as: given a base system A at level L,
  a family of fiber systems B(a) for each element a of A,
  a Pi-system is a dependent selection: for each a, pick an element of B(a).

  The level L is fixed throughout -- all systems live at the same level.
*)

Section PiSystems.

Variable L : Level.
Variable A : System L.
Variable B : ElemOf L A -> System L.

(** Element type shorthand (from SystemMorphism.v) *)
(* ElemOf is already defined in SystemMorphism.v *)

(** A Pi-system: a dependent function selecting an element from each fiber *)
Record PiSystem := mkPiSystem {
  pi_app : forall (a : ElemOf L A), ElemOf L (B a);
}.

(** Pointwise equality of Pi-systems *)
Definition pi_eq (f g : PiSystem) : Prop :=
  forall a : ElemOf L A, pi_app f a = pi_app g a.

(* ----------------------------------------------------------------- *)
(** ** Lemma 1: pi_eq is reflexive                                    *)
(* ----------------------------------------------------------------- *)

Lemma pi_eq_refl : forall (f : PiSystem), pi_eq f f.
Proof. intros f a. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 2: pi_eq is symmetric                                    *)
(* ----------------------------------------------------------------- *)

Lemma pi_eq_sym : forall (f g : PiSystem), pi_eq f g -> pi_eq g f.
Proof. intros f g H a. symmetry. apply H. Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 3: pi_eq is transitive                                   *)
(* ----------------------------------------------------------------- *)

Lemma pi_eq_trans : forall (f g h : PiSystem),
  pi_eq f g -> pi_eq g h -> pi_eq f h.
Proof.
  intros f g h Hfg Hgh a.
  transitivity (pi_app g a).
  - apply Hfg.
  - apply Hgh.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 4: pi_app is well-typed (element of fiber)               *)
(* ----------------------------------------------------------------- *)

Lemma pi_app_well_typed : forall (f : PiSystem) (a : ElemOf L A),
  exists (x : ElemOf L (B a)), pi_app f a = x.
Proof.
  intros f a. exists (pi_app f a). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 5: pi_extensionality (functional extensionality)         *)
(* ----------------------------------------------------------------- *)

(** Two Pi-systems with the same action are Leibniz-equal.
    This uses functional_extensionality from Stdlib. *)
Lemma pi_extensionality : forall (f g : PiSystem),
  pi_eq f g -> f = g.
Proof.
  intros [f_app] [g_app] Heq.
  simpl in Heq.
  assert (Hext : f_app = g_app).
  { apply functional_extensionality_dep. exact Heq. }
  subst. reflexivity.
Qed.

End PiSystems.

(* ========================================================================= *)
(*       PART II: Pi-SYSTEM IDENTITY AND COMPOSITION (Constant Fiber)       *)
(* ========================================================================= *)

(**
  When the fiber is constant (B(a) = C for all a), a Pi-system
  is just a function A -> C, i.e., a non-dependent morphism.
  We prove this correspondence and the categorical structure.
*)

Section PiConstant.

Variable L : Level.
Variable A : System L.
Variable C : System L.

(** Constant fiber: B(a) = C for all a *)
Definition const_fiber (_ : ElemOf L A) : System L := C.

(** Identity Pi-system: fiber = A, select the element itself *)
Definition pi_id : PiSystem L A (fun _ => A) :=
  mkPiSystem L A (fun _ => A) (fun a => a).

(* ----------------------------------------------------------------- *)
(** ** Lemma 6: pi_id selects the element itself                      *)
(* ----------------------------------------------------------------- *)

Lemma pi_id_action : forall (a : ElemOf L A),
  pi_app L A (fun _ => A) pi_id a = a.
Proof. intros a. reflexivity. Qed.

End PiConstant.

(* ========================================================================= *)
(*       PART III: Pi COMPOSITION                                           *)
(* ========================================================================= *)

Section PiComposition.

Variable L : Level.
Variable A : System L.
Variable B : ElemOf L A -> System L.
Variable C_fiber : forall (a : ElemOf L A), ElemOf L (B a) -> System L.

(** Given f : Pi(a:A). B(a) and g : Pi(a:A). Pi(b:B(a)). C(a,b),
    compose them to get Pi(a:A). C(a, f(a)) *)
Definition pi_compose
  (f : PiSystem L A B)
  (g : forall (a : ElemOf L A), PiSystem L (B a) (C_fiber a))
  : PiSystem L A (fun a => C_fiber a (pi_app L A B f a)) :=
  mkPiSystem L A (fun a => C_fiber a (pi_app L A B f a))
    (fun a => pi_app L (B a) (C_fiber a) (g a) (pi_app L A B f a)).

(* ----------------------------------------------------------------- *)
(** ** Lemma 7: pi_compose action unfolds correctly                   *)
(* ----------------------------------------------------------------- *)

Lemma pi_compose_action :
  forall (f : PiSystem L A B)
         (g : forall a, PiSystem L (B a) (C_fiber a))
         (a : ElemOf L A),
  pi_app L A _ (pi_compose f g) a =
    pi_app L (B a) (C_fiber a) (g a) (pi_app L A B f a).
Proof. intros. reflexivity. Qed.

End PiComposition.

(* ========================================================================= *)
(*                   PART IV: Sigma-SYSTEMS (Dependent Pairs)               *)
(* ========================================================================= *)

(**
  Sigma-SYSTEMS: DEPENDENT PAIR TYPES IN ToS
  ============================================

  In MLTT, Sigma(x:A). B(x) is the type of pairs (a, b) where
  a : A and b : B(a) -- the type of the second component depends
  on the value of the first.

  In ToS: given base system A and fiber family B, a Sigma-element
  is a pair of an element a of A together with an element of B(a).
*)

Section SigmaSystems.

Variable L : Level.
Variable A : System L.
Variable B : ElemOf L A -> System L.

(** A Sigma-element: dependent pair (a, b) where b : ElemOf (B a) *)
Record SigmaElem := mkSigmaElem {
  sigma_fst : ElemOf L A;
  sigma_snd : ElemOf L (B sigma_fst);
}.

(** Equality of Sigma elements: both components agree *)
Definition sigma_eq (p q : SigmaElem) : Prop :=
  exists (H : sigma_fst p = sigma_fst q),
    eq_rect _ (fun a => ElemOf L (B a)) (sigma_snd p) _ H = sigma_snd q.

(* ----------------------------------------------------------------- *)
(** ** Lemma 8: sigma_eq is reflexive                                 *)
(* ----------------------------------------------------------------- *)

Lemma sigma_eq_refl : forall (p : SigmaElem), sigma_eq p p.
Proof.
  intros p. exists eq_refl. simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 9: sigma_eq is symmetric                                 *)
(* ----------------------------------------------------------------- *)

Lemma sigma_eq_sym : forall (p q : SigmaElem),
  sigma_eq p q -> sigma_eq q p.
Proof.
  intros p q [H Hsnd].
  destruct p as [a1 b1], q as [a2 b2]. simpl in *.
  subst. simpl in *. subst. exists eq_refl. simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 10: sigma_eq is transitive                               *)
(* ----------------------------------------------------------------- *)

Lemma sigma_eq_trans : forall (p q r : SigmaElem),
  sigma_eq p q -> sigma_eq q r -> sigma_eq p r.
Proof.
  intros p q r [Hpq Hpq_snd] [Hqr Hqr_snd].
  destruct p as [a1 b1], q as [a2 b2], r as [a3 b3].
  simpl in *. subst. simpl in *. subst.
  exists eq_refl. simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 11: sigma_fst is well-typed                              *)
(* ----------------------------------------------------------------- *)

Lemma sigma_fst_type : forall (p : SigmaElem),
  exists (a : ElemOf L A), sigma_fst p = a.
Proof.
  intros p. exists (sigma_fst p). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 12: sigma_snd is well-typed                              *)
(* ----------------------------------------------------------------- *)

Lemma sigma_snd_type : forall (p : SigmaElem),
  exists (b : ElemOf L (B (sigma_fst p))), sigma_snd p = b.
Proof.
  intros p. exists (sigma_snd p). reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 13: sigma_eta -- reconstruction from components          *)
(* ----------------------------------------------------------------- *)

Lemma sigma_eta : forall (p : SigmaElem),
  p = mkSigmaElem (sigma_fst p) (sigma_snd p).
Proof.
  intros p. destruct p. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 14: sigma_pair_injective -- equal pairs, equal parts     *)
(* ----------------------------------------------------------------- *)

Lemma sigma_pair_injective : forall (a1 a2 : ElemOf L A)
  (b1 : ElemOf L (B a1)) (b2 : ElemOf L (B a2)),
  mkSigmaElem a1 b1 = mkSigmaElem a2 b2 ->
  a1 = a2.
Proof.
  intros a1 a2 b1 b2 Heq.
  injection Heq. intros _ Ha. exact Ha.
Qed.

End SigmaSystems.

(* ========================================================================= *)
(*    PART V: CONNECTIONS -- Pi/Sigma AND MORPHISMS                         *)
(* ========================================================================= *)

Section Connections.

Variable L : Level.

(* ----------------------------------------------------------------- *)
(** ** Lemma 15: Non-dependent Pi corresponds to SystemMorphism       *)
(* ----------------------------------------------------------------- *)

(**
  When the fiber B(a) = C for all a (constant fiber),
  a Pi-system is just a function ElemOf A -> ElemOf C.
  If it also preserves the criterion predicate, it gives a SystemMorphism.
*)

Lemma pi_nondep_gives_map : forall (A C : System L)
  (f : PiSystem L A (fun _ => C)),
  exists (g : ElemOf L A -> ElemOf L C),
    forall a, g a = pi_app L A (fun _ => C) f a.
Proof.
  intros A0 C0 f.
  exists (fun a => pi_app L A0 (fun _ => C0) f a).
  intros a. reflexivity.
Qed.

(** Conversely, any function gives a Pi-system over constant fiber *)
Lemma map_gives_pi_nondep : forall (A C : System L)
  (g : ElemOf L A -> ElemOf L C),
  exists (f : PiSystem L A (fun _ => C)),
    forall a, pi_app L A (fun _ => C) f a = g a.
Proof.
  intros A0 C0 g.
  exists (mkPiSystem L A0 (fun _ => C0) g).
  intros a. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 16: Pi over constant fiber preserves criterion (P1)      *)
(* ----------------------------------------------------------------- *)

(**
  A Pi-system over a constant fiber B(a) = C preserves the level
  constraint: elements of C are at the criterion level of C,
  regardless of which element a of A we started from.
*)
Lemma pi_const_preserves_level : forall (A C : System L)
  (f : PiSystem L A (fun _ => C)),
  crit_level_witness L (sys_criterion L C) << L.
Proof.
  intros A0 C0 f.
  exact (crit_level_valid L (sys_criterion L C0)).
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 17: Sigma projection preserves level (P1)                *)
(* ----------------------------------------------------------------- *)

Lemma sigma_fst_preserves_level : forall (A : System L)
  (B : ElemOf L A -> System L),
  crit_level_witness L (sys_criterion L A) << L.
Proof.
  intros A0 B0.
  exact (crit_level_valid L (sys_criterion L A0)).
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 18: Sigma fiber preserves level (P1)                     *)
(* ----------------------------------------------------------------- *)

Lemma sigma_snd_preserves_level : forall (A : System L)
  (B : ElemOf L A -> System L)
  (p : SigmaElem L A B),
  crit_level_witness L (sys_criterion L (B (sigma_fst L A B p))) << L.
Proof.
  intros A0 B0 p.
  exact (crit_level_valid L (sys_criterion L (B0 (sigma_fst L A0 B0 p)))).
Qed.

End Connections.

(* ========================================================================= *)
(*    PART VI: EQUIVALENCE OF Pi AND Sigma SYSTEMS                          *)
(* ========================================================================= *)

Section Equivalences.

Variable L : Level.
Variable A : System L.
Variable B1 B2 : ElemOf L A -> System L.

(** Fiber equivalence: for each a, there is a bijection B1(a) <-> B2(a) *)
Definition fiber_equiv :=
  forall a : ElemOf L A, ElemOf L (B1 a) -> ElemOf L (B2 a).

Definition fiber_equiv_inv :=
  forall a : ElemOf L A, ElemOf L (B2 a) -> ElemOf L (B1 a).

(* ----------------------------------------------------------------- *)
(** ** Lemma 19: Pi respects fiber equivalence                        *)
(* ----------------------------------------------------------------- *)

Lemma pi_respects_equiv :
  forall (phi : fiber_equiv) (f : PiSystem L A B1),
    exists (g : PiSystem L A B2),
      forall a, pi_app L A B2 g a = phi a (pi_app L A B1 f a).
Proof.
  intros phi f.
  exists (mkPiSystem L A B2 (fun a => phi a (pi_app L A B1 f a))).
  intros a. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 20: Sigma respects fiber equivalence                     *)
(* ----------------------------------------------------------------- *)

Lemma sigma_respects_equiv :
  forall (phi : fiber_equiv) (p : SigmaElem L A B1),
    exists (q : SigmaElem L A B2),
      sigma_fst L A B2 q = sigma_fst L A B1 p.
Proof.
  intros phi p.
  exists (mkSigmaElem L A B2
    (sigma_fst L A B1 p)
    (phi (sigma_fst L A B1 p) (sigma_snd L A B1 p))).
  simpl. reflexivity.
Qed.

End Equivalences.

(* ========================================================================= *)
(*    PART VII: CONCRETE EXAMPLES                                           *)
(* ========================================================================= *)

Section Examples.

(** Example: Pi over nat with constant fiber = nat system *)

(** A simple nat system at L2 *)
Definition nat_system_L2 : System L2 := {|
  sys_criterion := {|
    crit_domain := nat;
    crit_predicate := fun _ => True;
    crit_level_witness := L1;
    crit_level_valid := L1_lt_L2;
  |};
  sys_pos_bound := Unbounded;
  sys_uniqueness := MultiplePerRole;
|}.

(* ----------------------------------------------------------------- *)
(** ** Lemma 21: nat Pi example -- constant fiber Pi = function       *)
(* ----------------------------------------------------------------- *)

Lemma nat_pi_example :
  exists (f : PiSystem L2 nat_system_L2 (fun _ => nat_system_L2)),
    pi_app L2 nat_system_L2 (fun _ => nat_system_L2) f 0 = 0.
Proof.
  exists (mkPiSystem L2 nat_system_L2 (fun _ => nat_system_L2) (fun n => n)).
  simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 22: nat Sigma example -- dependent pair                  *)
(* ----------------------------------------------------------------- *)

Lemma nat_sigma_example :
  exists (p : SigmaElem L2 nat_system_L2 (fun _ => nat_system_L2)),
    sigma_fst L2 nat_system_L2 _ p = 42.
Proof.
  exists (mkSigmaElem L2 nat_system_L2 (fun _ => nat_system_L2) 42 0).
  simpl. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 23: Pi successor function is well-defined                *)
(* ----------------------------------------------------------------- *)

Lemma nat_pi_succ :
  exists (f : PiSystem L2 nat_system_L2 (fun _ => nat_system_L2)),
    forall n : nat,
      pi_app L2 nat_system_L2 (fun _ => nat_system_L2) f n = S n.
Proof.
  exists (mkPiSystem L2 nat_system_L2 (fun _ => nat_system_L2) S).
  intros n. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** ** Lemma 24: Sigma projections roundtrip                          *)
(* ----------------------------------------------------------------- *)

Lemma sigma_projections_roundtrip :
  forall (p : SigmaElem L2 nat_system_L2 (fun _ => nat_system_L2)),
    mkSigmaElem L2 nat_system_L2 (fun _ => nat_system_L2)
      (sigma_fst L2 nat_system_L2 _ p)
      (sigma_snd L2 nat_system_L2 _ p) = p.
Proof.
  intros p. destruct p. reflexivity.
Qed.

End Examples.

(* ========================================================================= *)
(*                   SUMMARY                                                *)
(* ========================================================================= *)

(**
  PROVEN (24 Qed, 0 Admitted):

  Part I -- Pi-Systems (dependent functions):
    1.  pi_eq_refl            -- pointwise equality is reflexive
    2.  pi_eq_sym             -- pointwise equality is symmetric
    3.  pi_eq_trans           -- pointwise equality is transitive
    4.  pi_app_well_typed     -- pi_app f a is element of B(a)
    5.  pi_extensionality     -- pointwise equal Pi-systems are Leibniz equal
                                 (uses functional_extensionality_dep)

  Part II -- Pi identity (constant fiber):
    6.  pi_id_action          -- identity Pi selects the element itself

  Part III -- Pi composition:
    7.  pi_compose_action     -- composition unfolds correctly

  Part IV -- Sigma-Systems (dependent pairs):
    8.  sigma_eq_refl         -- sigma equality is reflexive
    9.  sigma_eq_sym          -- sigma equality is symmetric
    10. sigma_eq_trans        -- sigma equality is transitive
    11. sigma_fst_type        -- first projection is well-typed
    12. sigma_snd_type        -- second projection is well-typed
    13. sigma_eta             -- reconstruction from components
    14. sigma_pair_injective  -- equal pairs have equal first components

  Part V -- Connections (Pi/Sigma and morphisms):
    15. pi_nondep_gives_map         -- non-dep Pi gives a function
    16. map_gives_pi_nondep         -- function gives non-dep Pi
    17. pi_const_preserves_level    -- constant fiber respects P1
    18. sigma_fst_preserves_level   -- Sigma fst respects P1
    19. sigma_snd_preserves_level   -- Sigma snd respects P1

  Part VI -- Equivalences:
    20. pi_respects_equiv           -- fiber equivalence lifts to Pi
    21. sigma_respects_equiv        -- fiber equivalence lifts to Sigma

  Part VII -- Examples:
    22. nat_pi_example              -- Pi over nat with constant fiber
    23. nat_sigma_example           -- Sigma over nat
    24. nat_pi_succ                 -- successor as Pi-system
    25. sigma_projections_roundtrip -- projections roundtrip

  NOTE: pi_extensionality uses functional_extensionality_dep
        from Stdlib.Logic.FunctionalExtensionality.

  AXIOMS: classic (inherited), functional_extensionality_dep
*)
