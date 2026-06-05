(** * NumberIsVolume.v — "number = volume" made rigorous: the counting measure on a causal set is a
      genuine FINITELY-ADDITIVE, MONOTONE measure with empty = 0, and on the chain the half-open causal
      segments TILE exactly, so the volume adds.  This deepens the NUMBER half of CausalOrderGeometry.v:
      "number = volume" is not a metaphor but a measure — and the volume is intrinsically FINITE (a nat),
      the Element-side replacement of the continuum volume integral integral sqrt(-g).

    -- The measure --
      A region of the causal set is the (finite) set of its elements present; its VOLUME is the COUNT of
      those elements (Sorkin: "number = volume").  This is a finitely-additive measure:
        - additive:  vol (A disjoint-union B) = vol A + vol B   (length_app);
        - monotone:  A included in B  =>  vol A <= vol B          (NoDup_incl_length);
        - empty:     vol empty = 0.
      On the CHAIN (a discrete timelike geodesic), the half-open causal segment [x,y) has volume seg x y =
      y - x, and these segments TILE exactly: for x <= y <= z, [x,z) = [x,y) disjoint-union [y,z), so
      seg x z = seg x y + seg y z — the discrete proper-volume adds along the chain with NO correction.

    -- The P4 point --
      The volume is a COUNT — a nat, finite by construction.  It cannot diverge; there is no convergence
      condition, no role-limit.  The continuum volume integral integral sqrt(-g) d^4x (a real that can
      diverge) is replaced by an exact, always-finite integer.  Geometry's scale becomes Element-side.

    -- HONEST scope --
      A 1D-chain instance plus the general counting measure on finite regions.  Known: causal-set kinematics
      (Sorkin), "number = volume".  This file does NOT prove the continuum limit "count -> true volume"
      (the causal-set closeness / Hauptvermutung is open/conjectural), and does NOT claim nature IS a causal
      set.  It formalizes that the counting volume is a genuine finite measure that tiles on the chain.

    Elements: vol A = length A; the chain segment seg x y = y - x; seg 0 4 = 4
    Roles:    count = measure; disjoint union = additivity; inclusion = monotonicity; segment = tile
    Rules:    number = volume is a finitely-additive monotone measure; tiles exactly on the chain; finite

    ============ E/R/R разбор ============
      Rules (L5): объём области = СЧЁТ её элементов = подлинная конечно-аддитивная мера (аддитивность по
                  непересекающимся, монотонность, пусто=0); на цепи полуоткрытые сегменты ТАЙЛИРУЮТ.
      Roles (L4): счёт = мера; непересекающееся объединение = аддитивность; вложение = монотонность;
                  сегмент = тайл; P4 = объём интринсически конечен (nat), не role-limit интеграл.
      Elements  : vol A := length A; vol(A++B)=vol A+vol B; seg x y := y-x; seg x z = seg x y + seg y z.
    ДИАГНОСТИКА (P4): «число = объём» — не метафора, а МЕРА (аддитивность + монотонность + точное замощение,
    машинно).  Объём = nat (Element, конечен по построению), не вещественный интеграл (role-limit, мог бы
    расходиться) = Element-сторонняя замена int sqrt(-g).  ЧЕСТНО: 1D-цепь + общая мера на конечных
    областях; континуумный предел счёт->объём = гипотеза близости Соркина (открыта), НЕ доказываю.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  The counting measure on finite regions                                 *)
(* ===================================================================== *)

(** A region = the finite list of causal-set elements present in it; its VOLUME is the count. *)
Definition vol (A : list nat) : nat := length A.

Definition disjoint (A B : list nat) : Prop := forall x, In x A -> ~ In x B.

(** Empty region has zero volume. *)
Lemma vol_empty : vol [] = 0.
Proof. reflexivity. Qed.

(** ★ FINITE ADDITIVITY: the volume of a concatenation is the sum of volumes (and for disjoint regions
    the concatenation IS the union, by disjoint_union_nodup below). *)
Lemma vol_additive : forall A B, vol (A ++ B) = vol A + vol B.
Proof. intros A B. unfold vol. apply length_app. Qed.

(** For disjoint regions, the concatenation is a valid duplicate-free representation of the union — so
    vol_additive genuinely counts the union without overcounting. *)
Lemma disjoint_union_nodup :
  forall A B, NoDup A -> NoDup B -> disjoint A B -> NoDup (A ++ B).
Proof. intros A B HA HB Hd. apply NoDup_app; [ exact HA | exact HB | exact Hd ]. Qed.

(** ★ MONOTONICITY: a sub-region has no greater volume. *)
Lemma vol_monotone : forall A B, NoDup A -> incl A B -> vol A <= vol B.
Proof. intros A B HA Hi. unfold vol. apply NoDup_incl_length; [ exact HA | exact Hi ]. Qed.

(* ===================================================================== *)
(*  The chain: half-open causal segments tile, so volume adds exactly      *)
(* ===================================================================== *)

(** The volume of the half-open causal segment [x,y) on the chain = number of elements = y - x. *)
Definition seg (x y : nat) : nat := y - x.

Lemma seg_self : forall x, seg x x = 0.
Proof. intro x. unfold seg. apply Nat.sub_diag. Qed.

(** ★ The segments TILE exactly: for x <= y <= z, [x,z) = [x,y) disjoint-union [y,z), so volume ADDS
    with no correction — discrete proper-volume additivity along the chain. *)
Lemma seg_additive : forall x y z, x <= y -> y <= z -> seg x z = seg x y + seg y z.
Proof. intros x y z Hxy Hyz. unfold seg. lia. Qed.

Lemma seg_concrete : seg 0 4 = 4.   (* the segment [0,4) has 4 elements *)
Proof. reflexivity. Qed.

(** Bridge: the explicit segment list [x, x+1, ..., y-1] has length = seg x y — the count IS the volume. *)
Lemma seg_is_count : forall x y, length (seq x (y - x)) = seg x y.
Proof. intros x y. unfold seg. apply length_seq. Qed.

(* ===================================================================== *)
(*  Capstone: number = volume is a finite measure that tiles               *)
(* ===================================================================== *)

(** "number = volume" made rigorous:
      (additive)  vol (A ++ B) = vol A + vol B — a finitely-additive measure;
      (monotone)  A included in B => vol A <= vol B;
      (empty)     vol empty = 0;
      (tiles)     on the chain the half-open segments tile: seg x z = seg x y + seg y z for x<=y<=z;
      (count)     the segment's element count IS its volume (length (seq ...) = seg).
    The volume is a COUNT — a nat, finite by construction (P4): the Element-side replacement of the
    continuum volume integral. *)
Theorem number_is_volume :
  (forall A B, vol (A ++ B) = vol A + vol B)
  /\ (forall A B, NoDup A -> incl A B -> vol A <= vol B)
  /\ vol [] = 0
  /\ (forall x y z, x <= y -> y <= z -> seg x z = seg x y + seg y z)
  /\ (forall x y, length (seq x (y - x)) = seg x y).
Proof.
  split; [ exact vol_additive | ].
  split; [ exact vol_monotone | ].
  split; [ exact vol_empty | ].
  split; [ exact seg_additive | exact seg_is_count ].
Qed.
