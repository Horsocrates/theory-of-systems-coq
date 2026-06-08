(** * RamseyBoundary.v — Ramsey's theorem ACROSS the finitization boundary: the finite Ramsey number
       R(3,3)=6 is an ELEMENT (a decidable, computed boolean fact, 0 axioms), while the INFINITE Ramsey
       theorem is a ROLE-LIMIT whose choice-content localizes — on the decidable side — to the
       least-successor selection of vein B (dc_chain).  This is the EXACT boundary of DecidableKonig:
       finite combinatorics is Element-drawable; the infinite leap is the price.

    -- The finite side (Element, 0 axioms) --
      A 2-colouring of the 15 edges of K6 is the 15-bit list `edges6 c`.  `mono15` is a BOOLEAN decider:
      it ORs the 20 triple-tests, true iff some triangle is monochromatic.  Then:
        R33_upper : forall c, mono15 (edges6 c) = true   — K6 ALWAYS forces a monochromatic triangle.
      Proved by FINITE ENUMERATION: forallb mono15 over all 2^15 edge-colourings is true (vm_compute),
      and every concrete colouring's 15-bit list is in that enumeration.  No pigeonhole induction, no
      axiom — a closed computation, the signature of an Element.
        R33_lower : hasmono5 c5 = false                  — the pentagon/pentagram 2-colouring of K5 has
      NO monochromatic triangle (both colour classes are 5-cycles, girth 5).  So R(3,3) > 5.
      Together: R(3,3) = 6 EXACTLY, a decided finite number.

    -- The infinite side (role-limit; choice localized to vein B) --
      Infinite Ramsey (every 2-colouring of pairs of N has an infinite monochromatic set) needs a weak
      choice: its construction picks, at each pivot, the colour that recurs infinitely often (an
      undecidable Pi-predicate) and an infinite active subset.  We localize this EXACTLY as DecidableKonig
      localized Konig: GIVEN the construction's output as decidable Rules — a pivot enumeration, the
      homogeneous colour `actcolor`, and a DECIDABLE "later index of colour b" witness — the infinite
      monochromatic set is built DETERMINISTICALLY by the least-successor chain `dc_chain` of vein B,
      0 axioms.  The remaining choice-content is exactly those hypotheses (the infinite pigeonhole on
      pivot colours), the role-limit; settheory/ChoicePriceMap.v, foundation/P4ProhibitsAC.v price it.

    -- The thesis (the boundary, sharp) --
      Ramsey theory straddles the SAME line as Konig / selection-without-AC: the finite theorem is a
      decidable Element (a closed boolean computation), the infinite theorem is a role-limit whose price,
      on the decidable side, IS the least-successor selector already built in vein B.  Finite combinatorics
      = Element; the infinite leap = choice.

    ============ E/R/R разбор ============
      Elements : конкретная раскраска c (15 бит K6 / 10 бит K5); конечные вершины; каждая раскраска актуальна (P4).
      Roles    : монохромный треугольник = роль; пентаграмма c5 = свидетель нижней границы; бесконечное
                 монохромное множество = role-limit (незавершённая ветвь).
      Rules    : pigeonhole форсирует треугольник в K6 (разрешитель mono15, перебор 2^15, 0 акс); бесконечно —
                 «наименьший следующий индекс цвета b» (dc_chain нити B) детерминирует монохромную подпоследовательность.
      ДИАГНОСТИКА (P4): КОНЕЧНЫЙ Рамсей = Element (R(3,3)=6 вычислимо, булев разрешитель, 0 акс); БЕСКОНЕЧНЫЙ =
        role-limit (бесконечный pigeonhole = выбор; на разрешимой стороне = dc_chain, 0 акс при данном свидетеле).
        Та же граница finite=decidable / infinite=choice, что König. Уровень: `новая теорема` (конечный) + `локализация цены`.

    STATUS: 15 Qed, 0 Admitted, 0 axioms  (finite by enumeration; infinite reuses cs.CountableDependentChoiceFree)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Bool Arith Lia.
From ToS Require Import cs.CountableDependentChoiceFree.
Import ListNotations.

(* ===================================================================== *)
(*  FINITE SIDE: R(3,3) = 6 as a decided boolean fact (Element)            *)
(* ===================================================================== *)

(** A triple is monochromatic iff its three edges (positions i,j,k in the 15-bit list) are all equal. *)
Definition tri (l : list bool) (i j k : nat) : bool :=
  Bool.eqb (nth i l false) (nth j l false) && Bool.eqb (nth j l false) (nth k l false).

(** The 15 edges of K6 in canonical order:
      0:(0,1) 1:(0,2) 2:(0,3) 3:(0,4) 4:(0,5) 5:(1,2) 6:(1,3) 7:(1,4) 8:(1,5)
      9:(2,3) 10:(2,4) 11:(2,5) 12:(3,4) 13:(3,5) 14:(4,5).  mono15 ORs the 20 triangle-tests. *)
Definition mono15 (l : list bool) : bool :=
  tri l 0 1 5 || tri l 0 2 6 || tri l 0 3 7 || tri l 0 4 8 ||
  tri l 1 2 9 || tri l 1 3 10 || tri l 1 4 11 ||
  tri l 2 3 12 || tri l 2 4 13 || tri l 3 4 14 ||
  tri l 5 6 9 || tri l 5 7 10 || tri l 5 8 11 ||
  tri l 6 7 12 || tri l 6 8 13 || tri l 7 8 14 ||
  tri l 9 10 12 || tri l 9 11 13 || tri l 10 11 14 ||
  tri l 12 13 14.

(** The 15-bit edge list of a concrete colouring of K6. *)
Definition edges6 (c : nat -> nat -> bool) : list bool :=
  [ c 0 1; c 0 2; c 0 3; c 0 4; c 0 5;
    c 1 2; c 1 3; c 1 4; c 1 5;
    c 2 3; c 2 4; c 2 5;
    c 3 4; c 3 5;
    c 4 5 ].

(** All bit-vectors of a given length — the finite enumeration of edge-colourings. *)
Fixpoint all_vectors (n : nat) : list (list bool) :=
  match n with
  | O => [ [] ]
  | S k => flat_map (fun v => [false :: v; true :: v]) (all_vectors k)
  end.

(** ★ Every bit-vector occurs in the enumeration of its own length. *)
Lemma in_all_vectors : forall v : list bool, In v (all_vectors (length v)).
Proof.
  induction v as [| b v IH]; simpl.
  - left. reflexivity.
  - apply in_flat_map. exists v. split.
    + exact IH.
    + destruct b; simpl; [ right; left | left ]; reflexivity.
Qed.

(** ★ The closed computation: EVERY 2-colouring of K6's 15 edges has a monochromatic triangle. *)
Lemma enum_forces_triangle : forallb mono15 (all_vectors 15) = true.
Proof. vm_compute. reflexivity. Qed.

(** ★★ R(3,3) ≤ 6 (Element): any 2-colouring of K6 forces a monochromatic triangle — by finite
    enumeration, 0 axioms.  This is a CLOSED boolean fact, the signature of decidability. *)
Theorem R33_upper : forall c : nat -> nat -> bool, mono15 (edges6 c) = true.
Proof.
  intro c.
  pose proof (proj1 (forallb_forall mono15 (all_vectors 15)) enum_forces_triangle) as H.
  apply H.
  change 15 with (length (edges6 c)).
  apply in_all_vectors.
Qed.

(** The pentagon/pentagram 2-colouring of K5: edge {i,j} is "red" iff i,j are cyclically adjacent
    (|i-j| = ±1 mod 5).  Both colour classes are 5-cycles (girth 5) — no triangle in either. *)
Definition c5 (i j : nat) : bool :=
  let d := (i + 5 - j) mod 5 in Nat.eqb d 1 || Nat.eqb d 4.

Definition tri_c (c : nat -> nat -> bool) (a b d : nat) : bool :=
  Bool.eqb (c a b) (c a d) && Bool.eqb (c a d) (c b d).

(** The 10 triangles of K5. *)
Definition hasmono5 (c : nat -> nat -> bool) : bool :=
  tri_c c 0 1 2 || tri_c c 0 1 3 || tri_c c 0 1 4 || tri_c c 0 2 3 ||
  tri_c c 0 2 4 || tri_c c 0 3 4 || tri_c c 1 2 3 || tri_c c 1 2 4 ||
  tri_c c 1 3 4 || tri_c c 2 3 4.

(** ★★ R(3,3) > 5 (Element): the pentagram colouring of K5 has NO monochromatic triangle — computed. *)
Theorem R33_lower : hasmono5 c5 = false.
Proof. vm_compute. reflexivity. Qed.

(** ★ R(3,3) = 6 EXACTLY: K6 forces a monochromatic triangle, K5 need not.  A decided finite number. *)
Theorem ramsey_3_3 :
  (forall c, mono15 (edges6 c) = true) /\ (exists c, hasmono5 c = false).
Proof. split; [ exact R33_upper | exists c5; exact R33_lower ]. Qed.

(** ★ The finite Ramsey property is given by a BOOLEAN decider — the Element witness (trivially decidable). *)
Corollary ramsey_decidable :
  forall c, { mono15 (edges6 c) = true } + { mono15 (edges6 c) = false }.
Proof. intro c. destruct (mono15 (edges6 c)); [ left | right ]; reflexivity. Qed.

(* ===================================================================== *)
(*  INFINITE SIDE: infinite Ramsey as a role-limit (choice = vein B)       *)
(* ===================================================================== *)

Section InfiniteRamsey.

  Variable c : nat -> nat -> bool.          (* a 2-colouring of pairs of N *)

  (** The construction's OUTPUT, taken as decidable Rules (cf. DecidableKonig's konig_step):
      pivot enumerates the pivots, actcolor i is the homogeneous colour from pivot i forward. *)
  Variable pivot : nat -> nat.
  Variable actcolor : nat -> bool.
  Hypothesis pivot_inc : forall i j, i < j -> pivot i < pivot j.
  Hypothesis homog : forall i j, i < j -> c (pivot i) (pivot j) = actcolor i.

  (** The infinitely-recurring colour b and a DECIDABLE "later pivot of colour b" — the localized choice. *)
  Variable b : bool.
  Variable s0 : nat.
  Hypothesis s0_color : actcolor s0 = b.

  Definition Rb (i j : nat) : bool := Nat.ltb i j && Bool.eqb (actcolor j) b.
  Hypothesis later : forall i, exists j, Rb i j = true.

  (** The deterministic monochromatic-pivot indices: the least-successor chain of vein B (0 axioms). *)
  Definition idx (k : nat) : nat := dc_chain Rb later s0 k.

  Lemma idx_step : forall k, Rb (idx k) (idx (S k)) = true.
  Proof. intro k. unfold idx. exact (dc_chain_step Rb later s0 k). Qed.

  Lemma idx_lt_succ : forall k, idx k < idx (S k).
  Proof.
    intro k. pose proof (idx_step k) as Hs. unfold Rb in Hs.
    apply andb_true_iff in Hs. destruct Hs as [Hlt _].
    apply Nat.ltb_lt in Hlt. exact Hlt.
  Qed.

  (** ★ The chain of monochromatic-pivot indices is strictly increasing. *)
  Lemma idx_inc : forall k l, k < l -> idx k < idx l.
  Proof.
    intros k l Hkl. induction Hkl as [| m Hm IH].
    - apply idx_lt_succ.
    - apply Nat.lt_trans with (m := idx m); [ exact IH | apply idx_lt_succ ].
  Qed.

  (** ★ Every chosen index carries colour b. *)
  Lemma idx_color : forall k, actcolor (idx k) = b.
  Proof.
    destruct k as [| k].
    - unfold idx. simpl. exact s0_color.
    - pose proof (idx_step k) as Hs. unfold Rb in Hs.
      apply andb_true_iff in Hs. destruct Hs as [_ Hc].
      apply Bool.eqb_prop in Hc. exact Hc.
  Qed.

  (** ★★ INFINITE RAMSEY (decidable side, 0 axioms): the pivots H k := pivot (idx k) form a strictly
      increasing infinite set, all of whose pairs have colour b — a monochromatic infinite set, built
      deterministically by the vein-B least-successor chain.  No AC: the choice-content sits entirely in
      the hypotheses (the infinite pigeonhole on pivot colours), the role-limit. *)
  Theorem ramsey_inf_mono : forall k l, k < l -> c (pivot (idx k)) (pivot (idx l)) = b.
  Proof.
    intros k l Hkl.
    assert (Hlt : idx k < idx l) by (apply idx_inc; exact Hkl).
    rewrite (homog (idx k) (idx l) Hlt). apply idx_color.
  Qed.

  Theorem ramsey_inf_increasing : forall k l, k < l -> pivot (idx k) < pivot (idx l).
  Proof. intros k l Hkl. apply pivot_inc, idx_inc, Hkl. Qed.

  (** ★ The monochromatic set is genuinely INFINITE: injective into N (strictly increasing). *)
  Theorem ramsey_inf_injective : forall k l, pivot (idx k) = pivot (idx l) -> k = l.
  Proof.
    intros k l Heq.
    destruct (Nat.lt_trichotomy k l) as [Hlt | [Heqkl | Hgt]].
    - exfalso. pose proof (ramsey_inf_increasing k l Hlt) as Hp. lia.
    - exact Heqkl.
    - exfalso. pose proof (ramsey_inf_increasing l k Hgt) as Hp. lia.
  Qed.

  (** ★ Packaged: there EXISTS an infinite (strictly increasing) monochromatic set of colour b. *)
  Theorem ramsey_inf_exists :
    exists H : nat -> nat,
      (forall k l, k < l -> H k < H l) /\
      (forall k l, k < l -> c (H k) (H l) = b).
  Proof.
    exists (fun k => pivot (idx k)). split.
    - intros k l Hkl. exact (ramsey_inf_increasing k l Hkl).
    - intros k l Hkl. exact (ramsey_inf_mono k l Hkl).
  Qed.

End InfiniteRamsey.

(* ===================================================================== *)
(*  CAPSTONE — the boundary                                                *)
(* ===================================================================== *)

(** Ramsey across the finitization boundary:
      (finite)    R(3,3) = 6 is a DECIDED Element — mono15 forces a triangle in K6 (R33_upper, by closed
                  enumeration of all 2^15 colourings, 0 axioms), and the pentagram colouring avoids one in
                  K5 (R33_lower) — a computed finite number, the signature of decidability;
      (infinite)  the infinite Ramsey theorem is a ROLE-LIMIT: given the construction's output as decidable
                  Rules + a decidable "later pivot of colour b", the infinite monochromatic set is built
                  DETERMINISTICALLY by vein B's dc_chain (ramsey_inf_mono / _increasing / _injective,
                  0 axioms); the choice-content is exactly the infinite pigeonhole hypothesis.
    Thesis: Ramsey straddles the SAME line as Konig / selection-without-AC — finite combinatorics is an
    Element (a closed boolean computation), the infinite leap is choice, and its decidable-side price IS
    the least-successor selector of vein B.  Honest boundary: settheory/ChoicePriceMap.v,
    foundation/P4ProhibitsAC.v (AC); the infinitely-recurring colour is the undecidable Pi-predicate.
    Level: a finite Ramsey theorem (new in the repo) + the infinite-side AC-price localization. *)
Theorem ramsey_boundary :
  (* finite: a decided number, 0 axioms *)
  ((forall c, mono15 (edges6 c) = true) /\ (exists c, hasmono5 c = false))
  /\ (* infinite, decidable side: a deterministic monochromatic set via vein B, 0 axioms *)
  (forall (c : nat -> nat -> bool) (pivot : nat -> nat) (actcolor : nat -> bool),
     (forall i j, i < j -> pivot i < pivot j) ->
     (forall i j, i < j -> c (pivot i) (pivot j) = actcolor i) ->
     forall (b : bool) (s0 : nat), actcolor s0 = b ->
     (forall i, exists j, Rb actcolor b i j = true) ->
     exists H : nat -> nat,
       (forall k l, k < l -> H k < H l) /\
       (forall k l, k < l -> c (H k) (H l) = b)).
Proof.
  split.
  - exact ramsey_3_3.
  - intros c pivot actcolor Hinc Hhom b s0 Hs0 Hlater.
    eapply ramsey_inf_exists; eassumption.
Qed.
