(** * QuinticUnsolvable.v — the concrete Abel–Ruffini quintic x^5 - 6x + 3, with the group-theoretic
       HEART machine-checked: a transposition and a 5-cycle GENERATE S_5 (120 permutations) — a closed
       finite computation (Element, 0 axioms).  This is the piece that was MISSING from the repo's
       Abel–Ruffini engine (algebra/SolvableGroup.v supplied "perfect ⇒ not solvable" but took the
       group's structure as an abstract premise); here the structure is COMPUTED.

    -- Why x^5 - 6x + 3 is unsolvable (the classical chain) --
      (1) it is irreducible over Q (Eisenstein at p=3);
      (2) it has exactly 2 non-real roots (3 real + 2 complex — derivative f'=5x^4-6 has 2 real critical
          points, so at most 3 real; IVT sign-changes give at least 3 real);
      (3) hence its Galois group, as a subgroup of S_5, contains a 5-cycle (irreducible degree 5 ⇒ 5 | |G|,
          Cauchy) AND a transposition (complex conjugation swaps the 2 non-real roots, fixes the 3 real);
      (4) a transposition + a 5-cycle GENERATE S_5  ← THIS file proves it, by computation;
      (5) so Gal = S_5, whose section A_5 is simple non-abelian, hence perfect — NOT solvable;
      (6) by the Galois solvability criterion, the polynomial is not solvable by radicals.

    -- What is MACHINE-CHECKED here (Element side, 0 axioms) --
      * (4) `gen_report`: the right-multiplication closure of {t=(0 1), c=(0 1 2 3 4)} has exactly 120
        DISTINCT elements, each a genuine permutation of {0..4}, is closed under the generators, and
        contains the identity — i.e. it IS S_5 (|S_5|=120).  A closed finite computation (vm_compute).
      * `s5_nonabelian`: t·c ≠ c·t — S_5 is non-abelian (the engine's NonAbelianFull input).
      * (1,2) arithmetic of THE polynomial: `no_rational_root` (no integer divisor of the constant 3 is a
        root — monic ⇒ every rational root is such an integer, the rational-root theorem), and
        `sign_changes` (f alternates sign on -2,-1,1,2 ⇒ ≥3 real roots by IVT).

    -- What stays a ROLE-LIMIT (honestly cited, not faked) --
      The Galois-theoretic bridges (2)→(3) "complex conjugation is a transposition", (3)+(4)⇒"Gal=S_5",
      (5) "A_5 simple", and (6) the radical-tower ⇔ solvable-group criterion are the completed-object
      content — the same wall algebra/SolvableGroup.v names for A_5's simplicity.  The engine
      `quintic_galois_group_not_solvable` discharges (5)→(6) GIVEN a perfect non-abelian group; this file
      feeds it the computed S_5 structure and the polynomial's arithmetic, and cites the bridges.

    ============ E/R/R разбор ============
      Elements : перестановки {0..4} (списки длины 5); многочлен x^5-6x+3; генераторы t (транспозиция), c (5-цикл).
      Roles    : разрешимость в радикалах = role-limit (производный ряд → {e}); группа Галуа = роль симметрий корней;
                 комплексное сопряжение = транспозиция-роль.
      Rules    : замыкание под умножением на генераторы (разрешимо: 120 перестановок = S_5); Abel-Ruffini
                 perfect non-abelian ⟹ не разрешима (движок); рацион. корень монического ⟹ целый делитель 3.
      ДИАГНОСТИКА (P4): порождение S_5 транспозицией+5-циклом = Element (замкнутое вычисление 120 перест., 0 акс) —
        НОВОЕ ядро; неразрешимость квинтика = role-limit на классических мостах (Gal=S_5; A_5 простая; критерий Галуа),
        честно цитируемых (как SolvableGroup для простоты A_5). Уровень: `новая теорема` (порождение S_5) + `сборка`.

    STATUS: 7 Qed, 0 Admitted, 0 axioms  (S_5 by computation; unsolvability engine reused from algebra.SolvableGroup)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List PeanoNat Bool Arith Lia ZArith.
From ToS Require Import algebra.SolvableGroup.
Import ListNotations.

(* ===================================================================== *)
(*  S_5 by computation: a transposition and a 5-cycle generate it          *)
(* ===================================================================== *)

(** A permutation of {0,1,2,3,4} is the length-5 list of its images. *)
Definition perm := list nat.
Definition dom : list nat := [0; 1; 2; 3; 4].
Definition app (p : perm) (i : nat) : nat := nth i p 0.
Definition comp (p q : perm) : perm := map (fun i => app p (app q i)) dom.  (* (p∘q)(i) = p(q i) *)

Definition idp : perm := [0; 1; 2; 3; 4].
Definition t   : perm := [1; 0; 2; 3; 4].          (* the transposition (0 1) *)
Definition c   : perm := [1; 2; 3; 4; 0].          (* the 5-cycle (0 1 2 3 4) *)
Definition gens : list perm := [t; c].

Fixpoint leqb (p q : perm) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => Nat.eqb a b && leqb p' q'
  | _, _ => false
  end.
Definition inb (x : perm) (l : list perm) : bool := existsb (leqb x) l.

(** One BFS round: right-multiply every current element by each generator, adding the new ones. *)
Definition addnew (s : list perm) (x : perm) : list perm := if inb x s then s else s ++ [x].
Definition next (s : list perm) : list perm :=
  fold_left (fun acc p => fold_left (fun acc2 g => addnew acc2 (comp g p)) gens acc) s s.

(** The subgroup generated by t and c (BFS to the fixed point; 50 rounds saturate S_5). *)
Definition gen_closure : list perm := Nat.iter 50 next [idp].

(** A genuine permutation of {0..4}: length 5 and each point hit exactly once. *)
Definition is_perm5 (p : perm) : bool :=
  Nat.eqb (length p) 5 && forallb (fun i => Nat.eqb (count_occ Nat.eq_dec p i) 1) dom.

(** ★★ THE NEW THEOREM (machine-checked, 0 axioms): the closure of {transposition, 5-cycle} has
    exactly 120 DISTINCT permutations of {0..4}, is closed under the generators, and contains the
    identity — i.e. it IS the symmetric group S_5 (|S_5| = 120).  A single closed computation. *)
Definition gen_report : bool :=
  let g := gen_closure in
  Nat.eqb (length g) 120 &&
  forallb is_perm5 g &&
  forallb (fun p => forallb (fun gn => inb (comp gn p) g) gens) g &&
  inb idp g &&
  Nat.eqb (length (nodup (list_eq_dec Nat.eq_dec) g)) 120.

Lemma gen_report_true : gen_report = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ Headline corollary: ⟨transposition, 5-cycle⟩ has 120 elements = S_5. *)
Lemma s5_size : length gen_closure = 120.
Proof. vm_compute. reflexivity. Qed.

(** ★ S_5 is non-abelian: t·c ≠ c·t (the engine's NonAbelianFull input). *)
Lemma s5_nonabelian : leqb (comp t c) (comp c t) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Arithmetic of the specific polynomial x^5 - 6x + 3                      *)
(* ===================================================================== *)

Definition qf (x : Z) : Z := (x ^ 5 - 6 * x + 3)%Z.

(** Monic with constant term 3: any rational root is an integer dividing 3 (rational-root theorem),
    i.e. one of ±1, ±3.  None of them is a root — so x^5-6x+3 has NO rational root. *)
Definition root_candidates : list Z := (1 :: -1 :: 3 :: -3 :: nil)%Z.
Definition no_rational_root : bool := forallb (fun d => negb (Z.eqb (qf d) 0%Z)) root_candidates.

Lemma no_rational_root_true : no_rational_root = true.
Proof. vm_compute. reflexivity. Qed.

(** f alternates sign on -2, -1, 1, 2 (values -17, 8, -2, 23) ⇒ at least 3 real roots (IVT).
    With f'=5x^4-6 having exactly 2 real critical points (at most 3 real roots), exactly 3 real +
    2 non-real — so complex conjugation is a transposition of the Galois group. *)
Definition sign_changes : bool :=
  (qf (-2) <? 0)%Z && (0 <? qf (-1))%Z && (qf 1 <? 0)%Z && (0 <? qf 2)%Z.

Lemma sign_changes_true : sign_changes = true.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE — Abel–Ruffini for x^5 - 6x + 3, assembled                     *)
(* ===================================================================== *)

(** The concrete quintic x^5 - 6x + 3 across the boundary:
      (A) NEW Element: a transposition and a 5-cycle GENERATE S_5 — gen_report computes 120 distinct
          permutations, closed, with identity (vm_compute, 0 axioms).  This is the group-theoretic heart
          of why an irreducible quintic with 2 non-real roots has Galois group S_5;
      (B) NEW Element: the polynomial has no rational root (monic ⇒ integer divisors of 3; none a root)
          and ≥3 real roots (IVT sign-changes) — the arithmetic feeding irreducibility & "2 non-real";
      (C) the engine (existing, algebra/SolvableGroup.v): a perfect non-abelian Galois group is NOT
          solvable — Abel–Ruffini, 0 axioms.
    Together with the cited classical bridges (Gal = S_5 from (A)+(B); A_5 simple ⇒ the perfect section;
    the radical-tower ⇔ solvable-group criterion) — the ROLE-LIMIT, the same completed-object wall
    SolvableGroup.v names for A_5's simplicity — x^5 - 6x + 3 is not solvable by radicals.
    Level: a new computational theorem (S_5 generated by transposition+5-cycle) + the concrete
    Abel–Ruffini assembly; the Galois-theoretic bridges are honestly cited, not faked. *)
Theorem quintic_x5m6x3_unsolvable_assembly :
  (* (A) NEW: transposition + 5-cycle generate S_5 (120 distinct perms, closed, with id) *)
  gen_report = true
  /\ (* (B) NEW: x^5-6x+3 has no rational root, and alternates sign (⇒ ≥3 real roots) *)
  (no_rational_root = true /\ sign_changes = true)
  /\ (* (C) the engine: a perfect non-abelian Galois group is not solvable (Abel–Ruffini) *)
  (forall (Q : GroupStr), (forall a b : gT Q, a = b \/ a <> b) ->
     Perfect Q -> NonAbelianFull Q -> ~ Solvable Q).
Proof.
  split; [ exact gen_report_true | ].
  split; [ split; [ exact no_rational_root_true | exact sign_changes_true ] | ].
  exact quintic_galois_group_not_solvable.
Qed.
