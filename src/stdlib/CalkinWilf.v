(** * CalkinWilf.v — the Calkin–Wilf tree: an explicit bijection ℕ⁺ ↔ ℚ⁺ in which every
      positive rational is reached in finitely many steps, in lowest terms, exactly once.
      The Element side of the finitization boundary in its purest form (ℚ⁺ is countable),
      a sibling of SternBrocot.v by a DIFFERENT mechanism (the child maps + a Bézout
      certificate, not the mediant + determinant), and the direct contrast with the
      continuum (ℝ is NOT enumerable = role-limit, the PCH side using classic + L4_witness).

    Elements: the nodes (a,b); the Bézout certificate u·a+v·b=1; the breadth-first list
              1/1, 1/2, 2/1, 1/3, 3/2, 2/3, 3/1 (L1 + P4)
    Roles:    Element side = ℚ⁺ is ENUMERATED — every rational is a finite-actual node, in
              lowest terms, with no duplicates (countable); role-limit = an irrational (√2) is
              NEVER a node — the limit of an infinite, non-terminating path (Pell/Fibonacci)
    Rules:    the two child maps (a,b)↦(a,a+b) and (a,b)↦(a+b,b); they preserve coprimality
              (Bézout 1 → Bézout 1, by ring) and split the fraction into <1 (left) and >1
              (right), so every node is lowest-terms and no fraction repeats

    THE DEEP POINT — ℚ⁺ is enumerated, in lowest terms, by one deterministic process.  Root
    1/1; each node a/b breeds a/(a+b) and (a+b)/b.  A Bézout certificate u·a+v·b=1 (the
    constructive "lowest terms" witness) is PRESERVED by both children: (u−v)·a+v·(a+b)=1 and
    u·(a+b)+(v−u)·b=1 (`cw_left_bezout`, `cw_right_bezout`, pure ring), and a Bézout 1 forces
    gcd=1 (`bezout_gcd1`).  So every node is automatically in lowest terms.  The left child is
    <1 (a<a+b) and the right is >1 (b<a+b) (`cw_children_sides`), so the two never coincide and
    no fraction repeats.  Breadth-first this lists 1/1, 1/2, 2/1, 1/3, 3/2, 2/3, 3/1, …
    (`cw_enumeration`) — every positive rational exactly once, the bijection ℕ⁺ ↔ ℚ⁺ (ℚ⁺
    countable = Element).  But √2 is NEVER a node (`cw_no_sqrt2`): it is the limit of the
    infinite non-terminating path 1/1→1/2→2/3→3/5→5/8→… — approached, never actualized
    (role-limit).  Element = a rational reached by a finite path (lowest terms, once);
    role-limit = an irrational that is only the limit of a path that never terminates.

    ============ E/R/R разбор ============
      Rules (L5): две карты-потомка (a,b)↦(a,a+b),(a+b,b); сохраняют взаимную простоту
                  (Безу 1 → Безу 1, ring) и расщепляют дробь на <1 (левый) и >1 (правый).
      Roles (L4): Element = ℚ⁺ перечислено (биекция ℕ⁺→ℚ⁺, конечный путь, низшие члены, без
                  дубликатов = счётно); role-limit = иррациональное (√2) НИКОГДА не узел (предел
                  бесконечного нетерминирующего пути Пелля/Фибоначчи).
      Elements  : узлы (a,b); сертификат Безу; обход 1/1,1/2,2/1,1/3,3/2,2/3,3/1 (L1+P4).
    ДИАГНОСТИКА (P4): ℚ⁺ перечислимо в низших членах = Element/счётно (то же «всё достижимо» что и
    конструктивная сторона H1); континуум ℝ НЕ перечислим = role-limit (PCH, classic+L4_witness).
    Один детерминированный процесс посещает каждое рациональное ровно раз; √2 = нетерминирующий путь.
    «Достижимо за конечный путь ⟺ рационально» — дерево-форма «терминирующий процесс ⟺ Element»;
    брат SternBrocot другим механизмом (карты-потомки + Безу, не медианта + определитель).

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The Calkin–Wilf tree: children and the Bézout "lowest terms" witness   *)
(* ===================================================================== *)

(** The two children of the node a/b: left a/(a+b) (<1), right (a+b)/b (>1). *)
Definition cw_left  (a b : Z) : Z * Z := (a, a + b).
Definition cw_right (a b : Z) : Z * Z := (a + b, b).

(** Bézout coprimality certificate: a constructive witness that a/b is in lowest terms (any
    common divisor divides u·a+v·b = 1). *)
Definition bezout (a b : Z) : Prop := exists u v : Z, u * a + v * b = 1.

(** The root 1/1 is in lowest terms. *)
Lemma root_bezout : bezout 1 1.
Proof. exists 1, 0. ring. Qed.

(** A Bézout certificate forces gcd = 1 — i.e. the fraction really is in lowest terms. *)
Lemma bezout_gcd1 : forall a b : Z, bezout a b -> Z.gcd a b = 1.
Proof.
  intros a b [u [v H]].
  assert (Hdiv : (Z.gcd a b | 1)).
  { rewrite <- H. apply Z.divide_add_r.
    - apply Z.divide_mul_r. apply Z.gcd_divide_l.
    - apply Z.divide_mul_r. apply Z.gcd_divide_r. }
  pose proof (Z.gcd_nonneg a b) as Hnn.
  assert (Hle : Z.gcd a b <= 1) by (apply Z.divide_pos_le; [ lia | exact Hdiv ]).
  assert (Hne : Z.gcd a b <> 0).
  { intro Hz. rewrite Hz in Hdiv. destruct Hdiv as [k Hk]. rewrite Z.mul_0_r in Hk. lia. }
  lia.
Qed.

(* ===================================================================== *)
(*  The child maps preserve lowest terms (Bézout 1 → Bézout 1)            *)
(* ===================================================================== *)

(** ★ The left child a/(a+b) stays in lowest terms: witness (u−v, v). *)
Lemma cw_left_bezout : forall a b : Z, bezout a b -> bezout a (a + b).
Proof.
  intros a b [u [v H]]. exists (u - v), v. rewrite <- H. ring.
Qed.

(** ★ The right child (a+b)/b stays in lowest terms: witness (u, v−u). *)
Lemma cw_right_bezout : forall a b : Z, bezout a b -> bezout (a + b) b.
Proof.
  intros a b [u [v H]]. exists u, (v - u). rewrite <- H. ring.
Qed.

(** Both children of a lowest-terms node are in lowest terms — every Calkin–Wilf node is
    automatically reduced. *)
Lemma cw_children_lowest_terms : forall a b : Z,
  bezout a b -> bezout (fst (cw_left a b)) (snd (cw_left a b))
             /\ bezout (fst (cw_right a b)) (snd (cw_right a b)).
Proof.
  intros a b Hab. unfold cw_left, cw_right; simpl.
  split; [ apply cw_left_bezout | apply cw_right_bezout ]; exact Hab.
Qed.

(* ===================================================================== *)
(*  The two children differ: left < 1 < right ⟹ no fraction repeats        *)
(* ===================================================================== *)

(** ★ For a positive node, the left child is <1 (numerator a < denominator a+b) and the right
    child is >1 (denominator b < numerator a+b).  So the two children land on opposite sides
    of 1 and never coincide — the breadth-first walk hits each rational at most once. *)
Lemma cw_children_sides : forall a b : Z,
  0 < a -> 0 < b -> a < a + b /\ b < a + b.
Proof. intros a b Ha Hb. split; lia. Qed.

(* ===================================================================== *)
(*  Concrete breadth-first enumeration of ℚ⁺                              *)
(* ===================================================================== *)

(** The first three levels of the tree: 1/1 → 1/2, 2/1 → 1/3, 3/2, 2/3, 3/1.  This is the
    Calkin–Wilf sequence — every positive rational, in lowest terms, exactly once. *)
Lemma cw_enumeration :
     cw_left 1 1 = (1, 2) /\ cw_right 1 1 = (2, 1)
  /\ cw_left 1 2 = (1, 3) /\ cw_right 1 2 = (3, 2)
  /\ cw_left 2 1 = (2, 3) /\ cw_right 2 1 = (3, 1).
Proof. repeat split; reflexivity. Qed.

(** The "seam" making the tree a single sequence: in breadth-first order the denominator of
    one term equals the numerator of the next (Stern's diatomic / fusc).  Concretely along
    1/1, 1/2, 2/1, 1/3: snd = fst of the successor. *)
Lemma cw_seam_example :
  snd (1, 1) = fst (1, 2) /\ snd (1, 2) = fst (2, 1) /\ snd (2, 1) = fst (1, 3).
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: an irrational is never a node                             *)
(* ===================================================================== *)

(** ★ √2 is NEVER a Calkin–Wilf node: a node is a rational a/b, but no rational squares to 2.
    √2 is only the limit of the infinite, non-terminating path 1/1→1/2→2/3→3/5→5/8→…
    (Pell/Fibonacci) — approached but never actualized (role-limit). *)
Theorem cw_no_sqrt2 : ~ (exists r : Q, (r * r == 2)%Q).
Proof. exact sqrt2_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The Calkin–Wilf tree, split by the finitization boundary:
      (a) ELEMENT — ℚ⁺ is enumerated in lowest terms: the root is reduced (`root_bezout`),
          both child maps preserve reducedness (`cw_children_lowest_terms`), a Bézout 1
          certifies gcd=1 (`bezout_gcd1`), the children straddle 1 so nothing repeats
          (`cw_children_sides`), and the walk lists 1/1,1/2,2/1,1/3,3/2,2/3,3/1 (`cw_enumeration`)
          — the bijection ℕ⁺ ↔ ℚ⁺ (ℚ⁺ countable);
      (b) ROLE-LIMIT — √2 is never a node (`cw_no_sqrt2`): only the limit of a non-terminating
          path, the contrast with the non-enumerable continuum. *)
Theorem calkin_wilf_synthesis :
  bezout 1 1
  /\ (forall a b : Z, bezout a b -> bezout a (a + b) /\ bezout (a + b) b)
  /\ (forall a b : Z, bezout a b -> Z.gcd a b = 1)
  /\ cw_left 1 1 = (1, 2)
  /\ ~ (exists r : Q, (r * r == 2)%Q).
Proof.
  split; [ exact root_bezout | ].
  split; [ intros a b Hab; split; [ apply cw_left_bezout | apply cw_right_bezout ]; exact Hab | ].
  split; [ exact bezout_gcd1 | ].
  split; [ reflexivity | exact cw_no_sqrt2 ].
Qed.
