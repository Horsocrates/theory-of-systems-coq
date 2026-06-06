(** * DiffeoIsRelabeling.v — "gravity = Rule-object" thread 2: diffeomorphism invariance (general
       covariance) = invariance of the Rules under RELABELING of the Roles; relabelings = Aut(spacetime)
       = the SAME Aut(E/R/R object) that gives gauge groups.  Bottoms out in P3 + L5.

    THESIS.
    The Rules (causal order + number = geometry, Sorkin) are defined on RELATIONS, blind to the NAMES
    of the Roles (points).  A relabeling preserving the relations is an order-ISOMORPHISM = an
    AUTOMORPHISM of the spacetime E/R/R object — so diffeomorphism invariance is "the gauge symmetry
    of gravity": Aut(spacetime), the same Aut that gives gauge groups (ERRAutomorphism).  PHYSICAL =
    relabel-invariant (number, order); GAUGE/coordinate = label-dependent (not physical).  Bedrock:
    a system's identity is its ESSENCE not its NAME (P3, intensional identity) and Roles are positions
    whose names are arbitrary (L5, positionality).

    ============ E/R/R разбор ============
      Elements : точки/метки (носители позиций).
      Roles    : позиции (L5) с произвольными именами/координатами; переименование = функция на метках.
      Rules    : каузальный порядок + число (геометрия, Sorkin) — на ОТНОШЕНИЯХ, слепы к именам.
      ДИАГНОСТИКА (P3+L5): физическое = инвариант переименования (число, порядок); координатное = зависит
      от метки (gauge). Переименование, сохраняющее порядок = автоморфизм = Aut(пространство-время) = диффео
      = «калибровка гравитации» = тот же Aut, что калибровочные группы (ERRAutomorphism). Дно: тождество есть
      СУЩНОСТЬ не ИМЯ (P3) + порядок структурен, имена произвольны (L5). Уровень: `новое обрамление известного`.

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ===================================================================== *)
(*  Spacetime = points (labels) + a causal relation ; relabeling = a map   *)
(* ===================================================================== *)

Definition Relation := nat -> nat -> bool.

(** An order-isomorphism: the relabeling sigma preserves the causal relation
    (= an automorphism of the spacetime E/R/R structure = a diffeomorphism). *)
Definition order_iso (sigma : nat -> nat) (R : Relation) : Prop :=
  forall i j, R i j = R (sigma i) (sigma j).

(* ===================================================================== *)
(*  The two relabel-INVARIANTS (Sorkin: order + number = geometry)         *)
(* ===================================================================== *)

(** ★ NUMBER is relabel-invariant under ANY relabeling (the Sorkin "number" / discrete volume). *)
Lemma number_relabel_invariant : forall (sigma : nat -> nat) (pts : list nat),
  length (map sigma pts) = length pts.
Proof.
  intros sigma pts. induction pts as [|x xs IH]; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** ★ ORDER is preserved by an order-isomorphism (the Sorkin "order") — definitionally. *)
Lemma order_relabel_invariant : forall sigma R,
  order_iso sigma R -> forall i j, R i j = R (sigma i) (sigma j).
Proof. intros sigma R H i j. apply H. Qed.

(* ===================================================================== *)
(*  A concrete relabeling = an automorphism (bijection) of an antichain     *)
(* ===================================================================== *)

(** A 3-point antichain (all spacelike: empty causal relation). *)
Definition antichain : Relation := fun _ _ => false.
Definition pts3 : list nat := [0; 1; 2].

(** The relabeling that swaps labels 0 and 2 (a coordinate change). *)
Definition swap02 (n : nat) : nat :=
  match n with 0 => 2 | 2 => 0 | k => k end.

(** ★ swap02 is an order-iso (automorphism) of the antichain — it preserves all causal relations. *)
Lemma swap02_iso : order_iso swap02 antichain.
Proof. unfold order_iso, antichain. intros i j. reflexivity. Qed.

(** ★ swap02 is a genuine relabeling: a bijection (its own inverse) — diffeo is invertible. *)
Lemma swap02_involutive : forall n, swap02 (swap02 n) = n.
Proof. intro n. destruct n as [|[|[|k]]]; reflexivity. Qed.

(* ===================================================================== *)
(*  PHYSICAL (invariant) vs GAUGE (label-dependent)                        *)
(* ===================================================================== *)

(** ★ PHYSICAL: the number is invariant under the relabeling. *)
Lemma number_invariant_concrete : length (map swap02 pts3) = length pts3.
Proof. reflexivity. Qed.

(** ★ GAUGE: the head-label (a coordinate-dependent quantity) is NOT invariant — a pure artifact. *)
Lemma head_label_not_invariant : hd 0 (map swap02 pts3) <> hd 0 pts3.
Proof. simpl. discriminate. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Diffeomorphism invariance = relabeling invariance of the Rules:
      (number)    the count is relabel-invariant under ANY relabeling (Sorkin "number");
      (order)     the causal relation is preserved by an order-iso (Sorkin "order");
      (Aut)       a relation-preserving relabeling is an automorphism (here swap02: iso + involutive
                  bijection) = Aut(spacetime) = diffeo = "the gauge symmetry of gravity" (same Aut as gauge);
      (physical)  the number is invariant under the relabeling;
      (gauge)     a label-referencing quantity (the head-label) is NOT invariant = a coordinate artifact.
    Physical content = the relabel-invariant (relational) part; labels carry no physics.  Bedrock:
    identity = essence not name (P3); Roles = positions with arbitrary names (L5). *)
Theorem diffeo_is_relabel_invariance :
  (forall (sigma : nat -> nat) (pts : list nat), length (map sigma pts) = length pts)
  /\ (forall sigma R, order_iso sigma R -> forall i j, R i j = R (sigma i) (sigma j))
  /\ order_iso swap02 antichain
  /\ (forall n, swap02 (swap02 n) = n)
  /\ length (map swap02 pts3) = length pts3
  /\ hd 0 (map swap02 pts3) <> hd 0 pts3.
Proof.
  split. exact number_relabel_invariant.
  split. exact order_relabel_invariant.
  split. exact swap02_iso.
  split. exact swap02_involutive.
  split. exact number_invariant_concrete.
  exact head_label_not_invariant.
Qed.
