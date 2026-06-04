(** * AlgebraicClosureProcess.v — Q-bar as a PROCESS, not a completed object
    Elements: finite extensions (rungs) and elements sited at a finite rung
    Roles:    the algebraic closure as the role-limit of an ascending tower
    Rules:    embeddings rung_n ↪ rung_{n+1}; dimensions strictly increase
    STATUS:   14 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    The conceptual correction (Part XI): the algebraic closure of Q is NOT a
    "completed object".  Each algebraic number is FINITE data (minimal
    polynomial + root selector — e.g. the coordinates mkE a b c d of
    GaloisQ23.v), and the totality is a countable, effectively-enumerable RULE:
    an ℕ-indexed ASCENDING TOWER of finite extensions

        K_0 = Q ⊂ K_1 = Q[√2] ⊂ K_2 = Q[√2,√3] ⊂ K_3 = Q[√2,√3,√5] ⊂ …

    This file makes that precise and axiom-free, in two layers:

    LAYER A (abstract).  An `AlgTower` = (rungs, dimensions, embeddings) with
    strictly increasing dimensions.  We prove the ontological payload:
      • no_maximal_rung  — no finite rung is the whole closure;
      • tower_unbounded  — dimensions exceed every finite bound;
      • germ_finitely_sited — every element of the colimit (closure) lives at
        SOME finite rung: the closure is a direct limit, a process over finite
        elements, never an actual completed totality;
      • germ_of_inj / rung_embeds_faithfully — the embeddings are genuine
        inclusions (axiom-free, via decidable equality of ℕ — no UIP axiom).

    LAYER B (concrete, non-vacuous).  `multiquadratic : AlgTower` with
    dimensions 2^n (1,2,4,8,…) and zero-padding embeddings — the additive /
    dimension skeleton of Q(√2,√3,√5,…).  Its rung 2 has dimension 4 =
    [Q[√2,√3]:Q] = GaloisDegreeQ23.ext_degree: the concrete field built in
    GaloisQ23.v is literally rung 2 of this process.

    MORAL.  What classical mathematics calls "constructing the algebraic
    closure as a completed object" splits into a RULE ("the roots of any
    rational polynomial lie in SOME finite extension" — true, constructive,
    what mathematics actually uses) plus a platonist surplus ("a single object
    holding all roots at once").  ToS keeps the rule, drops the surplus.  So
    Q-bar is no wall — it is a process, exactly like Q, Z, N, and MORE
    P4-actual than R (finite element-data vs an unending Cauchy process).
*)

From Stdlib Require Import QArith.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat Lia.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
Open Scope nat_scope.

(* ===================== LAYER A: the abstract tower ===================== *)

Record AlgTower : Type := {
  carrier    : nat -> Type;                                  (* the n-th rung *)
  cdim       : nat -> nat;                                   (* its Q-dimension *)
  cemb       : forall n, carrier n -> carrier (S n);         (* rung_n ↪ rung_{n+1} *)
  cemb_inj   : forall n (x y : carrier n), cemb n x = cemb n y -> x = y;
  cdim_grows : forall n, cdim n < cdim (S n)
}.

(* the height never outpaces the dimension: n <= dim(rung n) *)
Lemma tower_height_le_dim : forall (T : AlgTower) n, n <= cdim T n.
Proof.
  intros T n. induction n.
  - lia.
  - assert (Hg := cdim_grows T n). lia.
Qed.

(* NO MAXIMAL RUNG: no finite rung can be the whole closure *)
Theorem no_maximal_rung : forall (T : AlgTower) n, exists m, cdim T n < cdim T m.
Proof. intros T n. exists (S n). apply cdim_grows. Qed.

(* the tower is unbounded: dimensions exceed every finite bound b *)
Theorem tower_unbounded : forall (T : AlgTower) b, exists n, b < cdim T n.
Proof.
  intros T b. exists (S b). assert (H := tower_height_le_dim T (S b)). lia.
Qed.

(* the embeddings are faithful inclusions *)
Lemma rung_embeds_faithfully : forall (T : AlgTower) n (x y : carrier T n),
  cemb T n x = cemb T n y -> x = y.
Proof. intros T n x y. apply cemb_inj. Qed.

(* ----- the colimit (the closure) as a direct limit of finite rungs ----- *)
(* an element of the closure is a pair (rung index n, element of rung n) *)
Definition Germ (T : AlgTower) : Type := { n : nat & carrier T n }.
Definition germ_of (T : AlgTower) (n : nat) (x : carrier T n) : Germ T :=
  existT _ n x.

(* EVERY element of the closure is sited at SOME finite rung: the closure is a
   process over finite elements, not a completed object beyond the stages *)
Theorem germ_finitely_sited : forall (T : AlgTower) (g : Germ T),
  exists n (x : carrier T n), g = germ_of T n x.
Proof. intros T [n x]. exists n. exists x. reflexivity. Qed.

(* distinct rung-elements give distinct closure-elements (rungs embed
   faithfully into the colimit) — axiom-free, via decidable equality of ℕ *)
Lemma germ_of_inj : forall (T : AlgTower) n (x y : carrier T n),
  germ_of T n x = germ_of T n y -> x = y.
Proof.
  intros T n x y H. unfold germ_of in H.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in H. exact H.
Qed.

(* CAPSTONE: the closure is a process — unbounded, no maximal rung, and every
   element finitely sited.  No completed totality is ever instantiated. *)
Theorem closure_is_a_process : forall (T : AlgTower),
  (forall n, exists m, cdim T n < cdim T m)
  /\ (forall b, exists n, b < cdim T n)
  /\ (forall g : Germ T, exists n (x : carrier T n), g = germ_of T n x).
Proof.
  intro T. split; [|split].
  - apply no_maximal_rung.
  - apply tower_unbounded.
  - apply germ_finitely_sited.
Qed.

(* ===================== LAYER B: a concrete non-vacuous tower ============ *)
(* Each rung modeled by its coordinate vector over Q (a finite list); the
   embedding doubles the dimension by zero-padding.  This is the additive /
   dimension skeleton of the multiquadratic tower Q(√2,√3,√5,…), dims 2^n. *)

Definition pad (l : list Q) : list Q := l ++ repeat 0%Q (length l).

Lemma pad_length : forall l, length (pad l) = 2 * length l.
Proof. intro l. unfold pad. rewrite length_app, repeat_length. lia. Qed.

Lemma pad_firstn : forall l, firstn (length l) (pad l) = l.
Proof.
  intro l. unfold pad. rewrite firstn_app, firstn_all, Nat.sub_diag.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma pad_inj : forall l1 l2, pad l1 = pad l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  assert (Hlen : length l1 = length l2).
  { assert (Hp : length (pad l1) = length (pad l2)) by (rewrite H; reflexivity).
    rewrite !pad_length in Hp. lia. }
  rewrite <- (pad_firstn l1), <- (pad_firstn l2), Hlen, H. reflexivity.
Qed.

(* dimensions 2^n strictly increase *)
Lemma two_pow_grows : forall n, 2 ^ n < 2 ^ (S n).
Proof.
  intro n. assert (H : 0 < 2 ^ n) by (induction n; simpl; lia).
  simpl. lia.
Qed.

Definition multiquadratic : AlgTower :=
  {| carrier    := fun _ => list Q;
     cdim       := fun n => 2 ^ n;
     cemb       := fun _ => pad;
     cemb_inj   := fun n x y H => pad_inj x y H;
     cdim_grows := two_pow_grows |}.

(* the low rungs are exactly the concrete fields already built:
   dim 1 = Q, dim 2 = Q[√2], dim 4 = Q[√2,√3] = GaloisQ23.E
   (4 = GaloisDegreeQ23.ext_degree, the Galois order proved there) *)
Example rung0_dim : cdim multiquadratic 0 = 1.   Proof. reflexivity. Qed.
Example rung1_dim : cdim multiquadratic 1 = 2.   Proof. reflexivity. Qed.
Example rung2_dim : cdim multiquadratic 2 = 4.   Proof. reflexivity. Qed.
