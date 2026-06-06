(** * BoundaryDecidability.v — ONE Element/role-limit boundary, THREE faces, ONE diagonal
      Flagship (Phase 1) of the Computer-Science branch.

      THESIS (synthesis+observation, NOT a new theorem):
      The project's Element / role-limit distinction is SECOND-ORDER — it classifies the
      decision-criteria (boundaries) themselves.  A boundary is:
        ElementDrawn   — drawn by a TERMINATING decider (a bool function that is correct);
        RoleLimitDrawn — provably NOT so drawable.
      The SAME negb-diagonal (b <> negb b = circular_dep_is_paradox, Roles.v §XII) is the
      universal obstruction that makes a boundary role-limit-drawn.  We exhibit ONE boundary
      in THREE faces:
        NUMBER  : the discriminant criterion "Δ a perfect square?" is ElementDrawn
                  (decidable via Nat.sqrt — the reduction-atlas dial).            [Element side]
        PROGRAM : the self-halting criterion is RoleLimitDrawn for any self-applicable
                  language (the halting boundary).                                [role-limit side]
        SET     : the boolean-predicate space A->bool is not enumerable (Cantor). [role-limit side]
      The three share one engine: diagonal_defeats_decider / negb_no_fixpoint.

    Reuses (genuine unification, not restatement):
      - cs/HaltingRoleLimit.v : negb_no_fixpoint, cantor_no_surjection, no_halting_decider.
    Cites (Element-side anchor, atlas A):
      - foundation/DiscriminantCompleteEigenvalue.v : rational_eigenvalue_iff_disc_square
        (rational eigenvalue <-> Δ=tr²−4·det a perfect square; decidable for ℤ).
      - stdlib/ReductionAtlasSynthesis.v, foundation/GRQFTDiscriminantBridge.v : Δ=8 (Hadamard),
        Δ=32 (Pell) are role-limits; perfect-square Δ is Element.
      - foundation/SortDecidable.v : the perfect-square decider (is_square) replicated below.

    Elements: discriminants (nat); programs (Prog); boolean predicates (A->bool); deciders Dom->bool
    Roles:    ElementDrawn / RoleLimitDrawn = the STATUS a boundary-criterion acquires (decidable
              by a terminating decider, or not); the decider = role-oracle (Status != Role)
    Rules:    diagonal_defeats_decider (negb has no fixpoint) defeats any decider;
              is_square / Nat.sqrt is the terminating rule drawing the Element boundary

    ============ E/R/R разбор ============
      Rules (L5): diagonal_defeats_decider — универсальное правило: если у домена для КАЖДОГО
                  кандидата-решателя есть само-отрицающий диагональный элемент, решателя нет
                  (ядро = b <> negb b).  is_square = терминирующее правило (Nat.sqrt), рисующее
                  Element-границу.
      Roles (L4): ElementDrawn vs RoleLimitDrawn — СТАТУС критерия-границы (разрешим терминирующим
                  решателем или нет).  Решатель — роль-оракул.  Status != Role.
      Elements  : три домена (дискриминанты / программы / булевы предикаты) и сами решатели.
    ДИАГНОСТИКА (P4): граница Element-проведена, когда её рисует ТЕРМИНИРУЮЩИЙ процесс (дискриминант
      через Nat.sqrt); role-limit-проведена, когда лишь завершённый/само-применимый процесс
      (halting, несчётность).  Реифицировать role-limit-границу как Element = категориальная
      ошибка.  ОДНА negb-диагональ — обструкция в программе (halting) и во множестве (Кантор);
      дискриминант — Element-сторона.  Честно: синтез+наблюдение (три классических результата
      переиспользуются), универсальность поинстансна, не мета-теорема.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import PeanoNat Bool.
From ToS Require Import cs.HaltingRoleLimit.

(* ===================================================================== *)
(*  THE META-BOUNDARY: is a boundary drawn by a terminating decider?      *)
(* ===================================================================== *)

(** A boundary [Side] on a domain [Dom] is ELEMENT-DRAWN if some terminating
    boolean decider is correct for it. *)
Definition ElementDrawn {Dom : Type} (Side : Dom -> Prop) : Prop :=
  exists dec : Dom -> bool, forall x, dec x = true <-> Side x.

(** It is ROLE-LIMIT-DRAWN if no such decider exists. *)
Definition RoleLimitDrawn {Dom : Type} (Side : Dom -> Prop) : Prop :=
  ~ ElementDrawn Side.

(** An Element-drawn boundary is (logically) decidable: its status is determinate. *)
Lemma element_drawn_implies_decidable :
  forall (Dom : Type) (Side : Dom -> Prop),
    ElementDrawn Side -> forall x, Side x \/ ~ Side x.
Proof.
  intros Dom Side [dec H] x. destruct (dec x) eqn:E.
  - left. apply (proj1 (H x)). exact E.
  - right. intro HS. apply (proj2 (H x)) in HS. rewrite E in HS. discriminate.
Qed.

(** ★ THE UNIVERSAL ENGINE: a self-negating diagonal against EVERY candidate decider
    forces the boundary to be role-limit-drawn.  This is the shared core of the halting
    boundary and Cantor's theorem — built on negb_no_fixpoint (Roles.v §XII). *)
Theorem diagonal_defeats_decider :
  forall (Dom : Type) (Side : Dom -> Prop),
    (forall dec : Dom -> bool, exists d, Side d <-> dec d = false) ->
    RoleLimitDrawn Side.
Proof.
  intros Dom Side Hdiag [dec Hdec].
  destruct (Hdiag dec) as [d Hd].
  (* Hdec d : dec d = true <-> Side d ;  Hd : Side d <-> dec d = false *)
  destruct (Bool.bool_dec (dec d) true) as [Et | Ef].
  - assert (Side d) as HS by (apply (proj1 (Hdec d)); exact Et).
    apply (proj1 Hd) in HS. rewrite Et in HS. discriminate.
  - apply Bool.not_true_is_false in Ef.
    assert (Side d) as HS by (apply (proj2 Hd); exact Ef).
    apply (proj2 (Hdec d)) in HS. rewrite Ef in HS. discriminate.
Qed.

(* ===================================================================== *)
(*  FACE 1 — NUMBER: the discriminant boundary is ELEMENT-drawn            *)
(*                                                                         *)
(*  d is the discriminant Δ = tr²−4·det of a 2×2 (reduction atlas A).      *)
(*  "Δ a perfect square" <-> rational eigenvalue <-> Element               *)
(*  (foundation/DiscriminantCompleteEigenvalue.v).  The criterion is drawn *)
(*  by a TERMINATING process — Nat.sqrt.                                   *)
(* ===================================================================== *)

(** Perfect-square decider (replicated from foundation/SortDecidable.v). *)
Definition is_square (n : nat) : bool := Nat.eqb (Nat.sqrt n * Nat.sqrt n) n.

Lemma is_square_iff : forall n, is_square n = true <-> exists r, r * r = n.
Proof.
  intro n. unfold is_square. split.
  - intro H. apply Nat.eqb_eq in H. exists (Nat.sqrt n). exact H.
  - intros [r Hr]. apply Nat.eqb_eq. rewrite <- Hr, Nat.sqrt_square. reflexivity.
Qed.

(** The Element side of the discriminant boundary: Δ has an integer square root. *)
Definition rational_split (d : nat) : Prop := exists r, r * r = d.

Theorem discriminant_element_drawn : ElementDrawn rational_split.
Proof. exists is_square. intro d. exact (is_square_iff d). Qed.

(** Concrete atlas instances: Δ=8 (Hadamard), Δ=32 (Pell) are role-limits (√2);
    a perfect-square Δ=9 is Element. *)
Example disc_hadamard_role_limit : is_square 8 = false.  Proof. reflexivity. Qed.
Example disc_pell_role_limit     : is_square 32 = false. Proof. reflexivity. Qed.
Example disc_rational_element    : is_square 9 = true.   Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  FACE 2 — PROGRAM: the self-halting boundary is ROLE-LIMIT-drawn        *)
(*                                                                         *)
(*  For any self-applicable language (the diagonal program exists against  *)
(*  every candidate decider), the halting boundary cannot be drawn by a    *)
(*  terminating decider.  Same engine as cs/HaltingRoleLimit.no_halting_   *)
(*  decider, here as an instance of diagonal_defeats_decider.              *)
(* ===================================================================== *)

Theorem halting_role_limit_drawn :
  forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
    (forall dec : Prog -> bool, exists diag, Halts diag diag <-> dec diag = false) ->
    RoleLimitDrawn (fun q : Prog => Halts q q).
Proof.
  intros Prog Halts Hself. apply diagonal_defeats_decider. exact Hself.
Qed.

(* ===================================================================== *)
(*  SYNTHESIS — one boundary, three faces, one diagonal                    *)
(* ===================================================================== *)

(** ★ The capstone: the SAME negb-diagonal underlies all three.  FACE 3 (SET) is
    cantor_no_surjection (cs/HaltingRoleLimit.v): the predicate space A->bool is not
    enumerable — uncountability as a RULE, role-limit-drawn. *)
Theorem one_boundary_three_faces :
  (* shared engine: negation has no fixed point *)
  (forall b : bool, b <> negb b)
  (* NUMBER: discriminant boundary is Element-drawn (decidable) *)
  /\ ElementDrawn rational_split
  (* PROGRAM: self-halting boundary is role-limit-drawn (no decider), given self-application *)
  /\ (forall (Prog : Type) (Halts : Prog -> Prog -> Prop),
        (forall dec : Prog -> bool, exists diag, Halts diag diag <-> dec diag = false) ->
        RoleLimitDrawn (fun q => Halts q q))
  (* SET: boolean-predicate space is not enumerable (Cantor) *)
  /\ (forall (A : Type) (g : A -> (A -> bool)), ~ (forall f, exists a, g a = f)).
Proof.
  repeat split.
  - exact negb_no_fixpoint.
  - exact discriminant_element_drawn.
  - exact halting_role_limit_drawn.
  - exact cantor_no_surjection.
Qed.

(** Computability = the project's finitization boundary, made algorithmic and self-aware:
    some boundaries (discriminant) a terminating process draws; some (halting, Cantor) only
    the completed/self-applicable process would — and the ONE diagonal marks exactly which. *)

Print Assumptions diagonal_defeats_decider.
Print Assumptions one_boundary_three_faces.
