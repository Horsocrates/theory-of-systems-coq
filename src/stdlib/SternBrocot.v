(** * SternBrocot.v — the Stern–Brocot / Farey tree as the Element-side ENUMERATION of
      ℚ⁺.  Every positive rational is reached by exactly one FINITE (terminating) path
      of mediants from the seeds 0/1 and 1/0 — a constructive witness of the
      countability of ℚ.  The unimodular invariant p'q − pq' = 1 (preserved by the
      mediant) is the SAME determinant ±1 carried by ContinuedFractions.v (there between
      consecutive convergents, here between tree neighbours), and it makes every node
      automatically lowest-terms.  The irrationals are the INFINITE paths — the boundary,
      role-limits, never nodes.

    Elements: the integers p, q; the concrete nodes 1/1, 1/2, 2/1, 1/3, 2/3, 3/2, 3/1
              (each finite, actual, in lowest terms — L1 + P4)
    Roles:    the tree = the Element-side COMPLETE non-redundant enumeration of ℚ⁺ (each
              rational a unique terminating path — countability of ℚ made constructive);
              an irrational = an INFINITE path (the boundary, a role-limit, never a node);
              the unimodular invariant p'q−pq'=1 (preserved by the mediant) = the witness
              that every node is lowest-terms, and the same ±1 of ContinuedFractions.v
    Rules:    the mediant (a+c)/(b+d); the unimodular determinant p'q−pq'=1; a path to a
              rational IS its continued fraction (Stern–Brocot ↔ continued fraction)

    THE DEEP POINT — the Stern–Brocot tree is the Element side made flesh: the
    countability of ℚ⁺ IS the fact that every rational has a unique FINITE path of
    mediants (this file proves the structural invariants of that tree), while the
    continuum is the boundary of INFINITE paths.  This ties H1 (finitization =
    constructivity) to CARDINALITY: the Element side is enumerable (a tree of terminating
    paths); the role-limit side is the uncountable boundary of non-terminating paths.
      · `mediant_det_left/right`, `unimodular_preserved`: the determinant p'q−pq'=1 is
        preserved by every mediant step — the whole tree is unimodular.  This is the
        SAME ±1 invariant as ContinuedFractions.cf_det (a Stern–Brocot path is a CF).
      · `mediant_lowest_terms`: unimodularity ⟹ every node is automatically in lowest
        terms (any common divisor of numerator and denominator divides 1).
      · `mediant_between_left/right`: the mediant lies strictly between its parents — the
        in-order tree is sorted, a genuine enumeration of ℚ⁺ in increasing order.
      · `sb_node_never_sqrt2`: every node is rational, so NO node is √2 (`no_rational_
        sqrt2`) — √2 is the infinite-path boundary, a role-limit, never an Element node.

    ============ E/R/R разбор ============
      Rules (L5): медианта (a+c)/(b+d); унимодулярный детерминант p'q−pq'=1; путь к
                  рациональному = его цепная дробь.
      Roles (L4): дерево = Element-сторонняя ПОЛНАЯ неизбыточная энумерация ℚ⁺ (счётность
                  конструктивно); иррациональное = бесконечный путь (граница, role-limit,
                  не узел); инвариант p'q−pq'=1 = гарант несократимости + тот же ±1 цепных дробей.
      Elements  : целые p,q; узлы 1/1,1/2,2/1,1/3,2/3,3/2,3/1 (конечны, несократимы, L1+P4).
    ДИАГНОСТИКА (P4): счётность ℚ ⟺ терминирующие пути; континуум ⟺ бесконечно-путевая граница;
    Element-сторона энумерируема (дерево), role-limit-сторона — несчётная граница; тот же
    унимодулярный детерминант ±1, что в ContinuedFractions; √2 = бесконечный путь, не узел.

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The mediant and the unimodular determinant                            *)
(* ===================================================================== *)

(** The mediant of p/q and p'/q' is (p+p')/(q+q'). *)
Definition mediant (p q p' q' : Z) : Z * Z := (p + p', q + q').

(** The 2×2 determinant of the neighbour pair p/q, p'/q'.  Stern–Brocot / Farey
    neighbours satisfy det2 = 1 (unimodularity). *)
Definition det2 (p q p' q' : Z) : Z := p' * q - p * q'.

(* ===================================================================== *)
(*  Unimodularity is preserved by the mediant (the determinant invariant) *)
(* ===================================================================== *)

(** The determinant of (p/q, mediant) equals the determinant of (p/q, p'/q'). *)
Lemma mediant_det_left : forall p q p' q',
  det2 p q (p + p') (q + q') = det2 p q p' q'.
Proof. intros. unfold det2. ring. Qed.

(** The determinant of (mediant, p'/q') equals the determinant of (p/q, p'/q'). *)
Lemma mediant_det_right : forall p q p' q',
  det2 (p + p') (q + q') p' q' = det2 p q p' q'.
Proof. intros. unfold det2. ring. Qed.

(** ★ The unimodular invariant p'q − pq' = 1 is preserved by the mediant on BOTH sides —
    so the whole Stern–Brocot tree is unimodular.  This is the SAME ±1 determinant that
    ContinuedFractions.cf_det carries between consecutive convergents. *)
Lemma unimodular_preserved : forall p q p' q', det2 p q p' q' = 1 ->
  det2 p q (p + p') (q + q') = 1 /\ det2 (p + p') (q + q') p' q' = 1.
Proof.
  intros p q p' q' H. split.
  - rewrite mediant_det_left. exact H.
  - rewrite mediant_det_right. exact H.
Qed.

(* ===================================================================== *)
(*  The mediant lies strictly between its parents (sorted enumeration)    *)
(* ===================================================================== *)

(** p/q < mediant when p/q < p'/q' (cross-multiplied, positive denominators). *)
Lemma mediant_between_left : forall a b c d : Z,
  0 < b -> 0 < d -> a * d < c * b -> a * (b + d) < (a + c) * b.
Proof. intros a b c d Hb Hd H. nia. Qed.

(** mediant < p'/q' likewise. *)
Lemma mediant_between_right : forall a b c d : Z,
  0 < b -> 0 < d -> a * d < c * b -> (a + c) * d < c * (b + d).
Proof. intros a b c d Hb Hd H. nia. Qed.

(* ===================================================================== *)
(*  Unimodularity ⟹ every node is in lowest terms                         *)
(* ===================================================================== *)

(** The explicit Bézout combination behind lowest-terms: q·(p+p') − p·(q+q') = 1. *)
Lemma mediant_bezout : forall p q p' q', det2 p q p' q' = 1 ->
  q * (p + p') - p * (q + q') = 1.
Proof. intros p q p' q' H. unfold det2 in H. nia. Qed.

(** ★ Lowest terms: if the neighbour determinant is 1, any common divisor of the
    mediant's numerator and denominator divides 1 — so the mediant is automatically in
    lowest terms.  Every Stern–Brocot node is a reduced fraction, for free. *)
Lemma mediant_lowest_terms : forall p q p' q' g, det2 p q p' q' = 1 ->
  (g | (p + p')) -> (g | (q + q')) -> (g | 1).
Proof.
  intros p q p' q' g H [k Hk] [l Hl].
  exists (q * k - p * l).
  pose proof (mediant_bezout p q p' q' H) as Hb.
  rewrite Hk, Hl in Hb. nia.
Qed.

(* ===================================================================== *)
(*  Concrete nodes (the top of the tree)                                  *)
(* ===================================================================== *)

(** The seed boundaries 0/1 and 1/0 are unimodular. *)
Lemma sb_seed_unimodular : det2 0 1 1 0 = 1.
Proof. reflexivity. Qed.

(** The root of the tree is 1/1 = mediant(0/1, 1/0). *)
Lemma sb_root : mediant 0 1 1 0 = (1, 1).
Proof. reflexivity. Qed.

(** Its left child 1/2 = mediant(0/1, 1/1). *)
Lemma sb_left_child : mediant 0 1 1 1 = (1, 2).
Proof. reflexivity. Qed.

(** Its right child 2/1 = mediant(1/1, 1/0). *)
Lemma sb_right_child : mediant 1 1 1 0 = (2, 1).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit side: √2 is an infinite path, never a node                 *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ Every Stern–Brocot node is a rational p/q, and no rational squares to 2
    (`no_rational_sqrt2`) — so NO node is √2.  √2 is the infinite-path boundary of the
    tree, a role-limit, reached by no finite path / Element node. *)
Theorem sb_node_never_sqrt2 : forall p q : Z,
  ~ ((inject_Z p / inject_Z q) * (inject_Z p / inject_Z q) == 2).
Proof. intros p q. apply no_rational_sqrt2. Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The Stern–Brocot tree as the Element-side enumeration of ℚ⁺, in one statement:
      (a) the unimodular determinant p'q−pq'=1 is preserved by every mediant step;
      (b) the mediant lies strictly between its parents (the tree is sorted);
      (c) unimodularity ⟹ every node is in lowest terms;
      (d) no node is √2 — the role-limit is the infinite-path boundary, never an Element. *)
Theorem stern_brocot_synthesis :
  (forall p q p' q', (det2 p q p' q' = 1)%Z ->
     ((det2 p q (p + p') (q + q') = 1)%Z /\ (det2 (p + p') (q + q') p' q' = 1)%Z))
  /\ (forall a b c d : Z, (0 < b)%Z -> (0 < d)%Z -> (a * d < c * b)%Z ->
        ((a * (b + d) < (a + c) * b)%Z /\ ((a + c) * d < c * (b + d))%Z))
  /\ (forall p q p' q' g : Z, (det2 p q p' q' = 1)%Z ->
        (g | (p + p'))%Z -> (g | (q + q'))%Z -> (g | 1)%Z)
  /\ (forall p q : Z, ~ ((inject_Z p / inject_Z q) * (inject_Z p / inject_Z q) == 2)).
Proof.
  split; [ exact unimodular_preserved | ].
  split.
  - intros a b c d Hb Hd Hlt. split;
    [ apply mediant_between_left | apply mediant_between_right ]; assumption.
  - split; [ exact mediant_lowest_terms | exact sb_node_never_sqrt2 ].
Qed.
