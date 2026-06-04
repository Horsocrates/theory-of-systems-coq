(** * DiscreteGeodesic.v — the geodesic as the SHORTEST discrete path (limit of paths)
    Elements: rational points (Q²) and finite paths (lists of points); path length ∈ Q
    Roles:    the geodesic as the role-EXTREMAL — the shortest discrete path / its infimum
    Rules:    triangle inequality (a detour never shortens); length ≥ endpoint distance
    STATUS:   13 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Closes the one borderline of Part XII: the thesis calls a geodesic "the role-
    extremal — the LIMIT OF DISCRETE PATHS", but the existing geodesic file
    (process/ProcessGeodesic.v) covers the ORBITAL side (Schwarzschild/ISCO/Kepler),
    not "shortest path". This file is the Element-side of THAT phrase, over ℚ:

      • a path is a finite list of rational points; its length `plen` is the sum of
        successive distances (FINITE rational data — no limits, no calculus);
      • the TRIANGLE INEQUALITY (`d1_triangle`) is the geodesic RULE: a detour through
        a third point never shortens;
      • ★ `plen_ge`: EVERY discrete path from a to b has length ≥ d(a,b) — the direct
        distance is the INFIMUM of discrete path lengths (the geodesic = role-extremal);
      • ★ `straight_is_shortest`: the direct two-point path attains it — the straight
        segment IS a shortest path (a geodesic);
      • ★ `geodesic_insert`: inserting an on-segment point does not change the length —
        the geodesic length is STABLE under refinement = the limit of discrete paths.

    The metric is the L¹ (taxicab) distance d₁((x,y),(x',y')) = |x−x'|+|y−y'|, which is
    RATIONAL (Qabs) and genuinely satisfies the triangle inequality. So "geodesic =
    shortest discrete path = infimum/limit of discrete path lengths" is realized
    entirely over ℚ, 0 axioms.

    HONEST SCOPE: the EUCLIDEAN length needs √ (role-limit), so we use the rational L¹
    metric; in L¹ geodesics are NOT unique (any monotone staircase is shortest) — an
    honest feature, not a bug. The smooth Riemannian geodesic over ℝ is the continuum
    role-limit (cf. Часть X). RELATED (existing repo): orbital geodesics in
    process/ProcessGeodesic.v; graph shortest-path distance in process/ProcessP3Metric.v.
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Q_scope.

Definition Point : Set := (Q * Q)%type.

(* L¹ (taxicab) distance — rational, no square roots *)
Definition d1 (p q : Point) : Q :=
  Qabs (fst p - fst q) + Qabs (snd p - snd q).

(* length of a discrete path a → l (l = the remaining points) *)
Fixpoint plen (a : Point) (l : list Point) : Q :=
  match l with
  | [] => 0
  | p :: l' => d1 a p + plen p l'
  end.

(* the endpoint of the path a → l (exact; = a if l is empty) *)
Fixpoint pend (a : Point) (l : list Point) : Point :=
  match l with [] => a | p :: l' => pend p l' end.

(* ===================== scalar helpers on Qabs ===================== *)
Lemma qabs_sub_triangle : forall x y z : Q,
  Qabs (x - z) <= Qabs (x - y) + Qabs (y - z).
Proof.
  intros x y z. assert (E : x - z == (x - y) + (y - z)) by ring.
  rewrite E. apply Qabs_triangle.
Qed.

Lemma qabs_sub_sym : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b. assert (E : a - b == -(b - a)) by ring.
  rewrite E. apply Qabs_opp.
Qed.

(* ===================== L¹ is a genuine metric ===================== *)
Lemma d1_nonneg : forall p q, 0 <= d1 p q.
Proof.
  intros p q. unfold d1.
  pose proof (Qabs_nonneg (fst p - fst q)).
  pose proof (Qabs_nonneg (snd p - snd q)). lra.
Qed.

Lemma d1_sym : forall p q, d1 p q == d1 q p.
Proof.
  intros p q. unfold d1.
  rewrite (qabs_sub_sym (fst p) (fst q)).
  rewrite (qabs_sub_sym (snd p) (snd q)). reflexivity.
Qed.

Lemma d1_self_zero : forall p, d1 p p == 0.
Proof.
  intro p. unfold d1.
  assert (Ex : fst p - fst p == 0) by ring.
  assert (Ey : snd p - snd p == 0) by ring.
  rewrite Ex, Ey. vm_compute. reflexivity.
Qed.

(* ★ THE GEODESIC RULE: triangle inequality — a detour never shortens *)
Theorem d1_triangle : forall a b c, d1 a c <= d1 a b + d1 b c.
Proof.
  intros a b c. unfold d1.
  pose proof (qabs_sub_triangle (fst a) (fst b) (fst c)) as Hx.
  pose proof (qabs_sub_triangle (snd a) (snd b) (snd c)) as Hy. lra.
Qed.

(* path length is additive under concatenation (composition of paths) *)
Lemma plen_app : forall l1 a l2,
  plen a (l1 ++ l2) == plen a l1 + plen (pend a l1) l2.
Proof.
  induction l1 as [|p l1' IH]; intros a l2.
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(* ★ EVERY discrete path from a to its endpoint is ≥ the direct distance:
   the direct distance is the INFIMUM of discrete path lengths (geodesic = extremal) *)
Theorem plen_ge : forall l a, d1 a (pend a l) <= plen a l.
Proof.
  induction l as [|p l' IH]; intro a.
  - simpl. rewrite d1_self_zero. apply Qle_refl.
  - simpl.
    eapply Qle_trans; [ apply (d1_triangle a p (pend p l')) | ].
    apply Qplus_le_compat; [ apply Qle_refl | apply IH ].
Qed.

(* the direct two-point path has length exactly d(a,b) *)
Theorem straight_is_geodesic : forall a b, plen a [b] == d1 a b.
Proof. intros a b. simpl. ring. Qed.

(* ★★ THE GEODESIC = SHORTEST PATH: no path beats the straight segment *)
Theorem straight_is_shortest : forall l a b,
  pend a l = b -> plen a [b] <= plen a l.
Proof.
  intros l a b Hb.
  pose proof (plen_ge l a) as H. rewrite Hb in H.
  rewrite straight_is_geodesic. exact H.
Qed.

(* ★ REFINEMENT INVARIANCE (= limit of discrete paths): inserting an on-segment
   point m (one for which d(a,m)+d(m,b)=d(a,b)) does not change the geodesic length *)
Theorem geodesic_insert : forall a m b,
  d1 a m + d1 m b == d1 a b -> plen a [m; b] == plen a [b].
Proof. intros a m b H. simpl. lra. Qed.

(* ===================== concrete witnesses ===================== *)
Definition A  : Point := (0, 0).
Definition Mid : Point := (1, 0).
Definition B  : Point := (2, 0).
Definition Up : Point := (1, 1).

(* refining the straight segment (0,0)→(2,0) through (1,0) keeps length = 2 *)
Theorem straight_refinement_concrete : plen A [Mid; B] == d1 A B.
Proof. vm_compute. reflexivity. Qed.

(* a non-monotone detour (0,0)→(1,1)→(2,0) is STRICTLY longer than the geodesic *)
Theorem detour_strictly_longer : d1 A B < plen A [Up; B].
Proof.
  assert (H1 : d1 A B == 2) by (vm_compute; reflexivity).
  assert (H2 : plen A [Up; B] == 4) by (vm_compute; reflexivity).
  rewrite H1, H2. lra.
Qed.
