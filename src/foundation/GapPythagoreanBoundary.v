(** * GapPythagoreanBoundary.v — the spectral gap of the universal TRACELESS 2×2 is an Element
       (rational, actualizable) IFF (ε, δ, gap/2) is a Pythagorean triple — vein A's discriminant
       valve, restricted to tr = 0, governs the whole physics-gap cluster.

    THE OBSERVATION.
    Every spectral-gap Hamiltonian in the repo is the TRACELESS symmetric 2×2
        H(ε,δ) = [[ε, δ], [δ, −ε]]      (tr = 0).
    Instances, verbatim from the physics files:
      - graphene : [[0, t],[t, 0]]     (stdlib/qchem/GrapheneTransfer.v:16, tr=0, det=−t²)    — ε=0
      - BCS      : [[ε, δ],[δ, −ε]]     (stdlib/qchem/BCSTransferMatrix.v:15, tr=0, det=−(ε²+δ²))
      - SSH / Ising transfer: same traceless / off-diagonal shape.
    Its characteristic discriminant is
        Δ = tr² − 4·det = 0 − 4·(−(ε²+δ²)) = 4·(ε² + δ²)   ( ≥ 0, so the gap spectrum is ALWAYS real —
    no elliptic/compact case, unlike the det=1 boost-vs-rotation split of GRQFTDiscriminantBridge), and
    the spectral gap is G = 2·√(ε²+δ²).

    THE BRIDGE TO VEIN A.
    By DiscriminantCompleteEigenvalue.rational_eigenvalue_iff_disc_square (the vein-A master valve:
    a 2×2 has a RATIONAL eigenvalue ⟺ Δ is a perfect square), specialised to t=0, e=−(ε²+δ²):
        gap is an Element (rational eigenvalue)  ⟺  ε² + δ²  is a perfect rational square
                                                 ⟺  (ε, δ, G/2)  is a PYTHAGOREAN triple.
    So the SAME perfect-square dial that sorts abstract eigenvalues (Element vs role-limit / surd)
    sorts PHYSICAL GAPS — and the Element gaps are exactly the rational points of the circle
    ε²+δ²=□, i.e. the Pythagorean / q-kinematics lattice that also gives the rational rotations
    (geometry/RationalSO3.v). For INTEGER (ε,δ) the sort is DECIDABLE, 0 axioms
    (decide_elementZ on Δ = 4(ε²+δ²)).

    WHAT IS NEW / HONEST SCALE.
    The algebra is `rational_eigenvalue_iff_disc_square` at t=0 — NOT a new theorem. The meta-pattern
    "rational physical quantity = Element, irrational = role-limit" is already H5/H6/H7 (Gisin, Bell/
    Tsirelson 2√2, the √2 gate ceiling). NEW here is the UNIFICATION: the entire gap cluster
    (graphene / BCS / SSH / Ising, and the gauge mass-gap question) is one traceless-2×2 family whose
    Element/role-limit status is a Pythagorean number-theoretic condition, sewing the gap-physics to
    vein A AND to the q-kinematics rational-circle thread. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : бесследовая симметричная 2×2 H(ε,δ)=[[ε,δ],[δ,−ε]]; инварианты tr=0, det=−(ε²+δ²),
                 Δ=4(ε²+δ²); щель G=2√(ε²+δ²); физ-инстансы — графен (ε=0), BCS, SSH, Ising.
      Roles    : off-diagonal δ = «связь»/coupling (хоппинг, спаривание); G = спектральная наблюдаемая/масса;
                 рацио-щель = Element (актуализуема), иррацио-щель = role-limit (континуум); полный-квадрат =
                 вентиль-решатель вены A.
      Rules    : G∈ℚ ⟺ ε²+δ² полный квадрат ⟺ (ε,δ,G/2) пифагорова ⟺ Δ полный квадрат
                 (= rational_eigenvalue_iff_disc_square при tr=0); целые (ε,δ) ⟹ разрешимо (decide_elementZ).
      ДИАГНОСТИКА (P4): Element-щели = рациональные точки окружности ε²+δ²=□ — мера 0, но плотны и РАЗРЕШИМЫ;
      почти все физ-щели — role-limit (континуум, не актуализованная рацио-величина). Граница «актуализуема /
      континуум» физики = тот же разрешимый вентиль квадрата, что и абстрактная граница собств. значений ⟹
      физика НАСЛЕДУЕТ вену A; рацио-щели = пифагорова решётка q-kinematics. ЧЕСТНО: это сужение вены A на
      tr=0 + унификация gap-кластера, не новая теорема; YM-характерный трансфер — отдельная проверка.
      Уровень: `синтез+наблюдение`.

    STATUS: 11 Qed, 0 Admitted, 0 axioms  (builds on foundation.DiscriminantCompleteEigenvalue, H1ConstructivityDecidable)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.H1ConstructivityDecidable.
From ToS Require Import foundation.DiscriminantCompleteEigenvalue.

Open Scope Q_scope.

(* ===================================================================== *)
(*  The traceless gap Hamiltonian H(ε,δ) = [[ε, δ],[δ, −ε]]                *)
(* ===================================================================== *)

(** Its trace is 0, its determinant is −(ε²+δ²); gap_normsq = (G/2)² = E_qp². *)
Definition gap_tr     (eps del : Q) : Q := eps + (- eps).
Definition gap_det    (eps del : Q) : Q := eps * (- eps) - del * del.
Definition gap_normsq (eps del : Q) : Q := eps * eps + del * del.

Lemma gap_tr_zero : forall eps del, gap_tr eps del == 0.
Proof. intros eps del. unfold gap_tr. ring. Qed.

Lemma gap_det_value : forall eps del, gap_det eps del == - gap_normsq eps del.
Proof. intros eps del. unfold gap_det, gap_normsq. ring. Qed.

(** ★ The gap discriminant Δ = tr²−4det = 4(ε²+δ²) — a sum of squares, hence ≥ 0: the gap spectrum is
    ALWAYS real (no elliptic/compact case, unlike the det=1 boost/rotation split of GRQFTDiscriminantBridge). *)
Lemma gap_disc_value : forall eps del,
  discQ (gap_tr eps del) (gap_det eps del) == 4 * gap_normsq eps del.
Proof. intros eps del. unfold discQ, gap_tr, gap_det, gap_normsq. ring. Qed.

(* ===================================================================== *)
(*  ★★ THE GAP-PYTHAGOREAN BICONDITIONAL (vein A at tr = 0)                *)
(* ===================================================================== *)

(** The eigenvalue equation of the traceless gap matrix is exactly x² = ε²+δ². *)
Lemma gap_chareq : forall eps del x,
  charval (gap_tr eps del) (gap_det eps del) x == 0 <-> x * x == gap_normsq eps del.
Proof.
  intros eps del x. unfold charval.
  assert (Hrw : x * x - gap_tr eps del * x + gap_det eps del == x * x - gap_normsq eps del).
  { rewrite gap_tr_zero, gap_det_value. ring. }
  rewrite Hrw. split; intro H; lra.
Qed.

(** ★★ The spectral gap is an Element (rational eigenvalue) IFF (ε, δ, G/2) is a Pythagorean triple
    (ε²+δ² a perfect rational square). This is the vein-A valve restricted to tr = 0. *)
Theorem gap_element_iff_pythagorean : forall eps del,
  has_rat_eig (gap_tr eps del) (gap_det eps del)
  <-> (exists g, g * g == gap_normsq eps del).
Proof.
  intros eps del. unfold has_rat_eig. split.
  - intros [x Hx]. exists x. apply (proj1 (gap_chareq eps del x)). exact Hx.
  - intros [g Hg]. exists g. apply (proj2 (gap_chareq eps del g)). exact Hg.
Qed.

(** ★ The LITERAL vein-A reading: the gap is an Element iff its discriminant Δ = 4(ε²+δ²) is a perfect
    square — `rational_eigenvalue_iff_disc_square` applied to the gap matrix. *)
Corollary gap_element_iff_disc_square : forall eps del,
  has_rat_eig (gap_tr eps del) (gap_det eps del)
  <-> disc_is_square_Q (gap_tr eps del) (gap_det eps del).
Proof. intros eps del. apply rational_eigenvalue_iff_disc_square. Qed.

(* ===================================================================== *)
(*  For INTEGER (ε,δ) the Element/role-limit sort of the gap is DECIDABLE  *)
(* ===================================================================== *)

(** Δ = 4(ε²+δ²) for integer ε,δ. *)
Definition gap_disc_Z (eps del : Z) : Z := (4 * (eps * eps + del * del))%Z.

(** ★ Whether the gap of an integer (ε,δ) Hamiltonian is an Element is DECIDABLE, 0 axioms: run the
    vein-A decider on Δ = 4(ε²+δ²). (ElementZ Δ ⟺ Δ a perfect square ⟺ gap rational, since 4 is a square.) *)
Corollary gap_element_decidable_Z : forall eps del : Z,
  { ElementZ (gap_disc_Z eps del) } + { ~ ElementZ (gap_disc_Z eps del) }.
Proof. intros eps del. exact (decide_elementZ (gap_disc_Z eps del)). Qed.

(* ===================================================================== *)
(*  Instances: the real physics matrices, sorted by the Pythagorean valve  *)
(* ===================================================================== *)

(** GRAPHENE [[0,t],[t,0]] (GrapheneTransfer.v): ε=0, δ=t, so ε²+δ²=t² is ALWAYS a square (t²) —
    the Dirac eigenvalues ±t are rational for any rational hopping t : ELEMENT (massless Dirac). *)
Example graphene_element : forall t, has_rat_eig (gap_tr 0 t) (gap_det 0 t).
Proof.
  intro t. apply (proj2 (gap_element_iff_pythagorean 0 t)).
  exists t. unfold gap_normsq. ring.
Qed.

(** BCS [[ε,δ],[δ,−ε]] (BCSTransferMatrix.v) at ε=1, δ=1/2: ε²+δ² = 5/4, NOT a square (gap = √5/2,
    the golden surd) — ROLE-LIMIT. This is the concrete case computed in BCSTransferMatrix.v (E_qp²=5/4). *)
Example bcs_1_half_role_limit :
  ~ has_rat_eig (gap_tr 1 (1#2)) (gap_det 1 (1#2)).
Proof.
  intro H. apply (proj1 (gap_element_iff_pythagorean 1 (1#2))) in H.
  destruct H as [g Hg].
  apply rolelimit_5. exists (2 * g).
  assert (Hn : gap_normsq 1 (1#2) == 5#4) by (unfold gap_normsq; vm_compute; reflexivity).
  rewrite Hn in Hg.
  assert (Hgoal : (2 * g) * (2 * g) == 4 * (g * g)) by ring.
  rewrite Hgoal, Hg. vm_compute. reflexivity.
Qed.

(** BCS at ε=4, δ=3: ε²+δ² = 25 = 5² — the (3,4,5) PYTHAGOREAN triple makes the gap eigenvalue 5
    RATIONAL : ELEMENT. The SAME 3-4-5 triple that gives the rational rotation (geometry/RationalSO3.v). *)
Example bcs_345_element : has_rat_eig (gap_tr 4 3) (gap_det 4 3).
Proof.
  apply (proj2 (gap_element_iff_pythagorean 4 3)).
  exists 5. unfold gap_normsq. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The universal traceless-2×2 gap, sorted by ONE Pythagorean / vein-A valve:
      (valve)      gap is Element ⟺ (ε,δ,G/2) Pythagorean ⟺ ε²+δ² a perfect square;
      (discriminant) Δ = tr²−4det = 4(ε²+δ²) ≥ 0 (gap spectrum always real);
      (Element)    graphene [[0,t],[t,0]] — gap ±t rational for any t;
      (role-limit) BCS(ε=1,δ=½) — gap √5/2, irrational (no rational eigenvalue);
      (Element)    BCS(ε=4,δ=3) — the 3-4-5 triple gives the rational gap 5.
    So the physics-gap cluster (graphene/BCS/SSH/Ising) inherits vein A's perfect-square boundary: the
    rationally-actualizable gaps are exactly the Pythagorean lattice; generic gaps are continuum
    role-limits. Honest: this is vein A specialised to tr=0 + a cross-cluster unification, not a new
    theorem; the gauge (Yang–Mills) character-transfer gap is a separate check. *)
Theorem gap_pythagorean_boundary :
  (forall eps del, has_rat_eig (gap_tr eps del) (gap_det eps del)
       <-> exists g, g * g == gap_normsq eps del)
  /\ (forall eps del, discQ (gap_tr eps del) (gap_det eps del) == 4 * gap_normsq eps del)
  /\ (forall t, has_rat_eig (gap_tr 0 t) (gap_det 0 t))
  /\ (~ has_rat_eig (gap_tr 1 (1#2)) (gap_det 1 (1#2)))
  /\ has_rat_eig (gap_tr 4 3) (gap_det 4 3).
Proof.
  split. exact gap_element_iff_pythagorean.
  split. exact gap_disc_value.
  split. exact graphene_element.
  split. exact bcs_1_half_role_limit.
  exact bcs_345_element.
Qed.
