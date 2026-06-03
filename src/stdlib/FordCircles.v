(** * FordCircles.v — Ford circles: the infinite tangent-circle family indexed by ℚ, the
      GEOMETRIC realization of the Stern–Brocot/Farey unimodular determinant |ps−qr|=1.
      Two Ford circles are tangent ⟺ their fractions are Farey neighbors (det ±1) — the
      Element-side adjacency of the rationals made geometry.  Each Ford circle has INTEGER
      curvature 2q² (a degenerate Apollonian packing, x-axis = curvature-0 circle), bridging
      DescartesCircles; the irrationals (√2) are exactly the points with NO Ford circle —
      the cusps the nested tangent circles approach but never reach (role-limit).

    Elements: the individual Ford circles; the determinant ps−qr; integer curvature 2q²;
              the concrete tangency chain 0/1 ~ 1/1 ~ 1/2 (L1 + P4)
    Roles:    Element side = every rational p/q carries a Ford circle (integer curvature 2q²)
              and the family tiles the half-plane by tangency = the Stern–Brocot tree as
              geometry, every ℚ enumerated with a tangent circle; role-limit = an irrational
              point (√2) has NO Ford circle — it sits in the gap, approached but never reached
    Rules:    tangency ⟺ |ps−qr|=1 (the unimodular determinant, now geometric); the mediant
              (p+r)/(q+s) inherits the determinant from both parents ⟹ tangent to both;
              the generating identity dist²−(r_q+r_s)² = (det²−1)/(q²s²)

    THE DEEP POINT — tangency ⟺ |ps−qr|=1.  Place at each fraction p/q the circle with center
    (p/q, 1/(2q²)) and radius 1/(2q²) (sitting on the x-axis).  Two such circles, at p/q and
    r/s, are externally tangent ⟺ dist²(centers) = (r_q+r_s)², and the ONE generating identity
    `ford_tangency_identity` shows dist²−(r_q+r_s)² = (det²−1)/(q²s²), det=ps−qr.  So they touch
    ⟺ det²=1 ⟺ |ps−qr|=1 ⟺ Farey neighbors — the SAME unimodular determinant as Stern–Brocot
    (SternBrocot.v `unimodular_preserved`), now a geometric fact (`ford_det1_tangent`,
    `ford_neighbors_tangent`).  The mediant (p+r)/(q+s) keeps the determinant with each parent
    (`mediant_det_left/right`, ring), so it is tangent to both — the Stern–Brocot tree grown as a
    tower of tangent circles.  Each Ford circle has integer curvature 2q² (a degenerate Apollonian
    packing — DescartesCircles).  But √2 has NO Ford circle: it is rational-free (`ford_no_sqrt2`
    via sqrt2_not_in_Q), the cusp the nested tangencies approach but never reach — the role-limit.
    Element = a rational point with its tangent circle (det ±1 adjacency); role-limit = an
    irrational point in the gap (a non-terminating descent of tangent circles).

    ============ E/R/R разбор ============
      Rules (L5): касание ⟺ |ps−qr|=1 (унимодулярный определитель Штерна–Броко, теперь геометрия);
                  медианта (p+r)/(q+s) наследует определитель от обоих родителей ⟹ касается обеих;
                  порождающее тождество dist²−(r_q+r_s)²=(det²−1)/(q²s²).
      Roles (L4): Element = каждая p/q несёт окружность Форда (целая кривизна 2q²), семейство
                  замощает полуплоскость касаниями = дерево Штерна–Броко как геометрия; role-limit =
                  иррациональная точка (√2) НЕ имеет окружности Форда (зазор, не достигается).
      Elements  : окружности Форда; определитель ps−qr; кривизна 2q²; цепочка 0/1~1/1~1/2 (L1+P4).
    ДИАГНОСТИКА (P4): касание ⟺ |det|=1 ⟺ сосед Фарея ⟺ Element-смежность; определитель ±1 (инвариант
    Штерна–Броко) ЕСТЬ касание (алгебра стала геометрией). √2 = точка, где вложенные касания не
    замыкаются на центр = role-limit (нетерминирующий путь). Кривизна 2q² целая ⟹ вырожденная аполлониева
    упаковка (мост к DescartesCircles). «Есть ли окружность Форда в √2?» = не-вопрос: √2 = имя процесса.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith.
From ToS Require Import analysis.Sqrt2Irrational.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Ford circle at a fraction p/q: center (p/q, 1/(2q²)), radius 1/(2q²)   *)
(* ===================================================================== *)

(** The x-coordinate (where the Ford circle touches the axis) and the radius
    (= the y-coordinate of the center). *)
Definition fx (p q : Z) : Q := inject_Z p / inject_Z q.
Definition frad (q : Z) : Q := 1 / (2 * inject_Z q * inject_Z q).

(** The tangency "defect": dist²(centers) − (r_q + r_s)².  Zero ⟺ the two Ford circles are
    externally tangent; positive ⟺ disjoint. *)
Definition tang_defect (p q r s : Z) : Q :=
    (fx p q - fx r s) * (fx p q - fx r s)
  + (frad q - frad s) * (frad q - frad s)
  - (frad q + frad s) * (frad q + frad s).

(* ===================================================================== *)
(*  The generating identity: defect = (det² − 1)/(q²s²)                    *)
(* ===================================================================== *)

(** ★ THE ONE identity behind everything: the tangency defect of the Ford circles at p/q and
    r/s equals (det² − 1)/(q²s²), where det = ps − qr.  So they are tangent (defect 0) exactly
    when det² = 1, i.e. |ps − qr| = 1 — the Stern–Brocot/Farey unimodular determinant. *)
Lemma ford_tangency_identity :
  forall p q r s : Z, ~ inject_Z q == 0 -> ~ inject_Z s == 0 ->
    tang_defect p q r s
    == ((inject_Z p * inject_Z s - inject_Z q * inject_Z r)
        * (inject_Z p * inject_Z s - inject_Z q * inject_Z r) - 1)
       / (inject_Z q * inject_Z q * inject_Z s * inject_Z s).
Proof.
  intros p q r s Hq Hs. unfold tang_defect, fx, frad.
  field. first [ assumption | split; assumption ].
Qed.

(** ★ The useful direction: if the determinant squares to 1 (Farey neighbors), the Ford
    circles are tangent.  This turns Stern–Brocot's `unimodular_preserved` into geometry. *)
Lemma ford_det1_tangent :
  forall p q r s : Z, ~ inject_Z q == 0 -> ~ inject_Z s == 0 ->
    (inject_Z p * inject_Z s - inject_Z q * inject_Z r)
    * (inject_Z p * inject_Z s - inject_Z q * inject_Z r) == 1 ->
    tang_defect p q r s == 0.
Proof.
  intros p q r s Hq Hs Hdet.
  rewrite ford_tangency_identity by assumption.
  rewrite Hdet. unfold Qdiv. ring.
Qed.

(* ===================================================================== *)
(*  Concrete tangencies (Farey neighbors) and a non-tangency               *)
(* ===================================================================== *)

(** Concrete Farey-neighbor tangencies (each |ps − qr| = 1): 0/1 ~ 1/1, 1/2 ~ 1/3,
    1/2 ~ 2/3 — the defect is exactly 0. *)
Lemma ford_neighbors_tangent :
  tang_defect 0 1 1 1 == 0
  /\ tang_defect 1 2 1 3 == 0
  /\ tang_defect 1 2 2 3 == 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Non-neighbors are NOT tangent: 0/1 and 2/3 have det = −2 (|det|=2≠1), so the circles are
    disjoint — defect = (4−1)/9 = 1/3 > 0. *)
Lemma ford_non_neighbor_gap : tang_defect 0 1 2 3 == 1 # 3.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  The mediant inherits the determinant from both parents                 *)
(* ===================================================================== *)

(** ★ The mediant (p+r)/(q+s) keeps the SAME determinant with each parent (= ps − qr): so if
    the parents are Farey neighbors, the mediant is tangent to BOTH — the Stern–Brocot tree as
    a tower of tangent Ford circles.  Left parent p/q: *)
Lemma mediant_det_left :
  forall p q r s : Z, (p * (q + s) - q * (p + r) = p * s - q * r)%Z.
Proof. intros. ring. Qed.

(** Right parent r/s. *)
Lemma mediant_det_right :
  forall p q r s : Z, ((p + r) * s - (q + s) * r = p * s - q * r)%Z.
Proof. intros. ring. Qed.

(** Concrete: parents 0/1 ~ 1/1 (tangent), mediant 1/2 is tangent to both. *)
Lemma ford_mediant_tangent_example :
  tang_defect 0 1 1 2 == 0 /\ tang_defect 1 2 1 1 == 0.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  Role-limit: an irrational point has no Ford circle                     *)
(* ===================================================================== *)

(** ★ √2 has NO Ford circle: a Ford circle sits at a rational p/q, but no rational squares to
    2.  √2 is the cusp the nested tangent circles approach but never reach — the role-limit. *)
Theorem ford_no_sqrt2 : ~ (exists r : Q, r * r == 2).
Proof. exact sqrt2_not_in_Q. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** Ford circles, split by the finitization boundary:
      (a) ELEMENT — tangency IS the unimodular determinant: defect = (det²−1)/(q²s²)
          (`ford_tangency_identity`), so det²=1 (Farey neighbors) ⟹ tangent
          (`ford_det1_tangent`), and the mediant inherits the determinant from both parents
          (`mediant_det_left/right`) — the Stern–Brocot tree as a tower of tangent circles;
      (b) ROLE-LIMIT — √2 has no Ford circle (`ford_no_sqrt2`): the irrational cusp the nested
          tangencies approach but never reach. *)
Theorem ford_circles_synthesis :
  (forall p q r s : Z, ~ inject_Z q == 0 -> ~ inject_Z s == 0 ->
     (inject_Z p * inject_Z s - inject_Z q * inject_Z r)
     * (inject_Z p * inject_Z s - inject_Z q * inject_Z r) == 1 ->
     tang_defect p q r s == 0)
  /\ (forall p q r s : Z, (p * (q + s) - q * (p + r) = p * s - q * r)%Z)
  /\ tang_defect 0 1 1 1 == 0
  /\ ~ (exists r : Q, r * r == 2).
Proof.
  split; [ exact ford_det1_tangent | ].
  split; [ exact mediant_det_left | ].
  split; [ vm_compute; reflexivity | exact ford_no_sqrt2 ].
Qed.
