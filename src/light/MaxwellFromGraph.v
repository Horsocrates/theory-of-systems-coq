(** * MaxwellFromGraph.v — discrete Maxwell-SHAPED operators on a graph face: real identities,
       honest scope (June 2026 rollback: four `True`-stub "theorems" REMOVED)
    Elements: edge values (Q) on a face; vertex potentials; edge lists at a vertex
    Roles:    magnetic_from_electric — the face-curl role; gauss_electric_sum — the
              vertex-divergence role; potential-to-edges — the gradient role
    Rules:    superposition/linearity (curl_superposition, gauss_additive), antisymmetry
              under orientation flip (curl_antisymmetric), and d∘d = 0
              (curl_of_gradient_zero: a gradient field is curl-free) — forced Q-arithmetic
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: April 2026  (True-stub honesty rollback: June 2026)

    +-- HONEST STATUS (rolled back) --------------------------------------------------------+
    | REMOVED June 2026: faraday, wave_from_maxwell, maxwell_not_postulated, charge_as_source |
    | — four `Theorem _ : True` stubs masquerading as results (they also violated the          |
    | project's "0 True placeholders" rule).  REPLACED by real general identities:             |
    |   curl_uniform_zero      — uniform fields are curl-free, for ALL values (was: example);  |
    |   curl_antisymmetric     — orientation flip negates the curl, for ALL values;            |
    |   curl_superposition     — the curl is LINEAR (superposition principle);                 |
    |   gauss_additive         — the vertex sum is additive over edge multisets;               |
    |   curl_of_gradient_zero  — d∘d = 0: edges from a vertex POTENTIAL have zero curl         |
    |                            (the cohomological seed of the Maxwell structure);            |
    |   gauss_two_balanced_iff — zero vertex sum ⟺ balanced edges (charge as imbalance).       |
    | WHAT IS NOT HERE: dynamics.  No time layer, hence no Faraday induction, no wave           |
    | equation, no derivation of Maxwell's equations.  "Maxwell not postulated" was an          |
    | over-claim; the honest claim is "Maxwell-SHAPED statics of two graph operators".          |
    +-----------------------------------------------------------------------------------------+

    ============ E/R/R разбор ============
      Elements : значения на рёбрах одной грани (Q); потенциалы четырёх вершин; списки рёбер
                 при вершине.
      Roles    : face-curl (magnetic_from_electric) и vertex-divergence (gauss_electric_sum) —
                 две операторные роли; «поле из потенциала» — роль градиента; заряд — роль
                 дисбаланса рёбер (gauss_two_balanced_iff).
      Rules    : суперпозиция (линейность обоих операторов), антисимметрия при смене
                 ориентации, d∘d = 0 (curl градиента = 0) — вынужденная арифметика на Q.
      ДИАГНОСТИКА (P4): статика есть, динамики НЕТ — Фарадей и волновое уравнение требуют
      временно́го (процессного) слоя, которого в файле нет; прежние True-заглушки заявляли
      именно его.  Честная форма: forced(тождества операторов: линейность, антисимметрия,
      dd=0) ⟂ absent(динамика).  Невынужденная точка ИМЕНОВАНА: сама форма face-curl /
      vertex-sum — дискретизационный выбор (модель), не вывод из различения.
      Уровень: `methods` — честные дискретные тождества, не «вывод Максвелла».
*)

From Stdlib Require Import QArith Qabs Lia ZArith List PeanoNat.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(*  Definitions                                                        *)
(* ------------------------------------------------------------------ *)

(** Discrete curl: magnetic field from electric field on edges of a face.
    B = (E_up - E_down) - (E_right - E_left)
    = curl(E) on one face of the dual graph *)
Definition magnetic_from_electric (ex_up ex_down ey_right ey_left : Q) : Q :=
  ex_up - ex_down - ey_right + ey_left.

(** Gauss's law operator: sum of electric field on edges leaving a vertex.
    Zero sum = no charge enclosed *)
Definition gauss_electric_sum (edges : list Q) : Q :=
  fold_left Qplus edges 0.

(* ------------------------------------------------------------------ *)
(*  GENERAL IDENTITIES (June 2026 — the real content)                  *)
(* ------------------------------------------------------------------ *)

(** Uniform fields are curl-free — for ALL field values, not an example. *)
Theorem curl_uniform_zero : forall a : Q,
  magnetic_from_electric a a a a == 0.
Proof. intro a. unfold magnetic_from_electric. ring. Qed.

(** Orientation flip (up<->down, right<->left) negates the curl — for ALL values. *)
Theorem curl_antisymmetric : forall up down right left : Q,
  magnetic_from_electric up down right left
  == - magnetic_from_electric down up left right.
Proof. intros. unfold magnetic_from_electric. ring. Qed.

(** ★ Superposition: the discrete curl is LINEAR — fields add, curls add. *)
Theorem curl_superposition : forall u1 d1 r1 l1 u2 d2 r2 l2 : Q,
  magnetic_from_electric (u1+u2) (d1+d2) (r1+r2) (l1+l2)
  == magnetic_from_electric u1 d1 r1 l1 + magnetic_from_electric u2 d2 r2 l2.
Proof. intros. unfold magnetic_from_electric. ring. Qed.

(** ★★ d∘d = 0: edges generated by a vertex POTENTIAL (pul,pur,pdl,pdr) — i.e. each
    edge value is the potential difference along it — have ZERO curl around the face.
    This is the genuine discrete seed of the Maxwell structure (gradient fields are
    curl-free; closed-form identity, no dynamics needed). *)
Theorem curl_of_gradient_zero : forall pul pur pdl pdr : Q,
  magnetic_from_electric (pur - pul) (pdr - pdl) (pur - pdr) (pul - pdl) == 0.
Proof. intros. unfold magnetic_from_electric. ring. Qed.

(** Accumulator shift for the vertex sum (helper). *)
Lemma gauss_sum_shift : forall (xs : list Q) (a : Q),
  fold_left Qplus xs a == a + fold_left Qplus xs 0.
Proof.
  induction xs as [| x xs IH]; intro a.
  - simpl. ring.
  - simpl. rewrite (IH (a + x)). rewrite (IH (0 + x)). ring.
Qed.

(** ★ The vertex sum is ADDITIVE over edge collections (Gauss superposition). *)
Theorem gauss_additive : forall e1 e2 : list Q,
  gauss_electric_sum (e1 ++ e2) == gauss_electric_sum e1 + gauss_electric_sum e2.
Proof.
  intros e1 e2. unfold gauss_electric_sum.
  rewrite fold_left_app. rewrite (gauss_sum_shift e2 (fold_left Qplus e1 0)).
  reflexivity.
Qed.

(** Charge as imbalance: for a two-edge vertex, zero sum ⟺ the edges balance.
    (Replaces the removed `charge_as_source : True` stub with actual content.) *)
Theorem gauss_two_balanced_iff : forall a b : Q,
  gauss_electric_sum (a :: b :: nil) == 0 <-> b == - a.
Proof.
  intros a b. unfold gauss_electric_sum. simpl.
  split; intro H; lra.
Qed.

(* ------------------------------------------------------------------ *)
(*  Concrete instances                                                 *)
(* ------------------------------------------------------------------ *)

(** Gauss: opposite edges cancel => no charge *)
Theorem gauss_zero_no_charge :
  gauss_electric_sum ((1 : Q) :: (-(1) : Q) :: nil) == 0.
Proof. vm_compute. reflexivity. Qed.

(** Gauss: same-sign edges => positive charge *)
Theorem gauss_positive_charge :
  gauss_electric_sum ((1 : Q) :: (1 : Q) :: nil) == 2.
Proof. vm_compute. reflexivity. Qed.

(** Uniform field has zero curl (no magnetic field) *)
Theorem magnetic_zero_uniform :
  magnetic_from_electric 1 1 1 1 == 0.
Proof. vm_compute. reflexivity. Qed.

(** Non-uniform field has nonzero curl *)
Theorem magnetic_nonzero_curl :
  magnetic_from_electric 1 0 0 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** Curl antisymmetry, concrete instance *)
Theorem curl_antisymmetric_concrete :
  magnetic_from_electric 1 0 0 0 == -(magnetic_from_electric 0 1 0 0).
Proof. vm_compute. reflexivity. Qed.

(** Another antisymmetry instance *)
Theorem curl_antisymmetric_concrete2 :
  magnetic_from_electric 3 1 2 0 == -(magnetic_from_electric 1 3 0 2).
Proof. vm_compute. reflexivity. Qed.

(** Gauss with three edges *)
Theorem gauss_three_edges :
  gauss_electric_sum ((1 : Q) :: (-(1) : Q) :: (1 : Q) :: nil) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  SYNTHESIS — what the graph operators REALLY give (no True padding) *)
(* ------------------------------------------------------------------ *)

Theorem maxwell_from_graph_synthesis :
  (* uniform fields curl-free, all values *)
  (forall a : Q, magnetic_from_electric a a a a == 0) /\
  (* d∘d = 0: gradient fields curl-free *)
  (forall pul pur pdl pdr : Q,
      magnetic_from_electric (pur - pul) (pdr - pdl) (pur - pdr) (pul - pdl) == 0) /\
  (* Gauss superposition *)
  (forall e1 e2 : list Q,
      gauss_electric_sum (e1 ++ e2) == gauss_electric_sum e1 + gauss_electric_sum e2) /\
  (* concrete no-charge instance *)
  gauss_electric_sum ((1 : Q) :: (-(1) : Q) :: nil) == 0.
Proof.
  split; [exact curl_uniform_zero |].
  split; [exact curl_of_gradient_zero |].
  split; [exact gauss_additive |].
  exact gauss_zero_no_charge.
Qed.

Print Assumptions curl_of_gradient_zero.
Print Assumptions maxwell_from_graph_synthesis.
