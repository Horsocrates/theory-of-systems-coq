(** * ReductionAtlasSurd.v — the reduction atlas, page I: the SURD ENGINE as a cluster primitive.
      The cluster's many quadratic role-limits are NOT independent facts: they are one engine —
      the surd theorem — read through domain-specific indices.  Each domain obstruction is the
      single equation m² = n_X·k² (k≠0), impossible iff the index n_X is not a perfect square.
      Stripping the domain dressing (geometry, dynamics, quantum nonlocality) leaves m²=n_X·k²,
      and the impossibility is `GeneralSqrt` at index n_X.  The 45°-rotation obstruction is index
      2, the lattice-equilateral / 60°-point obstruction is index 3, the order-5 / icosahedron /
      golden-ratio obstruction is index 5, the Tsirelson optimum is index 8.  Four diverse
      role-limits = ONE engine at four indices.

    Elements: the integer indices n_X ∈ {2,3,5,8}; the obstruction equations m²=n_X·k²;
              the engine's proof (L1 + P4)
    Roles:    each domain's surd index n_X — the single integer that decides the domain's
              dichotomy; the obstruction is n_X dressed up in domain-specific form
    Rules:    the one generating rule — m²=n·k² (k≠0) is impossible iff n is not a perfect square;
              it sorts every domain by one question, "is n_X a perfect square?"

    THE DEEP POINT — the catalogue collapses to one engine.  "Why no equilateral triangle on the
    integer lattice?  Why no rational rotation of order 5?  Why is the Tsirelson optimum
    irrational?" — these LOOK like different questions across geometry, dynamics, and quantum
    nonlocality.  The atlas shows they are ONE question — "is the index n_X a perfect square?" —
    asked of different n_X.  Each obstruction reduces to m² = n_X·k² with k≠0 (`no_scaled_square`),
    impossible because n_X is not a perfect square (`GeneralSqrt`'s surd theorem).  So the
    role-limits are not independent obstructions but a single engine instantiated: index 2 (the
    45° rotation), index 3 (the lattice equilateral, the 60° point), index 5 (order 5, the
    icosahedron, the golden ratio), index 8 (Tsirelson 2√2).  This raises the honesty bar from
    "a new framing of a known fact, many times" to "these known facts are ONE theorem."  Element =
    a domain index; role-limit = the engine read at a non-square index.

    ============ E/R/R разбор ============
      Rules (L5): одно правило — m²=n·k² (k≠0) невозможно ⟺ n не полный квадрат; сортирует все
                  домены одним вопросом «полный ли квадрат n_X?».
      Roles (L4): сурд-индекс n_X домена — единственное целое, решающее дихотомию; обструкция = n_X
                  наряженный в домен (45°→2, равносторонний/60°→3, порядок-5/икосаэдр/золотое→5, Цирельсон→8).
      Elements  : индексы n_X∈{2,3,5,8}; уравнения m²=n_X·k²; доказательство движка (L1+P4).
    ДИАГНОСТИКА (P4): атлас растворяет разнообразие — «почему нет равностороннего/порядка-5/Цирельсон иррац.?»
    суть ОДИН вопрос к разным n_X. Каталог из 68 инстансов схлопывается в ОДИН движок (сурд-теорема) при доменных
    индексах. Не «новое обрамление ×68», а «это ОДНА теорема». Примитивы кластера сделаны явными.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
From ToS Require Import stdlib.GeneralSqrt.
From ToS Require Import stdlib.GranularFloor.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE, in obstruction form: m² = n·k² is impossible for non-square n *)
(* ===================================================================== *)

(** ★ The single rule the whole atlas runs on: if n is not a perfect square, no integers solve
    m² = n·k² with k > 0.  Every domain obstruction below is this equation at its index n_X. *)
Lemma no_scaled_square : forall n m k : Z,
  (forall j : Z, j * j <> n) -> 0 < k -> m * m <> n * (k * k).
Proof.
  intros n m k Hns Hk Heq.
  apply (nonsquare_gap_nonzero n m k Hns Hk). nia.
Qed.

(* ===================================================================== *)
(*  The surd indices: 2, 3, 5, 8 are not perfect squares                   *)
(* ===================================================================== *)

Lemma idx2 : forall j : Z, j * j <> 2.
Proof. intros j. apply (not_square_strict j 1 2); lia. Qed.

Lemma idx3 : forall j : Z, j * j <> 3.
Proof. intros j. apply (not_square_strict j 1 3); lia. Qed.

Lemma idx5 : forall j : Z, j * j <> 5.
Proof. intros j. apply (not_square_strict j 2 5); lia. Qed.

Lemma idx8 : forall j : Z, j * j <> 8.
Proof. intros j. apply (not_square_strict j 2 8); lia. Qed.

(* ===================================================================== *)
(*  The reductions: four domains, four indices, one engine                 *)
(* ===================================================================== *)

(** ★ Index 2 — the 45° rotation.  The isosceles-right obstruction a² = 2b² (a rational point at
    45° would need it) has no nonzero solution: the engine at index 2. *)
Theorem rotation45_role_limit : forall m k : Z, 0 < k -> m * m <> 2 * (k * k).
Proof. intros m k Hk. exact (no_scaled_square 2 m k idx2 Hk). Qed.

(** ★ Index 3 — the lattice equilateral triangle (and the 60° point).  The equilateral
    obstruction is exactly (pt−rq)² = 3·(pr+qt)² (the doubled-area / Lagrange identity); for a
    nondegenerate triangle pr+qt > 0, this is impossible: the engine at index 3. *)
Theorem equilateral_role_limit : forall p q r t : Z,
  0 < p * r + q * t ->
  (p * t - r * q) * (p * t - r * q) <> 3 * ((p * r + q * t) * (p * r + q * t)).
Proof.
  intros p q r t Hk.
  exact (no_scaled_square 3 (p * t - r * q) (p * r + q * t) idx3 Hk).
Qed.

(** The abstract index-3 obstruction, shared by the 60° point and the sphere body-diagonal. *)
Theorem index3_role_limit : forall m k : Z, 0 < k -> m * m <> 3 * (k * k).
Proof. intros m k Hk. exact (no_scaled_square 3 m k idx3 Hk). Qed.

(** ★ Index 5 — order 5 / the icosahedron / the golden ratio.  The order-5 trace and the golden
    relation both force m² = 5·k² (e.g. (2φ−1)² = 5); impossible: the engine at index 5. *)
Theorem order5_role_limit : forall m k : Z, 0 < k -> m * m <> 5 * (k * k).
Proof. intros m k Hk. exact (no_scaled_square 5 m k idx5 Hk). Qed.

(** ★ Index 8 — the Tsirelson optimum 2√2 = √8.  The optimal CHSH value forces m² = 8·k²;
    impossible: the engine at index 8. *)
Theorem tsirelson_role_limit : forall m k : Z, 0 < k -> m * m <> 8 * (k * k).
Proof. intros m k Hk. exact (no_scaled_square 8 m k idx8 Hk). Qed.

(* ===================================================================== *)
(*  The atlas page: four domains as one engine                            *)
(* ===================================================================== *)

(** The surd-engine atlas page:
      (engine) m²=n·k² is impossible for any non-square n (`no_scaled_square`);
      and four cluster role-limits are this engine at four indices —
        index 2: the 45° rotation;
        index 3: the lattice equilateral triangle / the 60° point;
        index 5: order 5 / the icosahedron / the golden ratio;
        index 8: the Tsirelson optimum 2√2.
    Four diverse obstructions, one theorem read at four indices. *)
Theorem surd_atlas :
  (forall n m k : Z, (forall j : Z, j * j <> n) -> 0 < k -> m * m <> n * (k * k))
  /\ (forall m k : Z, 0 < k -> m * m <> 2 * (k * k))
  /\ (forall m k : Z, 0 < k -> m * m <> 3 * (k * k))
  /\ (forall m k : Z, 0 < k -> m * m <> 5 * (k * k))
  /\ (forall m k : Z, 0 < k -> m * m <> 8 * (k * k)).
Proof.
  split; [ exact no_scaled_square | ].
  split; [ exact rotation45_role_limit | ].
  split; [ exact index3_role_limit | ].
  split; [ exact order5_role_limit | exact tsirelson_role_limit ].
Qed.
