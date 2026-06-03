(** * PythagoreanTriples.v — Rational points on the unit circle, DERIVED (not ad hoc)

    Elements: rational parameter t ∈ ℚ; integer pair (m,n); the triples themselves
              (3-4-5, 5-12-13, …) — all finite, actual over ℚ (L1 + P4)
    Roles:    a point (a,b) ∈ S¹ as the role a parameter plays; the EXCLUDED point
              (−1,0) = t→∞ as a role-limit (the single gap of the parametrization
              IS the P4-boundary); primitive vs non-primitive triple
    Rules:    a² + b² = 1 (defining rule); Euclid (m²−n²)²+(2mn)² = (m²+n²)²
              (pure ring, division-free); the stereographic map
              t ↦ ((1−t²)/(1+t²), 2t/(1+t²)) is the GENERATOR of all rational
              circle points; tangent-addition t ⊕ s = (t+s)/(1−ts) is the group law

    PURPOSE. Until now the Pythagorean triples were AD HOC: 3-4-5 and 5-12-13 were
    hard-coded in TimeDilation.v, NumericalPredictions.v, QubitThreeFormulas.v,
    SHOThreeFormulas.v, GaugeFieldFromConnection.v, process_qm/HilbertAsProcess.v.
    Here they become DERIVED: each is an instance of the single parametrization
    `param`. The "magic" constant 3-4-5 is just t = 1/2; 5-12-13 is t = 1/5; and
    composing the t=1/2 and t=1/3 rotations lands exactly on the quarter-turn
    (0,1) = i (the generator of Z₄ in ConnectionCircle.v). The Elements layer of
    the whole ℚ-kinematics program is now derived from ℚ itself, not illustrated.

    ============ E/R/R разбор ============
      Rules (L5): a²+b²=1; Euclid-тождество (чистый ring); стереографическая карта
                  как ПОРОЖДАЮЩЕЕ правило; тангенс-сложение = групповой закон.
      Roles (L4): точка (a,b) ∈ S¹ — роль параметра; (−1,0) = t→∞ = role-limit
                  (единственный пробел параметризации = P4-граница); примитивность.
      Elements  : t ∈ ℚ, пара (m,n), сами тройки — конечно-актуальны (L1+P4).
    ДИАГНОСТИКА (P4-граница): точка (−1,0) недостижима НИ ОДНИМ t∈ℚ — предел
    процесса t→∞, встроенный role-limit (`px_ne_neg1`) ⟹ ниточка прямо в теорему-
    границу финитизации. Континуальная окружность = role-limit плотного ℚ-процесса
    (плотность — следующий файл). Магические тройки = экземпляры `param`, не атомы.

    STATUS: 21 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
Open Scope Q_scope.

(* ===================================================================== *)
(*  PART I — Element core: Euclid's identity (pure ring, division-free)   *)
(* ===================================================================== *)

(** Euclid's identity: every (m,n) yields a Pythagorean triple. The
    rational/integer HEART of the construction — no division, pure ring. *)
Lemma euclid_identity : forall m n : Q,
  (m*m - n*n) * (m*m - n*n) + (2*m*n) * (2*m*n)
  == (m*m + n*n) * (m*m + n*n).
Proof. intros m n. ring. Qed.

(** The 3-4-5 triple is the instance (m,n) = (2,1): 3² + 4² = 5². *)
Example triple_3_4_5 :
  (2*2 - 1*1) * (2*2 - 1*1) + (2*2*1) * (2*2*1)
  == (2*2 + 1*1) * (2*2 + 1*1).
Proof. exact (euclid_identity 2 1). Qed.

(* ===================================================================== *)
(*  PART II — Denominator positivity (1 + t² > 0 always over ℚ)           *)
(* ===================================================================== *)

(** A square is nonnegative over ℚ (no `nra`/`Qsqr_nonneg` in this stdlib). *)
Lemma Qsqr_nonneg' : forall t : Q, 0 <= t * t.
Proof.
  intro t. destruct (Qlt_le_dec t 0) as [Hlt | Hge].
  - assert (Hnn : 0 <= (-t) * (-t)) by (apply Qmult_le_0_compat; lra).
    assert (Heq : (-t) * (-t) == t * t) by ring.
    rewrite Heq in Hnn. exact Hnn.
  - apply Qmult_le_0_compat; lra.
Qed.

Lemma one_plus_sq_pos : forall t : Q, 0 < 1 + t * t.
Proof. intro t. pose proof (Qsqr_nonneg' t). lra. Qed.

Lemma one_plus_sq_nz : forall t : Q, ~ (1 + t * t == 0).
Proof. intro t. pose proof (one_plus_sq_pos t). lra. Qed.

(* ===================================================================== *)
(*  PART III — Rule: the stereographic parametrization (the GENERATOR)    *)
(* ===================================================================== *)

(** Rational point on the unit circle from a rational parameter t. *)
Definition px (t : Q) : Q := (1 - t*t) / (1 + t*t).
Definition py (t : Q) : Q := (2*t)   / (1 + t*t).

Definition on_circle (a b : Q) : Prop := a*a + b*b == 1.

(** THE THEOREM: every rational parameter lands on the unit circle.
    So rational circle points are GENERATED from ℚ — derived, not listed. *)
Theorem param_on_circle : forall t : Q, on_circle (px t) (py t).
Proof.
  intro t. unfold on_circle, px, py.
  field; apply one_plus_sq_nz.
Qed.

(* ===================================================================== *)
(*  PART IV — Elements: the scattered ad hoc triples are now INSTANCES    *)
(* ===================================================================== *)

(** (3/5, 4/5) lies on the circle: 9/25 + 16/25 = 1. *)
Example tfv_on_circle : on_circle (3#5) (4#5).
Proof. unfold on_circle. vm_compute. reflexivity. Qed.

(** ...and it is exactly the instance t = 1/2.  3-4-5 = param(1/2). *)
Example three_four_five_is_param_half :
  px (1#2) == 3#5 /\ py (1#2) == 4#5.
Proof. split; vm_compute; reflexivity. Qed.

(** The 5-12-13 triple is the instance t = 1/5. *)
Example five_twelve_thirteen_is_param_fifth :
  px (1#5) == 12#13 /\ py (1#5) == 5#13.
Proof. split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  PART V — Rule: tangent-addition group law (concrete witness)          *)
(* ===================================================================== *)

(** Composition of rational rotations corresponds to tangent-addition
    on the parameter: R(t)·R(s) = R(t⊕s). *)
Definition tplus (t s : Q) : Q := (t + s) / (1 - t*s).

(** Composition of two planar points = the complex/rotation product.
    The SHARED primitive of the whole ℚ-kinematics cluster — kept
    self-contained (pairs over ℚ), no ComplexOverQ/Mat2 import, so the
    cluster stays robust to stale .vo. *)
Definition cmul (p q : Q * Q) : Q * Q :=
  (fst p * fst q - snd p * snd q, fst p * snd q + snd p * fst q).

(** 1 − t·s ≠ 0 is the role-limit hypothesis: t·s = 1 ⟺ t⊕s → ∞ = (−1,0). *)
Lemma one_minus_ts_nz : forall t s : Q, ~ (t * s == 1) -> ~ (1 - t * s == 0).
Proof. intros t s H Hc. apply H. lra. Qed.

(** Cleared-denominator factorizations (scale 1±u² and u by (1−ts)²).
    The key ring fact underneath: (1−ts)² + (t+s)² = (1+t²)(1+s²). *)
Lemma one_plus_u2 : forall t s : Q, ~ (t * s == 1) ->
  (1 + tplus t s * tplus t s) * ((1 - t*s) * (1 - t*s)) == (1 + t*t) * (1 + s*s).
Proof. intros t s Hts. unfold tplus. field. apply one_minus_ts_nz; exact Hts. Qed.

Lemma one_minus_u2 : forall t s : Q, ~ (t * s == 1) ->
  (1 - tplus t s * tplus t s) * ((1 - t*s) * (1 - t*s))
  == (1 - t*t) * (1 - s*s) - 4 * (t*s).
Proof. intros t s Hts. unfold tplus. field. apply one_minus_ts_nz; exact Hts. Qed.

Lemma num_u2 : forall t s : Q, ~ (t * s == 1) ->
  tplus t s * ((1 - t*s) * (1 - t*s)) == (t + s) * (1 - t*s).
Proof. intros t s Hts. unfold tplus. field. apply one_minus_ts_nz; exact Hts. Qed.

(** Closed coordinates of the summed-parameter point (no nested fractions). *)
Lemma px_tplus_closed : forall t s : Q, ~ (t * s == 1) ->
  px (tplus t s) == ((1 - t*t) * (1 - s*s) - 4 * (t*s)) / ((1 + t*t) * (1 + s*s)).
Proof.
  intros t s Hts.
  pose proof (one_minus_ts_nz t s Hts) as HD.
  rewrite <- (one_plus_u2 t s Hts), <- (one_minus_u2 t s Hts).
  unfold px. field. split; solve [ exact HD | apply one_plus_sq_nz ].
Qed.

Lemma py_tplus_closed : forall t s : Q, ~ (t * s == 1) ->
  py (tplus t s) == (2 * ((t + s) * (1 - t*s))) / ((1 + t*t) * (1 + s*s)).
Proof.
  intros t s Hts.
  pose proof (one_minus_ts_nz t s Hts) as HD.
  rewrite <- (one_plus_u2 t s Hts), <- (num_u2 t s Hts).
  unfold py. field. split; solve [ exact HD | apply one_plus_sq_nz ].
Qed.

(** Composition coordinates in closed form (clean field, denoms 1+t², 1+s²). *)
Lemma compose_fst_closed : forall t s : Q,
  px t * px s - py t * py s
  == ((1 - t*t) * (1 - s*s) - 4 * (t*s)) / ((1 + t*t) * (1 + s*s)).
Proof. intros t s. unfold px, py. field. split; apply one_plus_sq_nz. Qed.

Lemma compose_snd_closed : forall t s : Q,
  px t * py s + py t * px s
  == (2 * ((t + s) * (1 - t*s))) / ((1 + t*t) * (1 + s*s)).
Proof. intros t s. unfold px, py. field. split; apply one_plus_sq_nz. Qed.

(** ★ THE GROUP LAW (general): R(t)·R(s) = R(t⊕s) on rational circle points.
    SO(2,ℚ) ≅ (ℚ ∪ {∞}, tangent-addition). Previously only a numeric witness;
    now a theorem — the Rules (L5) layer of the foundation is complete. *)
Theorem param_group_law : forall t s : Q, ~ (t * s == 1) ->
  fst (cmul (px t, py t) (px s, py s)) == px (tplus t s) /\
  snd (cmul (px t, py t) (px s, py s)) == py (tplus t s).
Proof.
  intros t s Hts. unfold cmul; simpl. split.
  - rewrite (px_tplus_closed t s Hts). apply compose_fst_closed.
  - rewrite (py_tplus_closed t s Hts). apply compose_snd_closed.
Qed.

(** Concrete witness of the group law: composing the t=1/2 and t=1/3
    rotations gives t=1, whose point is (0,1) — the quarter-turn i,
    the generator of Z₄ in ConnectionCircle.v. The group structure of
    SO(2,ℚ) is real, and it closes onto the known rational subgroup. *)
Example compose_half_third_is_quarter_turn :
  tplus (1#2) (1#3) == 1 /\ px 1 == 0 /\ py 1 == 1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  PART VI — Role-limit: the point (−1,0) is unreachable (P4-boundary)   *)
(* ===================================================================== *)

(** The single gap of the stereographic chart, (−1,0), is reached only in
    the limit t→∞ — NO rational t actualizes it. This is the built-in
    P4-boundary: the continuum point is a role-limit of the ℚ-process,
    exactly the demarcation the finitization-boundary theorem formalizes. *)
Lemma px_ne_neg1 : forall t : Q, ~ (px t == -1).
Proof.
  intros t H. unfold px in H.
  assert (Hmul : (1 - t*t) == (-1) * (1 + t*t)).
  { rewrite <- H. field; apply one_plus_sq_nz. }
  lra.
Qed.

(* ===================================================================== *)
(*  PART VII — Element face: integer triples & primitivity (via gcd)      *)
(* ===================================================================== *)

(* Replicated from stdlib/GCD.v to keep this leaf self-contained. *)
Definition coprime (a b : nat) : Prop := Nat.gcd a b = 1%nat.

(** The generator (m,n) = (2,1) of the 3-4-5 triple is primitive:
    gcd(2,1)=1. Primitivity connects the rational chart to the
    number-theoretic (integer) face of the Elements. *)
Lemma coprime_2_1 : coprime 2 1.
Proof. unfold coprime. reflexivity. Qed.
