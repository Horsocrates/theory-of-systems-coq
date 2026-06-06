(** * H1CubicConstructivity.v — H1's constructive half, ONE DEGREE UP: decidable on the CUBIC class.
       H1ConstructivityDecidable proved the Element/role-limit sort is a constructive decider on the
       QUADRATIC discriminant class (∃r:ℚ, r²=D).  This lifts it to the CUBIC class (∃r:ℚ, r³=D): the sort
       is again a CONSTRUCTIVE TOTAL DECIDER (0 axioms), so the LEM-instance `CubeElement D ∨ ~CubeElement D`
       is again a THEOREM.  H1's constructivity is thereby shown DEGREE-STRATIFIED (degrees 2 and 3),
       realizing H8 ("the finitization boundary is stratified by algebraic degree") AS A DECISION THEOREM.

       The new work is an integer CUBE-ROOT decider (Stdlib has Z.sqrt but no Z.cbrt): decide perfect-cube
       by a bounded search on |D| (the cube root is bounded by |D|) plus a sign step, then bridge to ℚ via
       GeneralCbrt.rational_cube_is_perfect_cube.  ∛2 (Delian cube-doubling, a classical Greek impossibility)
       is the canonical degree-3 role-limit.

    WHAT THE REPO HAS (surveyed): GeneralCbrt.v — the ℚ↔ℤ cube bridge `rational_cube_is_perfect_cube`,
    `not_cube_strict`, and the role-limits cbrt2/3/5/9, the Element cbrt8 (all reused here).  GeneralRoot.v —
    the degree-uniform BRIDGE engine (induction on k).  GAP: no DECISION PROCEDURE at degree 3 (no integer
    cube-root decider, no LEM-instance theorem).  This adds it.

    ============ E/R/R разбор ============
      Elements : дискриминант/радиканд D:ℤ; предикат CubeElement D := ∃r:ℚ, r³=D; целый куб ∃m:ℤ, m³=D.
      Roles    : CubeElement = ∛-роль реализуется рациональным свидетелем (Element); cube_role_limit = не
                 реализуется над ℚ (∛D нетерминирующий, напр. ∛2 делийское).
      Rules    : сорт вычислим (поиск кубического корня по |D| + знак) ⟹ LEM-инстанс — ТЕОРЕМА (0-акс) и на степени 3.
      ДИАГНОСТИКА (P4): конструктивная половина H1 СТРАТИФИЦИРОВАНА ПО СТЕПЕНИ — решающая теорема на степени 2
      (квадрат) И 3 (куб), как движок GeneralRoot. ∛2 = канонический degree-3 role-limit (удвоение куба). ЧЕСТНО:
      степени 2,3 решены; общий-k decider (k-й корень над ℤ) — дальше; «role-limit требует РОВНО classic» — мета.
      Уровень: `синтез` (кубический корень над ℤ ⊕ мост GeneralCbrt → degree-3 decider + LEM-теорема).

    STATUS: 14 Qed, 0 Admitted, 0 axioms  (builds on stdlib.GeneralCbrt)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith List Bool.
From ToS Require Import stdlib.GeneralCbrt.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Degree-3 Element / role-limit predicate                                *)
(* ===================================================================== *)

(** CubeElement D: the role x³ = D is realized by a RATIONAL witness (Element). *)
Definition CubeElement (D : Z) : Prop := exists r : Q, (r * r * r == inject_Z D)%Q.

(** cube_role_limit D: not realized over ℚ (the non-terminating ∛D, e.g. the Delian ∛2). *)
Definition cube_role_limit (D : Z) : Prop := ~ CubeElement D.

(** CubeElement is exactly the integer perfect-cube predicate (forward: GeneralCbrt bridge; back: inject_Z). *)
Lemma cubeelement_iff_intcube : forall D : Z, CubeElement D <-> exists m : Z, m * m * m = D.
Proof.
  intro D. split.
  - intros [r Hr]. destruct (rational_cube_is_perfect_cube r D Hr) as [m Hm].
    exists m. symmetry. exact Hm.
  - intros [m Hm]. exists (inject_Z m). rewrite <- Hm.
    rewrite !inject_Z_mult. ring.
Qed.

(* ===================================================================== *)
(*  An integer cube-root decider (Stdlib has no Z.cbrt): bounded search    *)
(* ===================================================================== *)

(** Decide whether N:nat is a perfect cube, by a bounded search (the root is ≤ N). *)
Definition is_cube_nat (N : nat) : bool :=
  existsb (fun k => Nat.eqb (k * k * k)%nat N) (seq 0 (S N)).

Lemma is_cube_nat_correct : forall N : nat, is_cube_nat N = true <-> exists k : nat, (k * k * k)%nat = N.
Proof.
  intro N. unfold is_cube_nat. rewrite existsb_exists. split.
  - intros [k [_ Hk]]. exists k. apply Nat.eqb_eq. exact Hk.
  - intros [k Hk]. exists k. split.
    + apply in_seq. split; [ lia | ].
      assert (Hle : (k <= k * k * k)%nat) by nia. lia.
    + apply Nat.eqb_eq. exact Hk.
Qed.

(** Z.to_nat distributes over a cube of a non-negative integer. *)
Lemma Z2Nat_cube : forall a : Z, 0 <= a ->
  Z.to_nat (a * a * a) = (Z.to_nat a * Z.to_nat a * Z.to_nat a)%nat.
Proof.
  intros a Ha. rewrite Z2Nat.inj_mul by nia. rewrite Z2Nat.inj_mul by nia. reflexivity.
Qed.

(** An integer is a perfect cube iff its absolute value (as a nat) is a perfect cube — the cube root has
    the same magnitude and the sign of D (cube preserves sign). *)
Lemma intcube_iff_abs : forall D : Z,
  (exists m : Z, m * m * m = D) <-> (exists k : nat, (k * k * k)%nat = Z.to_nat (Z.abs D)).
Proof.
  intro D. split.
  - intros [m Hm]. exists (Z.to_nat (Z.abs m)).
    rewrite <- Z2Nat_cube by apply Z.abs_nonneg.
    f_equal. rewrite <- !Z.abs_mul. rewrite Hm. reflexivity.
  - intros [k Hk]. destruct (Z_le_dec 0 D) as [Hpos | Hneg].
    + exists (Z.of_nat k).
      rewrite <- !Nat2Z.inj_mul. rewrite Hk.
      rewrite Z2Nat.id by apply Z.abs_nonneg. apply Z.abs_eq. exact Hpos.
    + exists (- Z.of_nat k).
      assert (Hc : (- Z.of_nat k) * (- Z.of_nat k) * (- Z.of_nat k)
                   = - (Z.of_nat k * Z.of_nat k * Z.of_nat k)) by ring.
      rewrite Hc. rewrite <- !Nat2Z.inj_mul. rewrite Hk.
      rewrite Z2Nat.id by apply Z.abs_nonneg.
      rewrite Z.abs_neq by lia. ring.
Qed.

(* ===================================================================== *)
(*  ★★★ THE DEGREE-3 DECISION PROCEDURE                                    *)
(* ===================================================================== *)

(** ★★★ The cubic Element/role-limit sort is a CONSTRUCTIVE TOTAL DECISION PROCEDURE over ℚ: for every
    radicand D it returns a proof of which side of the finitization boundary ∛D lies on — 0 axioms. *)
Lemma decide_cubeelement : forall D : Z, {CubeElement D} + {~ CubeElement D}.
Proof.
  intro D. destruct (is_cube_nat (Z.to_nat (Z.abs D))) eqn:E.
  - left. apply cubeelement_iff_intcube, intcube_iff_abs, is_cube_nat_correct. exact E.
  - right. intro HC.
    apply cubeelement_iff_intcube, intcube_iff_abs, is_cube_nat_correct in HC.
    rewrite HC in E. discriminate.
Qed.

(** ★★ The LEM-instance for the cubic predicate is a THEOREM (0-axiom), not an axiom — degree 3. *)
Lemma cube_element_or_rolelimit : forall D : Z, CubeElement D \/ cube_role_limit D.
Proof. intro D. destruct (decide_cubeelement D) as [H | H]; [ left | right ]; exact H. Qed.

Lemma cube_not_both : forall D : Z, ~ (CubeElement D /\ cube_role_limit D).
Proof. intros D [HE HR]. apply HR. exact HE. Qed.

(* ===================================================================== *)
(*  Concrete (reusing GeneralCbrt): ∛8 Element ; ∛2, ∛3, ∛5, ∛9 role-limit *)
(* ===================================================================== *)

(** Element: ∛8 = 2 (a perfect cube). *)
Lemma cube_element_8 : CubeElement 8.
Proof. exists (inject_Z 2). exact cbrt8_element. Qed.

(** role-limit: ∛2 — the Delian cube-doubling, the canonical degree-3 role-limit. *)
Lemma cube_rolelimit_2 : cube_role_limit 2.
Proof. exact cbrt2_role_limit. Qed.

Lemma cube_rolelimit_3 : cube_role_limit 3.
Proof. exact cbrt3_role_limit. Qed.

Lemma cube_rolelimit_5 : cube_role_limit 5.
Proof. exact cbrt5_role_limit. Qed.

(** ∛9: between the cubes 8 = 2³ and 27 = 3³ — role-limit (≠ √-tier; degree-3 stratification). *)
Lemma cube_rolelimit_9 : cube_role_limit 9.
Proof. exact cbrt9_role_limit. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** H1's constructive half, one degree up — decidable on the CUBIC class:
      (LEM = thm)  `CubeElement D ∨ cube_role_limit D` is a THEOREM, 0-axiom (degree 3);
      (exclusive)  nothing is both;
      (Element)    ∛8 = 2 — Element;
      (role-limit) ∛2 (Delian), ∛3, ∛5, ∛9 — role-limit.
    Together with H1ConstructivityDecidable (degree 2), H1's constructivity is now DEGREE-STRATIFIED — a
    decision theorem at degrees 2 and 3 — realizing H8 (the boundary stratified by algebraic degree) as a
    THEOREM, not an observation.  Honest: degrees 2 and 3 are done; a general-k decider (a k-th-root search
    over ℤ) is the next frontier; the "role-limit needs exactly classic" direction remains axiom-budget meta. *)
Theorem H1_cubic_constructive_half :
  (forall D : Z, CubeElement D \/ cube_role_limit D)
  /\ (forall D : Z, ~ (CubeElement D /\ cube_role_limit D))
  /\ CubeElement 8
  /\ cube_role_limit 2
  /\ cube_role_limit 3
  /\ cube_role_limit 5
  /\ cube_role_limit 9.
Proof.
  split. exact cube_element_or_rolelimit.
  split. exact cube_not_both.
  split. exact cube_element_8.
  split. exact cube_rolelimit_2.
  split. exact cube_rolelimit_3.
  split. exact cube_rolelimit_5.
  exact cube_rolelimit_9.
Qed.
