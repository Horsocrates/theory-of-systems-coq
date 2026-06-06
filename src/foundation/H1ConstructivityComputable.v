(** * H1ConstructivityComputable.v — sharpening H1's constructive half from DECIDABLE to COMPUTABLE.
       H1ConstructivityDecidable proved the Element/role-limit sort is DECIDABLE (a sumbool, 0-axiom), but
       that decider is Qed-opaque (it routes through opaque lemmas), so it does not REDUCE.  This file gives
       the sort as a RUNNING boolean function `is_element_b : Z -> bool` (via the computable Nat.sqrt-based
       `is_square`), proves it correct, packages it as a `reflect`, and RUNS it as the reduction-atlas
       master valve on concrete integer 2×2 matrices (Δ = tr²−4det, "perfect square?").  This is the
       strongest form of "the Element side is the constructive side": not decidable-in-principle, but a
       boolean that `vm_compute`s.

    WHAT THE REPO HAS (surveyed): SortDecidable.is_square (computable Nat.sqrt test) + is_square_iff;
    GeneralSqrt.rational_square_is_perfect (ℚ→ℤ bridge); H1ConstructivityDecidable (ElementZ/role_limit +
    the sumbool decider).  GAP: no COMPUTABLE boolean sort that actually runs (the sumbool doesn't reduce).
    This adds it, reusing the SAME arithmetic, and runs it on the atlas discriminants.

    ============ E/R/R разбор ============
      Elements : дискриминант D:ℤ; булева функция-сорт is_element_b D (вычислима, через is_square=Nat.sqrt).
      Roles    : is_element_b = РАБОТАЮЩИЙ сорт (true=Element, false=role-limit); reflect связывает bool↔Prop.
      Rules    : is_element_b D = true ⟺ ElementZ D (та же арифметика, что в decide_elementZ); сорт БЕЖИТ (vm_compute).
      ДИАГНОСТИКА (P4): конструктивность Element-сорта заострена с «разрешимо» (sumbool) до «вычислимо» (булева
      функция + reflect) — сильнейший свидетель «Element-сторона конструктивна»: сорт не «в принципе», а реально
      бежит и сортирует матрицы атласа по Δ. ЧЕСТНО: степень 2; степень-3 (H8) — следующий рунг (инфра GeneralCbrt
      готова). Уровень: `синтез` (вычислимая+рефлективная форма decide_elementZ + запуск как вентиль атласа).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia QArith Bool.
From ToS Require Import foundation.SortDecidable.
From ToS Require Import stdlib.GeneralSqrt.
From ToS Require Import foundation.H1ConstructivityDecidable.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The sort as a RUNNING boolean function                                 *)
(* ===================================================================== *)

(** The Element/role-limit sort as a computable boolean: D is Element iff D >= 0 and Z.to_nat D is a
    perfect square (the Nat.sqrt-based `is_square`, which actually reduces). *)
Definition is_element_b (D : Z) : bool := (0 <=? D) && is_square (Z.to_nat D).

(** ★★ Correctness: the running boolean agrees with the Prop predicate (same arithmetic as decide_elementZ). *)
Lemma is_element_b_correct : forall D : Z, is_element_b D = true <-> ElementZ D.
Proof.
  intro D. unfold is_element_b. rewrite andb_true_iff. split.
  - intros [Hpos Hsq]. apply Z.leb_le in Hpos. apply is_square_iff in Hsq.
    destruct Hsq as [r Hr]. exists (inject_Z (Z.of_nat r)).
    rewrite <- inject_Z_mult.
    assert (E : (Z.of_nat r * Z.of_nat r)%Z = D).
    { rewrite <- Nat2Z.inj_mul, Hr. apply Z2Nat.id. exact Hpos. }
    rewrite E. reflexivity.
  - intros [q Hq]. destruct (rational_square_is_perfect q D Hq) as [m Hm].
    assert (Hpos : (0 <= D)%Z) by nia. split.
    + apply Z.leb_le. exact Hpos.
    + apply is_square_iff. exists (Z.to_nat (Z.abs m)).
      rewrite <- Z2Nat.inj_mul by apply Z.abs_nonneg.
      f_equal. rewrite <- Z.abs_mul, Z.abs_eq by nia. symmetry. exact Hm.
Qed.

(** ★ The sort as a `reflect`: the strongest packaging — the boolean and the Prop are interchangeable. *)
Lemma is_element_reflect : forall D : Z, reflect (ElementZ D) (is_element_b D).
Proof. intro D. apply iff_reflect. symmetry. apply is_element_b_correct. Qed.

(** The role-limit side as a running boolean too. *)
Definition is_role_limit_b (D : Z) : bool := negb (is_element_b D).

Lemma is_role_limit_b_correct : forall D : Z, is_role_limit_b D = true <-> role_limit D.
Proof.
  intro D. unfold is_role_limit_b, role_limit. rewrite negb_true_iff. split.
  - intros Hf HE. apply is_element_b_correct in HE. rewrite HE in Hf. discriminate.
  - intros Hne. destruct (is_element_b D) eqn:E; [ | reflexivity ].
    exfalso. apply Hne. apply is_element_b_correct. exact E.
Qed.

(* ===================================================================== *)
(*  Running the sort as the reduction-atlas master valve on 2×2 matrices   *)
(* ===================================================================== *)

(** The integer discriminant of a 2×2 matrix [[a,b],[c,d]]: Δ = tr²−4det = (a+d)²−4(ad−bc). *)
Definition mdiscZ (a b c d : Z) : Z := (a + d) * (a + d) - 4 * (a * d - b * c).

(** ★ The running master valve: feed an integer 2×2 matrix, get its Element/role-limit verdict by COMPUTING
    the discriminant and asking "perfect square?".  This is the reduction atlas, executable. *)
Definition sort_matrix (a b c d : Z) : bool := is_element_b (mdiscZ a b c d).

(** It RUNS (vm_compute) on the atlas matrices: *)
Example sort_boost345 : sort_matrix 5 3 3 5 = true.    (* Δ = 100−64 = 36 = 6²  : Element (eigs 8,2) *)
Proof. vm_compute. reflexivity. Qed.

Example sort_fibonacci : sort_matrix 1 1 1 0 = false.  (* Δ = 1+4 = 5 = √5      : role-limit (golden) *)
Proof. vm_compute. reflexivity. Qed.

Example sort_pell : sort_matrix 3 4 2 3 = false.       (* Δ = 36−4 = 32 = 4√2   : role-limit (√2) *)
Proof. vm_compute. reflexivity. Qed.

Example sort_order6 : sort_matrix 1 (-1) 1 0 = false.  (* Δ = 1−4 = −3 < 0      : role-limit (elliptic) *)
Proof. vm_compute. reflexivity. Qed.

(** Bare discriminant runs, for the record. *)
Example run_36 : is_element_b 36 = true.
Proof. vm_compute. reflexivity. Qed.

Example run_5 : is_element_b 5 = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** H1's constructive half, sharpened to a RUNNING decision function:
      (correct)   is_element_b D = true ⟺ ElementZ D (the boolean agrees with the predicate);
      (reflect)   reflect (ElementZ D) (is_element_b D) — boolean and Prop interchangeable;
      (role)      is_role_limit_b D = true ⟺ role_limit D;
      (executes)  the atlas valve runs: 3-4-5 boost (Δ=36) Element; Fibonacci (Δ=5), Pell (Δ=32),
                  order-6 (Δ=−3) role-limit — each by `vm_compute`.
    So the Element-side constructivity is not merely decidable-in-principle: the sort is a boolean that
    RUNS.  Honest: still degree 2 (the quadratic discriminant); degree 3 (the H8 cubic tier, ∛) is the
    next rung, with the GeneralCbrt bridge already in place. *)
Theorem H1_sort_is_computable :
  (forall D : Z, is_element_b D = true <-> ElementZ D)
  /\ (forall D : Z, is_role_limit_b D = true <-> role_limit D)
  /\ sort_matrix 5 3 3 5 = true
  /\ sort_matrix 1 1 1 0 = false
  /\ sort_matrix 3 4 2 3 = false
  /\ sort_matrix 1 (-1) 1 0 = false.
Proof.
  split. exact is_element_b_correct.
  split. exact is_role_limit_b_correct.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  vm_compute; reflexivity.
Qed.
