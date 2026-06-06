(** * DeterminantModB.v — the determinant library closing GENERAL n: a rational eigenvalue of an n×n
       integer matrix is an INTEGER, for EVERY n.  GeneralEigenvalueIntegral proved the logical core
       (aⁿ + b·K = 0 ⟹ b = 1) and localized the gap to the matrix input det(aI−bA) = aⁿ + b·K.  This builds
       a cofactor determinant for arbitrary n and proves that input via the mod-b route:
         det respects entrywise ≡ (mod b)  [det_congr_mod_b]  +  det(aI) = aⁿ  [det_scalar]
         ⟹ det(aI−bA) ≡ aⁿ (mod b)  ⟹  det(aI−bA) = aⁿ + b·K  ⟹  (core) b = 1.
       aI−bA ≡ aI (mod b) entrywise (−bA vanishes mod b), and a determinant — a polynomial in the entries —
       respects that congruence.  No characteristic-polynomial coefficients are computed; only the leading
       aⁿ (det(aI)) and the b-divisibility of the rest matter.

    -- The determinant --
      Matrices as functions nat→nat→ℤ; cofactor (Laplace) expansion along the first row, fuel = dimension n:
        detf 0 M = 1;  detf (S k) M = Σ_{j<S k} (−1)ʲ · M 0 j · detf k (minor M j),  minor removes row 0, col j.

    WHAT THE REPO HAS (surveyed): GeneralEigenvalueIntegral (the core + the localized gap); RationalRootTest
    (Gauss).  No determinant.  GAP: an n×n determinant + the two properties closing the general-n criterion.

    ============ E/R/R разбор ============
      Elements : функц. матрица nat→nat→ℤ; кофакторный detf (fuel=n); scalar a = aI; minor (убрать строку 0, столбец j).
      Roles    : det(aI−bA) = char-значение; aI−bA ≡ aI (mod b); det = полином, уважает ≡ mod b.
      Rules    : det_congr_mod_b + det_scalar ⟹ det(aI−bA)≡aⁿ ⟹ aⁿ+b·K ⟹ (ядро) b=1, ∀n.
      ДИАГНОСТИКА (P4): общий n ЗАМКНУТ через mod-b (определитель-полином уважает редукцию по модулю b); char-коэфф
      не вычисляются. ЧЕСТНО: кофакторная det-библиотека + два свойства; собств. значение = det(aI−bA)=0. Уровень: `синтез`.

    STATUS: 10 Qed, 0 Admitted, 0 axioms  (builds on RationalRootTest + GeneralEigenvalueIntegral)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory List Arith.
From ToS Require Import algebra.RationalRootTest.
From ToS Require Import foundation.GeneralEigenvalueIntegral.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Function matrices, scalar matrix, minor, cofactor determinant           *)
(* ===================================================================== *)

Definition scalar (a : Z) : nat -> nat -> Z := fun i j => if Nat.eqb i j then a else 0.

Definition minor (M : nat -> nat -> Z) (j0 : nat) : nat -> nat -> Z :=
  fun i j => M (S i) (if Nat.ltb j j0 then j else S j).

Definition cof (a : Z) (j : nat) : Z := if Nat.even j then a else - a.

Fixpoint detf (n : nat) (M : nat -> nat -> Z) : Z :=
  match n with
  | O => 1
  | S k => fold_right Z.add 0 (map (fun j => cof (M O j) j * detf k (minor M j)) (seq 0 (S k)))
  end.

(* ===================================================================== *)
(*  Helpers on fold_right / map                                            *)
(* ===================================================================== *)

Lemma fold_all_zero : forall l : list Z, (forall x, In x l -> x = 0) -> fold_right Z.add 0 l = 0.
Proof.
  induction l as [| x l IH]; intro H; [ reflexivity | ].
  simpl. rewrite (H x (or_introl eq_refl)). rewrite IH; [ reflexivity | ].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma div_fold_add : forall (b : Z) (l : list Z),
  (forall x, In x l -> (b | x)) -> (b | fold_right Z.add 0 l).
Proof.
  intros b. induction l as [| x l IH]; intro H; simpl.
  - apply Z.divide_0_r.
  - apply Z.divide_add_r; [ apply H; left; reflexivity | apply IH; intros y Hy; apply H; right; exact Hy ].
Qed.

Lemma fold_map_sub : forall {A} (f g : A -> Z) (l : list A),
  fold_right Z.add 0 (map f l) - fold_right Z.add 0 (map g l)
  = fold_right Z.add 0 (map (fun x => f x - g x) l).
Proof.
  intros A f g. induction l as [| x l IH]; simpl; [ ring | rewrite <- IH; ring ].
Qed.

(* ===================================================================== *)
(*  Extensionality: det depends only on the n×n block                       *)
(* ===================================================================== *)

Lemma detf_ext : forall (n : nat) (M M' : nat -> nat -> Z),
  (forall i j, (i < n)%nat -> (j < n)%nat -> M i j = M' i j) -> detf n M = detf n M'.
Proof.
  induction n as [| k IH]; intros M M' Hext; [ reflexivity | ].
  cbn [detf]. f_equal. apply map_ext_in. intros j Hj. apply in_seq in Hj.
  rewrite (Hext O j ltac:(lia) ltac:(lia)). f_equal.
  apply IH. intros i jj Hi Hjj. unfold minor.
  apply Hext; [ lia | destruct (Nat.ltb jj j); lia ].
Qed.

(* ===================================================================== *)
(*  det(aI) = aⁿ                                                            *)
(* ===================================================================== *)

Lemma minor_scalar0 : forall a i j, minor (scalar a) 0 i j = scalar a i j.
Proof.
  intros a i j. unfold minor, scalar.
  replace (Nat.ltb j 0) with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma det_scalar : forall (n : nat) (a : Z), detf n (scalar a) = zpow a n.
Proof.
  induction n as [| k IH]; intro a; [ reflexivity | ].
  cbn [detf]. replace (seq 0 (S k)) with (0%nat :: seq 1 k) by reflexivity.
  cbn [map fold_right].
  assert (Htail : fold_right Z.add 0
      (map (fun j => cof (scalar a O j) j * detf k (minor (scalar a) j)) (seq 1 k)) = 0).
  { apply fold_all_zero. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [j [Hj Hin]]. apply in_seq in Hin. unfold cof, scalar in Hj.
    replace (Nat.eqb O j) with false in Hj by (symmetry; apply Nat.eqb_neq; lia).
    rewrite <- Hj. destruct (Nat.even j); ring. }
  rewrite Htail, Z.add_0_r.
  rewrite (detf_ext k (minor (scalar a) 0) (scalar a)) by (intros; apply minor_scalar0).
  rewrite IH.
  unfold cof, scalar. cbn [Nat.even Nat.eqb zpow]. ring.
Qed.

(* ===================================================================== *)
(*  det respects entrywise ≡ (mod b)                                       *)
(* ===================================================================== *)

Lemma det_congr_mod_b : forall (b : Z) (n : nat) (M M' : nat -> nat -> Z),
  (forall i j, (i < n)%nat -> (j < n)%nat -> (b | (M i j - M' i j))) ->
  (b | (detf n M - detf n M')).
Proof.
  induction n as [| k IH]; intros M M' Hc.
  - cbn [detf]. replace (1 - 1) with 0 by ring. apply Z.divide_0_r.
  - cbn [detf]. rewrite fold_map_sub. apply div_fold_add. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [j [Hj Hin]]. apply in_seq in Hin. rewrite <- Hj.
    unfold cof.
    assert (HM0 : (b | (M O j - M' O j))) by (apply Hc; lia).
    assert (HD : (b | (detf k (minor M j) - detf k (minor M' j)))).
    { apply IH. intros i jj Hi Hjj. unfold minor. apply Hc; [ lia | destruct (Nat.ltb jj j); lia ]. }
    set (P := detf k (minor M j)) in *. set (Q := detf k (minor M' j)) in *.
    destruct (Nat.even j);
      [ replace (M O j * P - M' O j * Q) with ((M O j - M' O j) * P + M' O j * (P - Q)) by ring
      | replace (- M O j * P - - M' O j * Q) with ((M O j - M' O j) * (- P) + (- M' O j) * (P - Q)) by ring ];
      apply Z.divide_add_r;
      solve [ apply Z.divide_mul_l; exact HM0 | apply Z.divide_mul_r; exact HD ].
Qed.

(* ===================================================================== *)
(*  ★★ A rational eigenvalue of an n×n integer matrix is an integer (∀n)    *)
(* ===================================================================== *)

(** The characteristic matrix aI − bA (cleared of the denominator b): entry a·[i=j] − b·A i j. *)
Definition charmat (a b : Z) (A : nat -> nat -> Z) : nat -> nat -> Z :=
  fun i j => scalar a i j - b * A i j.

(** ★★ At EVERY dimension n: a rational eigenvalue a/b (lowest terms, b>0) of an integer n×n matrix A —
    i.e. det(aI − bA) = 0, the cleared eigenvalue equation — is an INTEGER (b = 1).  Closes the general n. *)
Theorem rational_eigenvalue_nxn_is_integer : forall (n : nat) (A : nat -> nat -> Z) (a b : Z),
  rel_prime a b -> b > 0 -> detf n (charmat a b A) = 0 -> b = 1.
Proof.
  intros n A a b Hrp Hbpos Heig.
  assert (Hcongr : (b | (detf n (charmat a b A) - detf n (scalar a)))).
  { apply det_congr_mod_b. intros i j _ _. unfold charmat.
    replace (scalar a i j - b * A i j - scalar a i j) with (b * (- A i j)) by ring.
    exists (- A i j). ring. }
  rewrite det_scalar in Hcongr. rewrite Heig in Hcongr.
  destruct Hcongr as [K HK].
  apply (eigenvalue_integral_general n a b K Hrp Hbpos). nia.
Qed.

(* ===================================================================== *)
(*  Concrete: a 2×2 and the determinant runs                               *)
(* ===================================================================== *)

(** detf computes: det of diag(2,3) at the char point (a,b)=(2,1) is 0 (eigenvalue 2). *)
Example det2_diag23_eig2 :
  detf 2 (charmat 2 1 (fun i j => if Nat.eqb i j then (if Nat.eqb i 0 then 2 else 3) else 0)) = 0.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The determinant library closing general n:
      (det aI)     detf n (scalar a) = aⁿ;
      (congruence) det respects entrywise ≡ (mod b);
      (∀n)         a rational eigenvalue of an integer n×n matrix is an INTEGER (b=1), every dimension.
    So the n×n eigenvalue-rationality criterion is closed for ALL n: a rational eigenvalue of an integer
    matrix is an integer (dividing det), decidable.  The leading aⁿ comes from det(aI); everything else is
    b-divisible (the determinant respects reduction mod b).  Honest: "eigenvalue" = det(aI−bA)=0 (the cleared
    characteristic equation — standard); the determinant is the cofactor expansion, built here. *)
Theorem determinant_closes_general_n :
  (forall n a, detf n (scalar a) = zpow a n)
  /\ (forall b n M M', (forall i j, (i < n)%nat -> (j < n)%nat -> (b | (M i j - M' i j))) ->
        (b | (detf n M - detf n M')))
  /\ (forall n A a b, rel_prime a b -> b > 0 -> detf n (charmat a b A) = 0 -> b = 1).
Proof.
  split. exact det_scalar.
  split. exact det_congr_mod_b.
  exact rational_eigenvalue_nxn_is_integer.
Qed.
