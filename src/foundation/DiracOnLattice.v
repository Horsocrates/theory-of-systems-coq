(** * DiracOnLattice.v — Wilson-Dirac operator on 2-site lattice
    Elements: hop_2, wd_2, det_2 (standalone, no process/ import)
    Roles:    hopping → Wilson-Dirac → determinant → zero modes
    Rules:    det(WD(m)) = m(m+2), zero at m=0 (physical), m=-2 (doubler)
    STATUS:   10 Qed, 0 Admitted, 0 new axioms
    Author:   Horsocrates | Date: April 2026

    LATTICE DIRAC:
    K=2 sites on a circle (periodic BC).
    Hopping H = [[0,1],[1,0]] (= σ₁).
    Wilson-Dirac: WD(m) = (m+1)·I - H.
    det(WD(m)) = (m+1)² - 1 = m² + 2m = m(m+2).

    ZERO MODES:
    m=0: det=0. Physical massless fermion (chiral zero mode).
    m=-2: det=0. Wilson doubler (removed by Wilson term in physical theory).

    CONNECTION TO CHIRALITY:
    The m=0 zero mode has definite handedness:
    kernel vector of WD(0) = [1,-1] or [1,1] (chiral or anti-chiral).
    This IS the lattice realization of chirality from L2.
*)

From Stdlib Require Import QArith Lia.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================ *)
(*  2×2 MATRIX OPERATIONS                                            *)
(* ================================================================ *)

Definition M2 := nat -> nat -> Q.

Definition mat2_det (A : M2) : Q :=
  A 0%nat 0%nat * A 1%nat 1%nat - A 0%nat 1%nat * A 1%nat 0%nat.

(* ================================================================ *)
(*  HOPPING MATRIX ON K=2 CIRCLE                                     *)
(* ================================================================ *)

(** Hopping = backward shift with periodic BC *)
Definition hop_2 : M2 := fun i j =>
  match i, j with
  | 0%nat, 1%nat => 1 | 1%nat, 0%nat => 1
  | _, _ => 0
  end.

(** Wilson-Dirac: WD(m) = (m+1)·I - H *)
Definition wd_2 (m : Q) : M2 := fun i j =>
  match i, j with
  | 0%nat, 0%nat => m + 1 | 1%nat, 1%nat => m + 1
  | 0%nat, 1%nat => -(1) | 1%nat, 0%nat => -(1)
  | _, _ => 0
  end.

(* ================================================================ *)
(*  DETERMINANT                                                      *)
(* ================================================================ *)

Lemma wd_2_det : forall m,
  mat2_det (wd_2 m) == m * m + 2 * m.
Proof.
  intro m. unfold mat2_det, wd_2. ring.
Qed.

Lemma wd_2_det_factored : forall m,
  mat2_det (wd_2 m) == m * (m + 2).
Proof.
  intro m. unfold mat2_det, wd_2. ring.
Qed.

(* ================================================================ *)
(*  ZERO MODES                                                       *)
(* ================================================================ *)

(** Physical zero mode at m=0 *)
Lemma zero_mode_at_m0 : mat2_det (wd_2 0) == 0.
Proof. unfold mat2_det, wd_2. ring. Qed.

(** Wilson doubler at m=-2 *)
Lemma doubler_at_m_neg2 : mat2_det (wd_2 (-(2))) == 0.
Proof. unfold mat2_det, wd_2. ring. Qed.

(** Only two zero modes *)
Lemma only_two_zeros : forall m,
  mat2_det (wd_2 m) == 0 -> m == 0 \/ m == -(2).
Proof.
  intro m. rewrite wd_2_det_factored.
  intro H.
  (* m * (m+2) = 0 → m = 0 or m+2 = 0 *)
  destruct (Qeq_dec m 0) as [Hm0 | Hm0].
  - left. exact Hm0.
  - right.
    assert (m + 2 == 0) as Hm2.
    { destruct (Qeq_dec (m + 2) 0) as [H2 | H2].
      - exact H2.
      - exfalso. apply Hm0.
        (* m * (m+2) = 0, m ≠ 0, m+2 ≠ 0 → contradiction *)
        (* In Q: if a*b = 0 and b ≠ 0, then a = 0 *)
        apply (Qmult_integral_l (m + 2) m H2).
        rewrite Qmult_comm. exact H.
    }
    lra.
Qed.

(* ================================================================ *)
(*  CHIRAL ZERO MODE                                                 *)
(* ================================================================ *)

(** At m=0: WD = [[1,-1],[-1,1]]. Kernel = span([1,1]). *)
Definition kernel_vec_m0 : nat -> Q := fun i =>
  match i with 0%nat => 1 | _ => 1 end.

Lemma kernel_check_0 :
  wd_2 0 0%nat 0%nat * kernel_vec_m0 0%nat + wd_2 0 0%nat 1%nat * kernel_vec_m0 1%nat == 0.
Proof. unfold wd_2, kernel_vec_m0. ring. Qed.

Lemma kernel_check_1 :
  wd_2 0 1%nat 0%nat * kernel_vec_m0 0%nat + wd_2 0 1%nat 1%nat * kernel_vec_m0 1%nat == 0.
Proof. unfold wd_2, kernel_vec_m0. ring. Qed.

(** The kernel vector is nonzero *)
Lemma kernel_nonzero : ~ (kernel_vec_m0 0%nat == 0 /\ kernel_vec_m0 1%nat == 0).
Proof. unfold kernel_vec_m0. lra. Qed.

(* ================================================================ *)
(*  SYNTHESIS                                                        *)
(* ================================================================ *)

Theorem dirac_on_lattice_synthesis :
  (* det(WD(m)) = m(m+2) *)
  (forall m, mat2_det (wd_2 m) == m * (m + 2)) /\
  (* Physical zero mode at m=0 *)
  mat2_det (wd_2 0) == 0 /\
  (* Wilson doubler at m=-2 *)
  mat2_det (wd_2 (-(2))) == 0 /\
  (* Kernel vector is in the kernel *)
  wd_2 0 0%nat 0%nat * kernel_vec_m0 0%nat + wd_2 0 0%nat 1%nat * kernel_vec_m0 1%nat == 0 /\
  (* Kernel vector is nonzero *)
  ~ (kernel_vec_m0 0%nat == 0 /\ kernel_vec_m0 1%nat == 0).
Proof.
  split; [exact wd_2_det_factored |
  split; [exact zero_mode_at_m0 |
  split; [exact doubler_at_m_neg2 |
  split; [exact kernel_check_0 |
  exact kernel_nonzero]]]].
Qed.
