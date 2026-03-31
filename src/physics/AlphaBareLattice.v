(** * AlphaBareLattice.v -- Bare coupling from Z^3 lattice eigenvalues
    Elements: cayley_re, cayley_im, beta_Z3, alpha_Z3, eigs_N2, eigs_N3
    Roles:    Compute alpha_bare at N=2 and N=3, show convergence
    Rules:    Unitarity (beta + 6*alpha = 1), alpha decreasing with N
    Status:   Physics
    STATUS: 26 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================== *)
(*  CAYLEY TRANSFORM (real and imaginary parts)                        *)
(* ================================================================== *)

(** u(lambda) = (1 + i*lambda/2) / (1 - i*lambda/2)
    |denominator|^2 = 1 + lambda^2/4 = (4 + lambda^2)/4
    Re u = (1 - lambda^2/4) / (1 + lambda^2/4) = (4 - lambda^2)/(4 + lambda^2)
    Im u = lambda / (1 + lambda^2/4) = 4*lambda/(4 + lambda^2) *)

Definition cayley_re (lambda : Q) : Q := (4 - lambda*lambda) / (4 + lambda*lambda).
Definition cayley_im (lambda : Q) : Q := 4 * lambda / (4 + lambda*lambda).

(* ================================================================== *)
(*  EIGENVALUE LIST AND WEIGHTED AVERAGES                              *)
(* ================================================================== *)

Definition EigList := list (Q * nat).

Definition weighted_sum (f : Q -> Q) (eigs : EigList) : Q :=
  fold_left (fun acc p => acc + f (fst p) * inject_Z (Z.of_nat (snd p))) eigs 0.

Definition total_count (eigs : EigList) : Q :=
  fold_left (fun acc p => acc + inject_Z (Z.of_nat (snd p))) eigs 0.

Definition weighted_avg (f : Q -> Q) (eigs : EigList) : Q :=
  weighted_sum f eigs / total_count eigs.

(** beta = |U_00|^2 = (avg Re)^2 + (avg Im)^2 *)
Definition beta_Z3 (eigs : EigList) : Q :=
  let re := weighted_avg cayley_re eigs in
  let im := weighted_avg cayley_im eigs in
  re * re + im * im.

(** alpha = (1 - beta) / z where z = 6 (coordination number of Z^3) *)
Definition alpha_Z3 (eigs : EigList) : Q := (1 - beta_Z3 eigs) / 6.

(* ================================================================== *)
(*  N=2 EIGENVALUES                                                    *)
(* ================================================================== *)

(** lambda = 2*(eps1 + eps2 + eps3) where eps_i in {1,-1}.
    Possible values: 6(x1), 2(x3), -2(x3), -6(x1). Total = 8. *)
Definition eigs_N2 : EigList := [(6,1%nat); (2,3%nat); (-(2),3%nat); (-(6),1%nat)].

(** N=3 eigenvalues: cos values {1, -1/2, -1/2} per dimension.
    lambda = 2*(sum of cos). Values: 6(x1), 3(x6), 0(x12), -3(x8). Total = 27. *)
Definition eigs_N3 : EigList := [(6,1%nat); (3,6%nat); (0,12%nat); (-(3),8%nat)].

(* ================================================================== *)
(*  TOTAL COUNTS                                                       *)
(* ================================================================== *)

Lemma total_N2 : total_count eigs_N2 == 8.
Proof. vm_compute. reflexivity. Qed.

Lemma total_N3 : total_count eigs_N3 == 27.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CAYLEY TRANSFORM SPOT CHECKS                                      *)
(* ================================================================== *)

(** (4 - 36)/(4 + 36) = -32/40 = -4/5 *)
Lemma cayley_re_6 : cayley_re 6 == -(4#5).
Proof. vm_compute. reflexivity. Qed.

(** (4 - 4)/(4 + 4) = 0/8 = 0 *)
Lemma cayley_re_2 : cayley_re 2 == 0.
Proof. vm_compute. reflexivity. Qed.

(** (4 - 0)/(4 + 0) = 4/4 = 1 *)
Lemma cayley_re_0 : cayley_re 0 == 1.
Proof. vm_compute. reflexivity. Qed.

(** (4 - 9)/(4 + 9) = -5/13 *)
Lemma cayley_re_3 : cayley_re 3 == -(5#13).
Proof. vm_compute. reflexivity. Qed.

(** 4*6/(4+36) = 24/40 = 3/5 *)
Lemma cayley_im_6 : cayley_im 6 == 3#5.
Proof. vm_compute. reflexivity. Qed.

(** 4*2/(4+4) = 8/8 = 1 *)
Lemma cayley_im_2 : cayley_im 2 == 1.
Proof. vm_compute. reflexivity. Qed.

(** 4*0/(4+0) = 0 *)
Lemma cayley_im_0 : cayley_im 0 == 0.
Proof. vm_compute. reflexivity. Qed.

(** 4*3/(4+9) = 12/13 *)
Lemma cayley_im_3 : cayley_im 3 == 12#13.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  N=2 BETA AND ALPHA                                                 *)
(* ================================================================== *)

(** Re avg = [(-4/5)*1 + 0*3 + 0*3 + (-4/5)*1] / 8 = (-8/5)/8 = -1/5.
    Im avg = [(3/5)*1 + 1*3 + (-1)*3 + (-3/5)*1] / 8 = 0/8 = 0.
    beta = (-1/5)^2 + 0^2 = 1/25 *)
Lemma beta_N2 : beta_Z3 eigs_N2 == 1#25.
Proof. vm_compute. reflexivity. Qed.

(** alpha = (1 - 1/25)/6 = (24/25)/6 = 24/150 = 4/25 *)
Lemma alpha_N2 : alpha_Z3 eigs_N2 == 4#25.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  N=3 BETA AND ALPHA (step-by-step to manage large Q fractions)      *)
(* ================================================================== *)

(** We compute the weighted sums step by step to control Q denominator size. *)

Lemma re_sum_N3 : weighted_sum cayley_re eigs_N3 == 378#65.
Proof. vm_compute. reflexivity. Qed.

Lemma im_sum_N3 : weighted_sum cayley_im eigs_N3 == -(81#65).
Proof. vm_compute. reflexivity. Qed.

(** Re avg = (378/65)/27 = 14/65.  Im avg = (-81/65)/27 = -3/65. *)
Lemma re_avg_N3 : weighted_avg cayley_re eigs_N3 == 14#65.
Proof. unfold weighted_avg. rewrite re_sum_N3, total_N3. vm_compute. reflexivity. Qed.

Lemma im_avg_N3 : weighted_avg cayley_im eigs_N3 == -(3#65).
Proof. unfold weighted_avg. rewrite im_sum_N3, total_N3. vm_compute. reflexivity. Qed.

(** beta = (14/65)^2 + (3/65)^2 = 196/4225 + 9/4225 = 205/4225 = 41/845 *)
Lemma beta_N3 : beta_Z3 eigs_N3 == 41#845.
Proof. vm_compute. reflexivity. Qed.

(** alpha = (1 - 41/845)/6 = (804/845)/6 = 804/5070 = 134/845 *)
Lemma alpha_N3 : alpha_Z3 eigs_N3 == 134#845.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  CONVERGENCE: ALPHA DECREASING                                      *)
(* ================================================================== *)

(** alpha_N2 = 4/25 = 0.16.  alpha_N3 = 134/845 ≈ 0.1586.
    4/25 > 134/845: cross-multiply 4*845 = 3380 > 134*25 = 3350. Yes.
    Alpha decreases with increasing lattice size. *)

Lemma alpha_decreasing : alpha_Z3 eigs_N2 > alpha_Z3 eigs_N3.
Proof.
  rewrite alpha_N2, alpha_N3. lra.
Qed.

(* ================================================================== *)
(*  UNITARITY CONSTRAINTS                                              *)
(* ================================================================== *)

Lemma unitarity_N2 : beta_Z3 eigs_N2 + 6 * alpha_Z3 eigs_N2 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma unitarity_N3 : beta_Z3 eigs_N3 + 6 * alpha_Z3 eigs_N3 == 1.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(*  ADDITIONAL CONVERGENCE EVIDENCE                                    *)
(* ================================================================== *)

(** Both alphas are positive *)
Lemma alpha_N2_pos : alpha_Z3 eigs_N2 > 0.
Proof. rewrite alpha_N2. lra. Qed.

Lemma alpha_N3_pos : alpha_Z3 eigs_N3 > 0.
Proof. rewrite alpha_N3. lra. Qed.

(** Both alphas are bounded above by 1/6 (maximum when beta=0) *)
Lemma alpha_N2_bound : alpha_Z3 eigs_N2 < 1#6.
Proof. rewrite alpha_N2. lra. Qed.

Lemma alpha_N3_bound : alpha_Z3 eigs_N3 < 1#6.
Proof. rewrite alpha_N3. lra. Qed.

(** Synthesis: the lattice calculation is structurally determined *)
Theorem alpha_bare_lattice_synthesis :
  (* Unitarity holds at both sizes *)
  beta_Z3 eigs_N2 + 6 * alpha_Z3 eigs_N2 == 1 /\
  beta_Z3 eigs_N3 + 6 * alpha_Z3 eigs_N3 == 1 /\
  (* Both alphas are in (0, 1/6) *)
  alpha_Z3 eigs_N2 > 0 /\ alpha_Z3 eigs_N2 < 1#6 /\
  alpha_Z3 eigs_N3 > 0 /\ alpha_Z3 eigs_N3 < 1#6.
Proof.
  split; [exact unitarity_N2|].
  split; [exact unitarity_N3|].
  split; [exact alpha_N2_pos|].
  split; [exact alpha_N2_bound|].
  split; [exact alpha_N3_pos|exact alpha_N3_bound].
Qed.
