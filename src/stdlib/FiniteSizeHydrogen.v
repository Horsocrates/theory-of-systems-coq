(** * FiniteSizeHydrogen.v — Finite-size hydrogen-like Hamiltonian
    Elements: H_hydrogen matrix entries, traces, Newton identities
    Roles:    tridiagonal + diagonal potential -1/(n+1) models truncated hydrogen
    Rules:    trace relations constrain eigenvalues; Newton identities
    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs List Bool Lia Lra Lqa.
Import ListNotations.
Open Scope Q_scope.

(* --- Matrix entry function --- *)
(* H_hydrogen K i j: tridiagonal with diagonal = -1/(n+1), off-diagonal = 1 *)
Definition H_hydrogen (K : nat) (i j : nat) : Q :=
  match Nat.eqb i j with
  | true  => -(1 # (Pos.of_nat (S i)))  (* diagonal: -1/(i+1) *)
  | false =>
    match (Nat.eqb i (S j), Nat.eqb j (S i)) with
    | (true, _) => 1                     (* sub-diagonal *)
    | (_, true) => 1                     (* super-diagonal *)
    | _ => 0
    end
  end.

(* 1: diagonal entries *)
Lemma H_diag_0 : H_hydrogen 3 O O == -(1#1).
Proof. vm_compute. reflexivity. Qed.

(* 2 *)
Lemma H_diag_1 : H_hydrogen 3 1%nat 1%nat == -(1#2).
Proof. vm_compute. reflexivity. Qed.

(* 3 *)
Lemma H_diag_2 : H_hydrogen 3 2%nat 2%nat == -(1#3).
Proof. vm_compute. reflexivity. Qed.

(* 4: off-diagonal entries *)
Lemma H_offdiag_01 : H_hydrogen 3 O 1%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* 5 *)
Lemma H_offdiag_12 : H_hydrogen 3 1%nat 2%nat == 1.
Proof. vm_compute. reflexivity. Qed.

(* 6: zero entry *)
Lemma H_zero_02 : H_hydrogen 3 O 2%nat == 0.
Proof. vm_compute. reflexivity. Qed.

(* --- Trace for K=3 --- *)
Definition trace3 : Q :=
  H_hydrogen 3 O O + H_hydrogen 3 1%nat 1%nat + H_hydrogen 3 2%nat 2%nat.

(* 7 *)
Lemma trace3_value : trace3 == -(11#6).
Proof. unfold trace3. vm_compute. reflexivity. Qed.

(* --- tr(H^2) for K=3 --- *)
(* (H^2)_{ii} = sum_k H_{ik} * H_{ki} *)
Definition H2_diag (i : nat) : Q :=
  H_hydrogen 3 i O * H_hydrogen 3 O i +
  H_hydrogen 3 i 1%nat * H_hydrogen 3 1%nat i +
  H_hydrogen 3 i 2%nat * H_hydrogen 3 2%nat i.

Definition trace3_sq : Q := H2_diag O + H2_diag 1%nat + H2_diag 2%nat.

(* 8 *)
Lemma H2_diag_0_value : H2_diag O == 2.
Proof. unfold H2_diag. vm_compute. reflexivity. Qed.

(* 9 *)
Lemma H2_diag_1_value : H2_diag 1%nat == 9#4.
Proof. unfold H2_diag. vm_compute. reflexivity. Qed.

(* 10 *)
Lemma H2_diag_2_value : H2_diag 2%nat == 10#9.
Proof. unfold H2_diag. vm_compute. reflexivity. Qed.

(* 11 *)
Lemma trace3_sq_value : trace3_sq == 193#36.
Proof. unfold trace3_sq. vm_compute. reflexivity. Qed.

(* --- Newton identities ---
   p1 = e1, p2 = e1*p1 - 2*e2
   where p_k = tr(H^k), e_k = elementary symmetric polynomials of eigenvalues.
   For 3x3: eigenvalues l1,l2,l3
     e1 = l1+l2+l3 = tr(H)
     p2 = tr(H^2)
     e2 = (e1^2 - p2)/2
*)

(* 12 *)
Lemma newton_e1 : trace3 == -(11#6).
Proof. unfold trace3. vm_compute. reflexivity. Qed.

Definition e1 : Q := trace3.
Definition e2 : Q := (e1 * e1 - trace3_sq) / 2.

(* 13 *)
Lemma e2_value : e2 == -(1#1).
Proof. unfold e2, e1, trace3, trace3_sq. vm_compute. reflexivity. Qed.

(* --- Ratio discussion: tr(H^2)/tr(H)^2 measures eigenvalue spread --- *)
Definition trace_ratio : Q := trace3_sq / (trace3 * trace3).

(* 14 *)
Lemma trace_ratio_value : trace_ratio == 193 # 121.
Proof. unfold trace_ratio, trace3_sq, trace3. vm_compute. reflexivity. Qed.

(* 15: trace is negative — all eigenvalues have negative sum *)
Lemma trace_negative : trace3 < 0.
Proof.
  assert (Hv : trace3 == -(11#6)) by (unfold trace3; vm_compute; reflexivity).
  rewrite Hv. lra.
Qed.
