(** * FundamentalIntegral.v -- Slater-type integrals over Q
    Elements: qfact, qpow, slater_integral, factorial values
    Roles:    Radial integrals for hydrogen-like atoms stay in Q
    Rules:    slater_integral n alpha = n!/alpha^(n+1), all computed exactly
    Status:   complete
    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith_base Lia Lqa.
Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Q-valued factorial and power                               *)
(* ================================================================== *)

Fixpoint qfact (n : nat) : Q :=
  match n with
  | O => 1
  | S k => inject_Z (Z.of_nat (S k)) * qfact k
  end.

Fixpoint qpow (base : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | S k => base * qpow base k
  end.

(** The fundamental Slater integral: int_0^inf r^n e^{-alpha r} dr = n! / alpha^{n+1} *)
Definition slater_integral (n : nat) (alpha : Q) : Q :=
  qfact n / qpow alpha (S n).

(* ================================================================== *)
(*  Part II: Factorial values                                          *)
(* ================================================================== *)

Lemma factorial_values :
  qfact O = 1 /\ qfact (S O) = 1 /\ qfact (S (S O)) = 2 /\
  qfact (S (S (S O))) = 6 /\ qfact (S (S (S (S O)))) = 24.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(*  Part III: Concrete Slater integral evaluations                     *)
(* ================================================================== *)

Lemma si_0_1 : slater_integral O 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma si_1_1 : slater_integral (S O) 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma si_2_1 : slater_integral (S (S O)) 1 == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma si_2_2 : slater_integral (S (S O)) 2 == (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma si_3_half : slater_integral (S (S (S O))) (1#2) == 96.
Proof. vm_compute. reflexivity. Qed.

Lemma si_3_1 : slater_integral (S (S (S O))) 1 == 6.
Proof. vm_compute. reflexivity. Qed.

Lemma si_4_1 : slater_integral (S (S (S (S O)))) 1 == 24.
Proof. vm_compute. reflexivity. Qed.

(** Slater integrals always produce Q values (trivial by definition:
    qfact and qpow both return Q, and Q is closed under division) *)
Lemma slater_vs_gaussian :
  forall n alpha, exists (p : Z) (q : positive),
    slater_integral n alpha == (p # q).
Proof.
  intros n alpha.
  exists (Qnum (slater_integral n alpha)).
  exists (Qden (slater_integral n alpha)).
  unfold Qeq. simpl. lia.
Qed.

(** qpow computes correctly *)
Lemma qpow_1_n : forall n, qpow 1 n == 1.
Proof.
  induction n as [|k IH].
  - vm_compute. reflexivity.
  - simpl. rewrite IH. lra.
Qed.

(** qpow with base 2 *)
Lemma qpow_2_3 : qpow 2 (S (S (S O))) == 8.
Proof. vm_compute. reflexivity. Qed.

(** Slater integral positivity for n=0 *)
Lemma si_0_1_positive : (0 < slater_integral O 1)%Q.
Proof. vm_compute. reflexivity. Qed.

