(** SharkovskiiCovering.v — Covering implies fixed point (concrete verification) *)
(** E/R/R: Elements = PL map values; Roles = interval covering; Rules = fixed point existence *)
From Stdlib Require Import QArith Qabs Lia ZArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(** PL map: f(x) = 1/2+x on [0,1/2], f(x) = 2-2x on [1/2,1] *)
Definition f_pl (x : Q) : Q :=
  if Qle_bool x (1#2) then (1#2) + x else 2 - 2*x.

(** Fixed point: f(2/3) = 2 - 4/3 = 2/3 *)
Lemma fp_verify : f_pl (2#3) == 2#3.
Proof. unfold f_pl. vm_compute. reflexivity. Qed.

(** f^2: compose *)
Definition f2_pl (x : Q) : Q := f_pl (f_pl x).

(** Period-2 point: f^2(1/3) = 1/3 *)
Lemma fp2_verify : f2_pl (1#3) == 1#3.
Proof. unfold f2_pl, f_pl. vm_compute. reflexivity. Qed.

(** f^3 *)
Definition f3_pl (x : Q) : Q := f_pl (f2_pl x).

(** Period-3 point: f^3(0) = 0 *)
Lemma fp3_verify : f3_pl 0 == 0.
Proof. unfold f3_pl, f2_pl, f_pl. vm_compute. reflexivity. Qed.

(** f^4 *)
Definition f4_pl (x : Q) : Q := f_pl (f3_pl x).

(** Period-4 point: f^4(2/9) = 2/9 *)
Lemma fp4_verify : f4_pl (2#9) == 2#9.
Proof. unfold f4_pl, f3_pl, f2_pl, f_pl. vm_compute. reflexivity. Qed.

(** Boundary values *)
Lemma f_pl_0 : f_pl 0 == 1#2.
Proof. unfold f_pl. vm_compute. reflexivity. Qed.

Lemma f_pl_half : f_pl (1#2) == 1.
Proof. unfold f_pl. vm_compute. reflexivity. Qed.

Lemma f_pl_1 : f_pl 1 == 0.
Proof. unfold f_pl. vm_compute. reflexivity. Qed.

(** Image of [0,1] under f is [0,1]: f(0)=1/2, f(1/2)=1, f(1)=0 *)
(** So [0,1] is f-invariant *)
Lemma f_pl_invariant_check :
  f_pl 0 == 1#2 /\ f_pl (1#2) == 1 /\ f_pl 1 == 0.
Proof.
  split; [exact f_pl_0|].
  split; [exact f_pl_half|].
  exact f_pl_1.
Qed.

(** f^2 boundary values *)
Lemma f2_pl_0 : f2_pl 0 == 1.
Proof. unfold f2_pl, f_pl. vm_compute. reflexivity. Qed.

Lemma f2_pl_1 : f2_pl 1 == 1#2.
Proof. unfold f2_pl, f_pl. vm_compute. reflexivity. Qed.

(** f^3 at 1/2: period-3 orbit point *)
Lemma f3_pl_half : f3_pl (1#2) == 1#2.
Proof. unfold f3_pl, f2_pl, f_pl. vm_compute. reflexivity. Qed.

(** Covering principle: f([0,1]) contains [0,1], so fixed point exists *)
(** Concretely verified: f(2/3) = 2/3 *)
Theorem covering_implies_fp :
  f_pl 0 == 1#2 /\ f_pl 1 == 0 /\ f_pl (2#3) == 2#3.
Proof.
  split; [exact f_pl_0|].
  split; [exact f_pl_1|].
  exact fp_verify.
Qed.
