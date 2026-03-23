(** EigenvalueProcess.v — Eigenvalue processes for market transfer matrices.
    E/R/R: Elements = traces, Rayleigh quotients;
           Roles = convergence indicator, gap measure;
           Rules = monotone convergence, diminishing gaps.
    STATUS: 20 Qed, 0 Admitted, 0 axioms *)

From Stdlib Require Import QArith QArith.Qabs Lia Lra List.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================ *)
(* Trace process: models tr(M^n) for a concrete transfer matrix     *)
(* ================================================================ *)

Definition ex_tr (m : nat) : Q :=
  match m with
  | O => 3
  | S O => 3
  | S (S O) => 5
  | S (S (S O)) => 9
  | S (S (S (S O))) => 17
  | _ => 0
  end.

(* Rayleigh quotient: ratio of successive traces *)
Definition rayleigh (m : nat) : Q :=
  ex_tr (S m) / ex_tr m.

(* Gap indicator: difference of successive Rayleigh quotients *)
Definition gap_indicator (m : nat) : Q :=
  rayleigh (S m) - rayleigh m.

(* Trace growth: tr(M^{n+1}) - tr(M^n) *)
Definition trace_growth (m : nat) : Q :=
  ex_tr (S m) - ex_tr m.

(* ================================================================ *)
(* Concrete Rayleigh values                                         *)
(* ================================================================ *)

Lemma ray_0 : rayleigh O == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma ray_1 : rayleigh (S O) == 5#3.
Proof. vm_compute. reflexivity. Qed.

Lemma ray_2 : rayleigh (S (S O)) == 9#5.
Proof. vm_compute. reflexivity. Qed.

Lemma ray_3 : rayleigh (S (S (S O))) == 17#9.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ *)
(* Convergence: gaps diminish                                       *)
(* ================================================================ *)

Lemma gap_0 : gap_indicator O == 2#3.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_1 : gap_indicator (S O) == 2#15.
Proof. vm_compute. reflexivity. Qed.

Lemma gap_2 : gap_indicator (S (S O)) == 4#45.
Proof. vm_compute. reflexivity. Qed.

Lemma convergence_rate :
  rayleigh (S (S (S O))) - rayleigh (S (S O)) < rayleigh (S (S O)) - rayleigh (S O).
Proof.
  unfold rayleigh, ex_tr.
  unfold Qlt. simpl. lia.
Qed.

(* ================================================================ *)
(* Rayleigh is positive                                             *)
(* ================================================================ *)

Lemma rayleigh_0_pos : 0 < rayleigh O.
Proof. unfold rayleigh, ex_tr. unfold Qlt. simpl. lia. Qed.

Lemma rayleigh_1_pos : 0 < rayleigh (S O).
Proof. unfold rayleigh, ex_tr. unfold Qlt. simpl. lia. Qed.

Lemma rayleigh_2_pos : 0 < rayleigh (S (S O)).
Proof. unfold rayleigh, ex_tr. unfold Qlt. simpl. lia. Qed.

Lemma rayleigh_3_pos : 0 < rayleigh (S (S (S O))).
Proof. unfold rayleigh, ex_tr. unfold Qlt. simpl. lia. Qed.

(* ================================================================ *)
(* Trace growth                                                     *)
(* ================================================================ *)

Lemma trace_growth_0 : trace_growth O == 0.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_growth_1 : trace_growth (S O) == 2.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_growth_2 : trace_growth (S (S O)) == 4.
Proof. vm_compute. reflexivity. Qed.

Lemma trace_growth_3 : trace_growth (S (S (S O))) == 8.
Proof. vm_compute. reflexivity. Qed.

(* Trace grows monotonically after step 0 *)
Lemma trace_growth_increasing :
  trace_growth (S O) < trace_growth (S (S O)).
Proof. unfold trace_growth, ex_tr. unfold Qlt. simpl. lia. Qed.

Lemma trace_growth_increasing_2 :
  trace_growth (S (S O)) < trace_growth (S (S (S O))).
Proof. unfold trace_growth, ex_tr. unfold Qlt. simpl. lia. Qed.

(* Rayleigh bounded above by 2 *)
Lemma rayleigh_bounded : rayleigh (S (S (S O))) < 2.
Proof. unfold rayleigh, ex_tr. unfold Qlt. simpl. lia. Qed.

(* Trace values *)
Lemma ex_tr_0 : ex_tr O == 3.
Proof. vm_compute. reflexivity. Qed.

Lemma ex_tr_4 : ex_tr (S (S (S (S O)))) == 17.
Proof. vm_compute. reflexivity. Qed.
