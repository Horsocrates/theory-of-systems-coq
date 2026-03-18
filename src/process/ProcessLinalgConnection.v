(* ProcessLinalgConnection.v — Linear algebra connection *)
From Stdlib Require Import QArith QArith_base Lia.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessNonAbelianERR.
From ToS Require Import process.ProcessSU3Matrix.
From ToS Require Import process.ProcessSpectralTheoryQ.
Open Scope Q_scope.

(** linalg/ provides GENERAL Q-vector space axioms *)
(** process/ provides SPECIFIC Q-matrix operations (2x2, 3x3) *)

Theorem trace_id_3_imported : mat_trace_3 mat_id_3 == 3.
Proof. exact trace_id_3. Qed.

Theorem det_id_3_imported : mat_det_3 mat_id_3 == 1.
Proof. exact det_id_3. Qed.

Theorem char_poly_identity :
  char_poly_3x3 1 0 0 0 1 0 0 0 1 1 == 0.
Proof. exact identity_eigenvalue. Qed.

(** Spectral theorem over Q: eigenvalues as roots of Q-polynomial *)
(** For diagonal matrix: eigenvalues ARE the diagonal entries *)
Theorem diag_spectrum : forall a b c,
  char_poly_3x3 a 0 0 0 b 0 0 0 c a == 0 /\
  char_poly_3x3 a 0 0 0 b 0 0 0 c b == 0 /\
  char_poly_3x3 a 0 0 0 b 0 0 0 c c == 0.
Proof.
  intros a b c. split; [|split].
  - exact (diag_eigenvalue_1 a b c).
  - exact (diag_eigenvalue_2 a b c).
  - exact (diag_eigenvalue_3 a b c).
Qed.

Theorem linalg_connected :
  mat_trace_3 mat_id_3 == 3 /\
  mat_det_3 mat_id_3 == 1.
Proof. split; [exact trace_id_3 | exact det_id_3]. Qed.

Definition linalg_count := 6%nat.
