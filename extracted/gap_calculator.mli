
type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val of_nat : nat -> z

  val abs : z -> z
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val inject_Z : z -> q

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qabs : q -> q

val qpow : q -> nat -> q

val fact : nat -> nat

val fact_Q : nat -> q

val fact_prod : nat -> nat -> q

val bessel_term : nat -> nat -> q -> q

val bessel_partial : nat -> q -> nat -> q

val transfer_eigenvalue : nat -> q -> nat -> q

type diagMat = { dm_size : nat; dm_entry : (nat -> q) }

val transfer_mat : nat -> q -> nat -> diagMat

val matrix_mass_gap : nat -> q -> nat -> q

val spectral_gap : nat -> q -> nat -> q

val compute_gap : q -> nat -> q

val error_bound : nat -> q

type gapCertificate = { cert_beta : q; cert_M : nat; cert_value : q;
                        cert_error : q }

val try_certify : q -> nat -> gapCertificate option

val cert_from_pmg : gapCertificate

val gap_calculator : z -> positive -> nat -> (q, q) prod
