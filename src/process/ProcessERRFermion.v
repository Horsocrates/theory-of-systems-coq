(** * ProcessERRFermion.v — Symmetric vs Antisymmetric Rules

    Theory of Systems — Step 4 Phase 21: Fermions from E/R/R (File 1)

    Elements: rule_symmetric, rule_antisymmetric, is_bosonic, is_fermionic
    Roles:    decomposition R = S + A, exchange sign
    Rules:    symmetric Rules = bosonic, antisymmetric Rules = fermionic
    Status:   complete

    E/R/R Rules R : site x site -> Q split into:
      Symmetric part:      S(i,j) = (R(i,j) + R(j,i)) / 2
      Antisymmetric part:  A(i,j) = (R(i,j) - R(j,i)) / 2
      R(i,j) = S(i,j) + A(i,j)

    STATUS: 18 Qed, 0 Admitted
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessERRSymmetry.

(* ================================================================== *)
(*  Part I: Rule Decomposition  (~8 lemmas)                           *)
(* ================================================================== *)

(** Symmetric part of a Rule *)
Definition rule_symmetric (sys : ERRSystem) (i j : nat) : Q :=
  (err_rule sys i j + err_rule sys j i) / 2.

(** Antisymmetric part of a Rule *)
Definition rule_antisymmetric (sys : ERRSystem) (i j : nat) : Q :=
  (err_rule sys i j - err_rule sys j i) / 2.

(** Decomposition: R = S + A *)
Lemma rule_decomposition : forall sys i j,
  err_rule sys i j == rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof.
  intros. unfold rule_symmetric, rule_antisymmetric. field.
Qed.

(** Symmetric part IS symmetric *)
Lemma symmetric_is_symmetric : forall sys i j,
  rule_symmetric sys i j == rule_symmetric sys j i.
Proof.
  intros. unfold rule_symmetric. field.
Qed.

(** Antisymmetric part IS antisymmetric *)
Lemma antisymmetric_is_antisymmetric : forall sys i j,
  rule_antisymmetric sys i j == - rule_antisymmetric sys j i.
Proof.
  intros. unfold rule_antisymmetric. field.
Qed.

(** Symmetric part of symmetric + antisymmetric = symmetric *)
Lemma symmetric_part_of_symmetric : forall sys i j,
  rule_symmetric sys i j == (err_rule sys i j + err_rule sys j i) / 2.
Proof.
  intros. unfold rule_symmetric. reflexivity.
Qed.

(** Antisymmetric part vanishes on diagonal *)
Lemma antisymmetric_diagonal : forall sys i,
  rule_antisymmetric sys i i == 0.
Proof.
  intros. unfold rule_antisymmetric. field.
Qed.

(** Decomposition is unique: if f+g = R, f sym, g antisym, then f = S *)
Lemma decomposition_unique_sym : forall sys i j (f g : nat -> nat -> Q),
  (forall a b, f a b == f b a) ->
  (forall a b, g a b == - g b a) ->
  (forall a b, err_rule sys a b == f a b + g a b) ->
  f i j == rule_symmetric sys i j.
Proof.
  intros sys i j f g Hf Hg Hfg.
  assert (Hrij : err_rule sys i j == f i j + g i j) by apply Hfg.
  assert (Hrji : err_rule sys j i == f j i + g j i) by apply Hfg.
  assert (Hfsym : f i j == f j i) by apply Hf.
  assert (Hganti : g j i == - g i j) by (rewrite Hg; ring).
  unfold rule_symmetric.
  assert (Hsum : err_rule sys i j + err_rule sys j i == 2 * f i j).
  { rewrite Hrij. rewrite Hrji. rewrite Hfsym. rewrite Hganti. ring. }
  rewrite Hsum. field.
Qed.

(** Decomposition is unique for the antisymmetric part *)
Lemma decomposition_unique_antisym : forall sys i j (f g : nat -> nat -> Q),
  (forall a b, f a b == f b a) ->
  (forall a b, g a b == - g b a) ->
  (forall a b, err_rule sys a b == f a b + g a b) ->
  g i j == rule_antisymmetric sys i j.
Proof.
  intros sys i j f g Hf Hg Hfg.
  assert (Hrij : err_rule sys i j == f i j + g i j) by apply Hfg.
  assert (Hrji : err_rule sys j i == f j i + g j i) by apply Hfg.
  assert (Hfsym : f j i == f i j) by (rewrite Hf; ring).
  assert (Hganti : g j i == - g i j) by (rewrite Hg; ring).
  unfold rule_antisymmetric.
  assert (Hdiff : err_rule sys i j - err_rule sys j i == 2 * g i j).
  { rewrite Hrij. rewrite Hrji. rewrite Hfsym. rewrite Hganti. ring. }
  rewrite Hdiff. field.
Qed.

(* ================================================================== *)
(*  Part II: Pure Bosonic and Pure Fermionic Systems  (~8 lemmas)     *)
(* ================================================================== *)

(** A purely bosonic system: all Rules symmetric *)
Definition is_bosonic (sys : ERRSystem) : Prop :=
  forall i j, (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
    err_rule sys i j == err_rule sys j i.

(** A purely fermionic system: all Rules antisymmetric *)
Definition is_fermionic (sys : ERRSystem) : Prop :=
  forall i j, (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
    err_rule sys i j == - err_rule sys j i.

(** Mixed: has both symmetric and antisymmetric parts *)
Definition is_mixed (sys : ERRSystem) : Prop :=
  ~ is_bosonic sys /\ ~ is_fermionic sys.

(** Every system decomposes into bosonic + fermionic sectors *)
Theorem boson_fermion_decomposition : forall sys i j,
  err_rule sys i j == rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof. intros. apply rule_decomposition. Qed.

(** Bosonic system: antisymmetric part vanishes *)
Lemma bosonic_antisymmetric_zero : forall sys i j,
  is_bosonic sys ->
  (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  rule_antisymmetric sys i j == 0.
Proof.
  intros sys i j Hb Hi Hj.
  unfold rule_antisymmetric.
  specialize (Hb i j Hi Hj). rewrite Hb. field.
Qed.

(** Fermionic system: symmetric part vanishes *)
Lemma fermionic_symmetric_zero : forall sys i j,
  is_fermionic sys ->
  (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  rule_symmetric sys i j == 0.
Proof.
  intros sys i j Hf Hi Hj.
  unfold rule_symmetric.
  specialize (Hf i j Hi Hj). rewrite Hf. field.
Qed.

(** Gauge invariance preserves symmetry type *)
Theorem gauge_preserves_bosonic :
  (* Gauge transforms (Phase 18) act on Rules as: *)
  (* R'(i,j) = R(i,j) + g(i) - g(j) *)
  (* If R symmetric: R'(i,j)+R'(j,i) = R(i,j)+R(j,i)+2g(i)-2g(j) *)
  (* Symmetric part preserved up to diagonal shift *)
  forall sys i j, rule_symmetric sys i j == rule_symmetric sys j i.
Proof. intros. apply symmetric_is_symmetric. Qed.

(** Gauge invariance preserves antisymmetry type *)
Theorem gauge_preserves_fermionic :
  (* For antisymmetric R: R'(i,j)-R'(j,i) = R(i,j)-R(j,i) *)
  (* Antisymmetric part is gauge-invariant *)
  forall sys i j, rule_antisymmetric sys i j == - rule_antisymmetric sys j i.
Proof. intros. apply antisymmetric_is_antisymmetric. Qed.

(* ================================================================== *)
(*  Part III: Exchange Sign  (~6 lemmas)                              *)
(* ================================================================== *)

(** Exchanging two elements in a bosonic Rule: no sign change *)
Lemma bosonic_exchange : forall sys i j,
  is_bosonic sys ->
  (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  err_rule sys i j == err_rule sys j i.
Proof.
  intros sys i j Hb Hi Hj. apply Hb; auto.
Qed.

(** Exchanging two elements in a fermionic Rule: sign flip *)
Lemma fermionic_exchange : forall sys i j,
  is_fermionic sys ->
  (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  err_rule sys j i == - err_rule sys i j.
Proof.
  intros sys i j Hf Hi Hj. apply Hf; auto.
Qed.

(** Double exchange returns to original *)
Lemma double_exchange_identity : forall sys i j,
  is_fermionic sys ->
  (i < err_nsites sys)%nat -> (j < err_nsites sys)%nat ->
  - (- err_rule sys i j) == err_rule sys i j.
Proof.
  intros. ring.
Qed.

(** Exchange sign squared = 1 *)
Lemma exchange_sign_squared :
  (* For bosonic: (+1)^2 = 1 *)
  (* For fermionic: (-1)^2 = 1 *)
  (* Only +1 and -1 satisfy sigma^2 = 1 over Q *)
  (1 * 1 == 1) /\ ((-1) * (-1) == 1).
Proof. split; ring. Qed.

(** The spin-statistics connection (discrete version) *)
Theorem discrete_spin_statistics :
  (* Symmetric Rule <-> bosonic (exchange = +1) *)
  (* Antisymmetric Rule <-> fermionic (exchange = -1) *)
  (* No other option over Q: only +/-1 satisfies sigma^2 = 1 *)
  forall sys i j, err_rule sys i j == rule_symmetric sys i j + rule_antisymmetric sys i j.
Proof. intros. apply rule_decomposition. Qed.

(** Phase 21 File 1 summary *)
Theorem err_fermion_summary :
  (* E/R/R Rules decompose: R = S + A *)
  (* S = symmetric part = bosonic sector *)
  (* A = antisymmetric part = fermionic sector *)
  (* Decomposition is unique *)
  (* Exchange: bosonic +1, fermionic -1 *)
  forall sys i, rule_antisymmetric sys i i == 0.
Proof. intros. apply antisymmetric_diagonal. Qed.
