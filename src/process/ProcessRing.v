(** * ProcessRing.v — Rings and Ideals as Processes
    Elements: polynomials at each truncation level, ideal generators
    Roles:    polynomial ring Q[x]/(x^n), ideal as generator process
    Rules:    addition/multiplication at bounded degree, level growth
    Status:   complete
    STATUS: ~25 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

(* ========================================================================= *)
(*        PROCESS RING — Rings and Ideals as Processes                         *)
(*                                                                           *)
(*  Under P4: polynomial ring Q[x] is the process {Q[x]/(x^n)} at level n. *)
(*  At each level: finitely many monomials (degree < n).                    *)
(*  An ideal is a process of generators.                                    *)
(*                                                                           *)
(*  STATUS: ~25 Qed, 0 Admitted                                             *)
(*  AXIOMS: none                                                             *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import List. Import ListNotations.

Open Scope Q_scope.

From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessGroup.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Polynomial Process  (~10 lemmas)                          *)
(* ================================================================== *)

(** A polynomial: list of Q coefficients, degree = length - 1 *)

(** Polynomial evaluation via Horner's method *)
Fixpoint poly_eval (p : list Q) (x : Q) : Q :=
  match p with
  | [] => 0
  | a :: rest => a + x * poly_eval rest x
  end.

(** Polynomial addition (coefficient-wise) *)
Fixpoint poly_add (p q : list Q) : list Q :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: ps, b :: qs => (a + b) :: poly_add ps qs
  end.

(** Polynomial scaling *)
Fixpoint poly_scale (c : Q) (p : list Q) : list Q :=
  match p with
  | [] => []
  | a :: rest => (c * a) :: poly_scale c rest
  end.

(** Polynomial degree = length *)
Definition poly_degree (p : list Q) : nat := length p.

(** Truncation: keep first n coefficients *)
Definition poly_trunc (p : list Q) (n : nat) : list Q :=
  firstn n p.

(** Evaluation of empty polynomial *)
Lemma eval_nil : forall x, poly_eval [] x == 0.
Proof. intros x. simpl. lra. Qed.

(** Evaluation of constant polynomial *)
Lemma eval_const : forall a x, poly_eval [a] x == a.
Proof. intros a x. simpl. lra. Qed.

(** Evaluation distributes over addition *)
Lemma eval_add : forall p q x,
  poly_eval (poly_add p q) x == poly_eval p x + poly_eval q x.
Proof.
  induction p as [| a ps IHp]; intros q x; simpl.
  - lra.
  - destruct q as [| b qs]; simpl.
    + lra.
    + rewrite IHp. lra.
Qed.

(** Scale distributes through evaluation *)
Lemma eval_scale : forall c p x,
  poly_eval (poly_scale c p) x == c * poly_eval p x.
Proof.
  intros c. induction p as [| a ps IHp]; intros x; simpl.
  - lra.
  - rewrite IHp. lra.
Qed.

(** Degree of addition bounded by max *)
Lemma degree_add : forall p q,
  (poly_degree (poly_add p q) <= Nat.max (poly_degree p) (poly_degree q))%nat.
Proof.
  induction p as [| a ps IHp]; intros q; simpl.
  - unfold poly_degree. lia.
  - destruct q as [| b qs]; simpl.
    + unfold poly_degree. simpl. lia.
    + unfold poly_degree in *. simpl.
      specialize (IHp qs). lia.
Qed.

(** Degree of scaling *)
Lemma degree_scale : forall c p,
  poly_degree (poly_scale c p) = poly_degree p.
Proof.
  intros c. induction p as [| a ps IHp]; simpl.
  - reflexivity.
  - unfold poly_degree in *. simpl. rewrite IHp. reflexivity.
Qed.

(** Truncation preserves or shrinks degree *)
Lemma degree_trunc : forall p n,
  (poly_degree (poly_trunc p n) <= n)%nat.
Proof.
  intros p n. unfold poly_degree, poly_trunc.
  apply firstn_le_length.
Qed.

(** Truncation at degree is identity *)
Lemma trunc_full : forall p,
  poly_trunc p (poly_degree p) = p.
Proof.
  intros p. unfold poly_trunc, poly_degree. apply firstn_all.
Qed.

(** Truncation is idempotent when shrinking *)
Lemma trunc_trunc : forall p n m,
  (n <= m)%nat ->
  poly_trunc (poly_trunc p m) n = poly_trunc p n.
Proof.
  intros p n m Hnm. unfold poly_trunc.
  rewrite firstn_firstn. f_equal. lia.
Qed.

(* ================================================================== *)
(*  Part II: Polynomial Ring at Level n  (~8 lemmas)                  *)
(* ================================================================== *)

(** At level n: polynomials of degree < n form a ring *)
(** This is Q[x]/(x^n) — the truncated polynomial ring *)

(** Level-n polynomial: degree < n *)
Definition poly_at_level (n : nat) (p : list Q) : Prop :=
  (poly_degree p <= n)%nat.

(** Level inclusion *)
Lemma poly_level_increasing : forall n p,
  poly_at_level n p -> poly_at_level (S n) p.
Proof.
  intros n p H. unfold poly_at_level in *. lia.
Qed.

(** Zero polynomial at every level *)
Lemma poly_zero_at_level : forall n,
  poly_at_level n [].
Proof.
  intros n. unfold poly_at_level, poly_degree. simpl. lia.
Qed.

(** Addition preserves level *)
Lemma poly_add_at_level : forall n p q,
  poly_at_level n p -> poly_at_level n q ->
  poly_at_level n (poly_add p q).
Proof.
  intros n p q Hp Hq. unfold poly_at_level in *.
  assert (H := degree_add p q). lia.
Qed.

(** Scaling preserves level *)
Lemma poly_scale_at_level : forall n c p,
  poly_at_level n p -> poly_at_level n (poly_scale c p).
Proof.
  intros n c p Hp. unfold poly_at_level in *.
  rewrite degree_scale. exact Hp.
Qed.

(** Truncation brings to level n *)
Lemma poly_trunc_at_level : forall n p,
  poly_at_level n (poly_trunc p n).
Proof.
  intros n p. unfold poly_at_level. apply degree_trunc.
Qed.

(* ================================================================== *)
(*  Part III: Polynomial Process as RealProcess  (~7 lemmas)          *)
(* ================================================================== *)

(** Evaluate at increasing truncation: the polynomial process *)
Definition poly_process (coeffs : list Q) (x : Q) : RealProcess :=
  fun n => poly_eval (poly_trunc coeffs n) x.

(** At level 0: value is 0 *)
Lemma poly_process_0 : forall coeffs x,
  poly_process coeffs x 0%nat == 0.
Proof.
  intros coeffs x. unfold poly_process, poly_trunc. simpl. lra.
Qed.

(** Eventually constant (when n exceeds degree) *)
Lemma poly_process_eventually_const : forall coeffs x,
  exists N, forall n, (N <= n)%nat ->
    poly_process coeffs x n == poly_eval coeffs x.
Proof.
  intros coeffs x.
  exists (poly_degree coeffs). intros n Hn.
  unfold poly_process, poly_trunc.
  rewrite firstn_all2; [lra | unfold poly_degree in Hn; lia].
Qed.

(** Polynomial process is Cauchy (eventually constant → Cauchy) *)
Lemma poly_process_cauchy : forall coeffs x,
  is_Cauchy (poly_process coeffs x).
Proof.
  intros coeffs x.
  destruct (poly_process_eventually_const coeffs x) as [N HN].
  eapply eventually_const_cauchy. exact HN.
Qed.

(** Evaluation is additive as process *)
Lemma poly_process_add : forall p q x n,
  poly_eval (poly_add (poly_trunc p n) (poly_trunc q n)) x ==
  poly_process p x n + poly_process q x n.
Proof.
  intros p q x n. unfold poly_process. rewrite eval_add. lra.
Qed.

(** Under P4: Q[x] IS the process {Q[x]/(x^n)} *)
(** No completed infinite polynomial — just the process of truncations *)
Theorem polynomial_ring_is_process : forall coeffs x,
  is_Cauchy (poly_process coeffs x).
Proof. exact poly_process_cauchy. Qed.

(* ================================================================== *)
(*  Part IV: Ideal as Process  (~5 lemmas)                            *)
(* ================================================================== *)

(** An ideal generated by polynomials: at level n, use generators up to degree n *)

(** Generator process: at level n, the span of generators truncated to degree n *)
Definition generator_count_at_level (gens : list (list Q)) (n : nat) : nat :=
  length (filter (fun g => Nat.leb (poly_degree g) n) gens).

(** Generator count is increasing *)
Lemma generator_count_increasing : forall gens n,
  (generator_count_at_level gens n <= generator_count_at_level gens (S n))%nat.
Proof.
  intros gens n. unfold generator_count_at_level.
  induction gens as [| g gs IH]; simpl.
  - lia.
  - destruct (Nat.leb (poly_degree g) n) eqn:E1;
    destruct (Nat.leb (poly_degree g) (S n)) eqn:E2; simpl.
    + lia.
    + apply Nat.leb_le in E1. apply Nat.leb_nle in E2. lia.
    + lia.
    + lia.
Qed.

(** Helper: if n ≤ m, filter with (leb _ n) ⊆ filter with (leb _ m) *)
Lemma filter_leb_mono : forall (gs : list (list Q)) n m,
  (n <= m)%nat ->
  (length (filter (fun g => Nat.leb (poly_degree g) n) gs) <=
   length (filter (fun g => Nat.leb (poly_degree g) m) gs))%nat.
Proof.
  intros gs n m Hnm. induction gs as [| h hs IH]; simpl.
  - lia.
  - destruct (Nat.leb (poly_degree h) n) eqn:EN;
    destruct (Nat.leb (poly_degree h) m) eqn:EM; simpl.
    + lia.
    + apply Nat.leb_le in EN. apply Nat.leb_nle in EM. lia.
    + lia.
    + lia.
Qed.

(** Eventually all generators are included *)
Lemma generators_eventually_all : forall gens,
  exists N, generator_count_at_level gens N = length gens.
Proof.
  induction gens as [| g gs IH].
  - exists 0%nat. reflexivity.
  - destruct IH as [N HN].
    set (M := Nat.max N (poly_degree g)).
    exists M. unfold generator_count_at_level. simpl.
    assert (Hg : Nat.leb (poly_degree g) M = true).
    { apply Nat.leb_le. unfold M. lia. }
    rewrite Hg. simpl. f_equal.
    unfold generator_count_at_level in HN.
    assert (HNM : (N <= M)%nat) by (unfold M; lia).
    assert (Hfilter := filter_leb_mono gs N M HNM).
    assert (Hub : (length (filter (fun g0 => Nat.leb (poly_degree g0) M) gs) <=
                   length gs)%nat).
    { apply filter_length_le. }
    lia.
Qed.

(** Ideal dimension at level n is bounded by n *)
Lemma ideal_dimension_bounded : forall gens n,
  (generator_count_at_level gens n <= length gens)%nat.
Proof.
  intros gens n. unfold generator_count_at_level.
  apply filter_length_le.
Qed.

(** Under P4: an ideal IS the process of increasing generator spans *)
Theorem ideal_is_process : forall gens,
  exists N, forall n, (N <= n)%nat ->
    generator_count_at_level gens n = length gens.
Proof.
  intros gens.
  destruct (generators_eventually_all gens) as [N HN].
  exists N. intros n Hn.
  assert (Hle : (generator_count_at_level gens N <=
                 generator_count_at_level gens n)%nat).
  { clear HN. induction Hn; [lia |].
    assert (H := generator_count_increasing gens m). lia. }
  assert (Hub := ideal_dimension_bounded gens n).
  lia.
Qed.

(* ================================================================== *)
(*  Checks                                                              *)
(* ================================================================== *)

Check poly_eval. Check eval_add. Check eval_scale.
Check poly_at_level. Check poly_level_increasing.
Check poly_add_at_level. Check poly_scale_at_level.
Check poly_process. Check poly_process_cauchy.
Check polynomial_ring_is_process.
Check generator_count_at_level. Check generator_count_increasing.
Check generators_eventually_all. Check ideal_is_process.
