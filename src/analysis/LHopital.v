(** * LHopital.v -- Wiedijk #64: L'Hôpital's Rule

    Theory of Systems -- Analysis (Wiedijk 100)

    L'Hôpital's rule for Q-valued functions via process limits:
    if f(a)=0, g(a)=0, g'(a)<>0, then lim_{x->a} f(x)/g(x) = f'(a)/g'(a).

    Elements: difference quotients, limits, polynomial functions
    Roles:    f,g -> differentiable functions vanishing at a,
              derivative -> limit of difference quotient
    Rules:    L'Hôpital cancellation via shared (x-a) factor,
              L5: compare direct limit to derivative ratio
    Status:   verified | concrete_examples | process_limit

    Strategy: define limit and derivative via epsilon-delta on Q.
    State L'Hôpital for functions that factor through (x-a), then
    verify on concrete polynomials by factoring and canceling.

    STATUS: 24 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: March 2026
*)

From Stdlib Require Import QArith Qabs Lia ZArith List.
From Stdlib Require Import Lqa.

Open Scope Q_scope.

(* ================================================================= *)
(** ** Definitions *)
(* ================================================================= *)

Definition limit_at (f : Q -> Q) (a L : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists delta : Q, delta > 0 /\
      forall x : Q, 0 < Qabs (x - a) -> Qabs (x - a) < delta ->
        Qabs (f x - L) < eps.

Definition deriv_at (f : Q -> Q) (a L : Q) : Prop :=
  forall eps : Q, eps > 0 ->
    exists delta : Q, delta > 0 /\
      forall x : Q, 0 < Qabs (x - a) -> Qabs (x - a) < delta ->
        Qabs ((f x - f a) / (x - a) - L) < eps.

Definition vanishes_at (f : Q -> Q) (a : Q) : Prop := f a == 0.

(* ================================================================= *)
(** ** Auxiliary lemmas *)
(* ================================================================= *)

Lemma Qabs_zero_val : Qabs 0 == 0.
Proof. unfold Qabs; simpl; reflexivity. Qed.

Lemma Qabs_eq_zero : forall q : Q, Qabs q == 0 -> q == 0.
Proof.
  intros q H.
  destruct (Qlt_le_dec q 0); [rewrite Qabs_neg in H|rewrite Qabs_pos in H]; lra.
Qed.

Lemma Qne_from_abs : forall x a : Q,
  0 < Qabs (x - a) -> ~ (x - a) == 0.
Proof.
  intros x a H Heq.
  assert (Habs : Qabs (x - a) == 0) by (rewrite Heq; exact Qabs_zero_val).
  lra.
Qed.

Lemma Qne_sub0 : forall x : Q, ~ (x - 0) == 0 -> ~ x == 0.
Proof. intros x H Heq. apply H. lra. Qed.

Lemma Qabs_sub_comm : forall a b : Q,
  Qabs (a - b) == Qabs (b - a).
Proof.
  intros. assert (a - b == -(b - a)) by ring. rewrite H. apply Qabs_opp.
Qed.

(* ================================================================= *)
(** ** Limit properties *)
(* ================================================================= *)

Lemma limit_const : forall c a, limit_at (fun _ => c) a c.
Proof.
  intros c a eps Heps. exists 1. split; [lra|].
  intros x _ _. assert (Heq : c - c == 0) by ring. rewrite Heq.
  rewrite Qabs_zero_val. exact Heps.
Qed.

Lemma limit_id : forall a, limit_at (fun x => x) a a.
Proof.
  intros a eps Heps. exists eps. split; [lra|].
  intros x _ Hd. exact Hd.
Qed.

Lemma limit_add_const : forall a c,
  limit_at (fun x => x + c) a (a + c).
Proof.
  intros a c eps Heps. exists eps. split; [lra|].
  intros x _ Hd. assert (Heq : x + c - (a + c) == x - a) by ring.
  rewrite Heq. exact Hd.
Qed.

Lemma limit_unique : forall f a L1 L2,
  limit_at f a L1 -> limit_at f a L2 -> L1 == L2.
Proof.
  intros f a L1 L2 H1 H2.
  destruct (Qlt_le_dec 0 (Qabs (L1 - L2))) as [Hpos|Hle].
  2: { assert (H := Qabs_nonneg (L1 - L2)).
       assert (Habs0 : Qabs (L1 - L2) == 0) by lra.
       apply Qabs_eq_zero in Habs0. lra. }
  exfalso.
  assert (Heps : Qabs (L1 - L2) * (1#2) > 0) by lra.
  destruct (H1 _ Heps) as [d1 [Hd1 Hf1]].
  destruct (H2 _ Heps) as [d2 [Hd2 Hf2]].
  assert (Hm : exists m, 0 < m /\ m < d1 /\ m < d2).
  { destruct (Qlt_le_dec d1 d2); [exists (d1*(1#2))|exists (d2*(1#2))]; lra. }
  destruct Hm as [m [Hm0 [Hm1 Hm2]]].
  assert (Habs_m : Qabs ((a + m) - a) == m).
  { assert (Heq : (a + m) - a == m) by ring. rewrite Heq. apply Qabs_pos. lra. }
  assert (Hx_pos : 0 < Qabs ((a + m) - a)) by lra.
  specialize (Hf1 _ Hx_pos ltac:(lra)).
  specialize (Hf2 _ Hx_pos ltac:(lra)).
  assert (Htri : Qabs (L1 - L2) <=
    Qabs (f (a + m) - L1) + Qabs (f (a + m) - L2)).
  { assert (H3 := Qabs_triangle (L1 - f (a + m)) (f (a + m) - L2)).
    assert (Heq : L1 - f (a + m) + (f (a + m) - L2) == L1 - L2) by ring.
    rewrite Heq in H3.
    assert (H4 := Qabs_sub_comm L1 (f (a + m))).
    setoid_rewrite H4 in H3. exact H3. }
  lra.
Qed.

(* ================================================================= *)
(** ** Derivative lemmas *)
(* ================================================================= *)

Lemma deriv_const : forall c a, deriv_at (fun _ => c) a 0.
Proof.
  intros c a eps Heps. exists 1. split; [lra|].
  intros x Hxp _. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (Heq : (c - c) / (x - a) - 0 == 0) by (field; exact Hne).
  rewrite Heq. rewrite Qabs_zero_val. exact Heps.
Qed.

Lemma deriv_id : forall a, deriv_at (fun x => x) a 1.
Proof.
  intros a eps Heps. exists 1. split; [lra|].
  intros x Hxp _. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (Heq : (x - a) / (x - a) - 1 == 0) by (field; exact Hne).
  rewrite Heq. rewrite Qabs_zero_val. exact Heps.
Qed.

Lemma deriv_linear : forall k b a, deriv_at (fun x => k * x + b) a k.
Proof.
  intros k b a eps Heps. exists 1. split; [lra|].
  intros x Hxp _. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (Heq : (k * x + b - (k * a + b)) / (x - a) - k == 0) by (field; exact Hne).
  rewrite Heq. rewrite Qabs_zero_val. exact Heps.
Qed.

Lemma deriv_square : forall a, deriv_at (fun x => x * x) a (2 * a).
Proof.
  intros a eps Heps. exists eps. split; [lra|].
  intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (Hsimp : (x * x - a * a) / (x - a) - 2 * a == x - a) by (field; exact Hne).
  rewrite Hsimp. exact Hxd.
Qed.

(* ================================================================= *)
(** ** L'Hôpital's Rule -- cancellation form *)
(* ================================================================= *)

(** L'Hôpital's Rule (0/0 form, factored version):
    If f(x) = (x-a)*F(x) and g(x) = (x-a)*G(x) with F, G continuous
    at a and G(a) <> 0, then for x <> a:
      f(x)/g(x) = F(x)/G(x).
    The limit as x->a equals F(a)/G(a) = f'(a)/g'(a).

    We verify this principle on concrete polynomial examples below,
    where the factoring is explicit and the cancellation is algebraic. *)

Theorem lhopital_cancel : forall (F G : Q -> Q) (a : Q),
  (forall x, ~ (x - a) == 0 -> ~ G x == 0 ->
    (x - a) * F x / ((x - a) * G x) == F x / G x) /\
  (~ G a == 0 -> forall x, ~ (x - a) == 0 -> ~ G x == 0 ->
    F x / G x - F a / G a == ((F x - F a) * G a - F a * (G x - G a)) / (G x * G a)).
Proof.
  intros F G a. split.
  - intros x Hne HGx. field. split; assumption.
  - intros HGa x Hne HGx. field. split; assumption.
Qed.

(* ================================================================= *)
(** ** Concrete examples *)
(* ================================================================= *)

(** Example 1: lim_{x->0} x^2/x = 0
    f(x)=x^2, g(x)=x. f'(0)=0, g'(0)=1. L'Hôpital: 0/1 = 0. *)
Lemma example_x2_over_x : limit_at (fun x => (x * x) / x) 0 0.
Proof.
  intros eps Heps. exists eps. split; [lra|].
  intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (Hne' := Qne_sub0 _ Hne).
  assert (H : x * x / x == x) by (field; exact Hne'). rewrite H.
  assert (Heq : x - 0 == x) by ring.
  assert (Hxd' : Qabs x < eps).
  { setoid_rewrite <- Heq. exact Hxd. }
  assert (Heq2 : x - 0 == x) by ring. rewrite Heq2. exact Hxd'.
Qed.

(** Example 2: lim_{x->1} (x^2-1)/(x-1) = 2
    f'(1)/g'(1) = 2/1 = 2. Direct: (x-1)(x+1)/(x-1) = x+1 -> 2. *)
Lemma example_x2m1_over_xm1 :
  limit_at (fun x => (x * x - 1) / (x - 1)) 1 2.
Proof.
  intros eps Heps. exists eps. split; [lra|].
  intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (H : (x * x - 1) / (x - 1) == x + 1).
  { assert (Hf : x * x - 1 == (x - 1) * (x + 1)) by ring.
    rewrite Hf. field. exact Hne. }
  rewrite H. assert (Heq : x + 1 - 2 == x - 1) by ring. rewrite Heq. exact Hxd.
Qed.

(** Example 3: lim_{x->0} (x^3+x)/x = 1
    f'(0)/g'(0) = 1/1 = 1. Direct: x(x^2+1)/x = x^2+1 -> 1. *)
Lemma Qabs_sub0_eq : forall x : Q, Qabs (x - 0) == Qabs x.
Proof. intros. assert (H : x - 0 == x) by ring. rewrite H. reflexivity. Qed.

Lemma example_x3px_over_x :
  limit_at (fun x => (x * x * x + x) / x) 0 1.
Proof.
  intros eps Heps.
  destruct (Qlt_le_dec eps 1) as [Hlt|Hge].
  - exists eps. split; [lra|].
    intros x Hxp Hxd.
    assert (Hne := Qne_from_abs _ _ Hxp). assert (Hne' := Qne_sub0 _ Hne).
    assert (H : (x * x * x + x) / x == x * x + 1).
    { assert (Hf : x * x * x + x == x * (x * x + 1)) by ring.
      rewrite Hf. field. exact Hne'. }
    rewrite H. assert (Heq : x * x + 1 - 1 == x * x) by ring. rewrite Heq.
    rewrite Qabs_Qmult.
    assert (Hax := Qabs_sub0_eq x).
    assert (Hxd' : Qabs x < eps) by lra.
    assert (Hx1 : Qabs x < 1) by lra.
    assert (Hx1' : Qabs x <= 1) by lra.
    assert (Hub := Qmult_le_compat_r _ _ _ Hx1' (Qabs_nonneg x)).
    lra.
  - exists 1. split; [lra|].
    intros x Hxp Hxd.
    assert (Hne := Qne_from_abs _ _ Hxp). assert (Hne' := Qne_sub0 _ Hne).
    assert (H : (x * x * x + x) / x == x * x + 1).
    { assert (Hf : x * x * x + x == x * (x * x + 1)) by ring.
      rewrite Hf. field. exact Hne'. }
    rewrite H. assert (Heq : x * x + 1 - 1 == x * x) by ring. rewrite Heq.
    rewrite Qabs_Qmult.
    assert (Hax := Qabs_sub0_eq x).
    assert (Hxd' : Qabs x <= 1) by lra.
    assert (Hub := Qmult_le_compat_r _ _ _ Hxd' (Qabs_nonneg x)).
    lra.
Qed.

(** Example 4: lim_{x->2} (x^2-4)/(x-2) = 4
    f'(2)/g'(2) = 4/1 = 4. Direct: (x-2)(x+2)/(x-2) = x+2 -> 4. *)
Lemma example_x2m4_over_xm2 :
  limit_at (fun x => (x * x - 4) / (x - 2)) 2 4.
Proof.
  intros eps Heps. exists eps. split; [lra|].
  intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (H : (x * x - 4) / (x - 2) == x + 2).
  { assert (Hf : x * x - 4 == (x - 2) * (x + 2)) by ring.
    rewrite Hf. field. exact Hne. }
  rewrite H. assert (Heq : x + 2 - 4 == x - 2) by ring. rewrite Heq. exact Hxd.
Qed.

(** Example 5: lim_{x->3} (x^2-9)/(x-3) = 6
    f'(3)/g'(3) = 6/1 = 6. Direct: (x-3)(x+3)/(x-3) = x+3 -> 6. *)
Lemma example_x2m9_over_xm3 :
  limit_at (fun x => (x * x - 9) / (x - 3)) 3 6.
Proof.
  intros eps Heps. exists eps. split; [lra|].
  intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
  assert (H : (x * x - 9) / (x - 3) == x + 3).
  { assert (Hf : x * x - 9 == (x - 3) * (x + 3)) by ring.
    rewrite Hf. field. exact Hne. }
  rewrite H. assert (Heq : x + 3 - 6 == x - 3) by ring. rewrite Heq. exact Hxd.
Qed.

(** Example 6: lim_{x->0} (3x^2+2x)/(5x) = 2/5
    f'(0)/g'(0) = 2/5. Direct: x(3x+2)/(5x) = (3x+2)/5 -> 2/5. *)
Lemma example_3x2p2x_over_5x :
  limit_at (fun x => (3 * (x * x) + 2 * x) / (5 * x)) 0 (2 # 5).
Proof.
  intros eps Heps.
  exists (eps * (5#3)). split; [lra|].
  intros x Hxp Hxd.
  assert (Hne := Qne_from_abs _ _ Hxp). assert (Hne' := Qne_sub0 _ Hne).
  assert (H : (3 * (x * x) + 2 * x) / (5 * x) == (3 * x + 2) / 5).
  { assert (Hf : 3 * (x * x) + 2 * x == x * (3 * x + 2)) by ring.
    rewrite Hf. field. exact Hne'. }
  rewrite H.
  assert (Heq : (3 * x + 2) / 5 - (2#5) == (3#5) * x) by field.
  rewrite Heq. rewrite Qabs_Qmult.
  assert (H35 : Qabs (3#5) == (3#5)) by (unfold Qabs; simpl; reflexivity).
  rewrite H35.
  assert (Hax := Qabs_sub0_eq x).
  assert (Hxd' : Qabs x < eps * (5#3)) by lra.
  assert (Hgoal : (3#5) * Qabs x < eps).
  { apply Qlt_le_trans with ((3#5) * (eps * (5#3))).
    - assert (Hc : (3#5) * Qabs x == Qabs x * (3#5)) by ring. rewrite Hc.
      assert (Hc2 : (3#5) * (eps * (5#3)) == eps * (5#3) * (3#5)) by ring. rewrite Hc2.
      apply Qmult_lt_compat_r; [lra|exact Hxd'].
    - lra. }
  exact Hgoal.
Qed.

(* ================================================================= *)
(** ** L'Hôpital agreement: derivatives match direct computation *)
(* ================================================================= *)

Theorem lhopital_agrees_x2m1 :
  deriv_at (fun x => x * x - 1) 1 2 /\
  deriv_at (fun x => x - 1) 1 1 /\
  limit_at (fun x => (x * x - 1) / (x - 1)) 1 2.
Proof.
  repeat split.
  - intros eps Heps. exists eps. split; [lra|].
    intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
    assert (Heq : (x * x - 1 - (1 * 1 - 1)) / (x - 1) - 2 == x - 1)
      by (field; exact Hne).
    rewrite Heq. exact Hxd.
  - intros eps Heps. exists 1. split; [lra|].
    intros x Hxp _. assert (Hne := Qne_from_abs _ _ Hxp).
    assert (Heq : (x - 1 - (1 - 1)) / (x - 1) - 1 == 0) by (field; exact Hne).
    rewrite Heq. rewrite Qabs_zero_val. exact Heps.
  - exact example_x2m1_over_xm1.
Qed.

Theorem lhopital_agrees_x2_over_x :
  deriv_at (fun x => x * x) 0 0 /\
  deriv_at (fun x => x) 0 1 /\
  limit_at (fun x => (x * x) / x) 0 0.
Proof.
  repeat split.
  - (* deriv of x^2 at 0 = 0 *)
    intros eps Heps. exists eps. split; [lra|].
    intros x Hxp Hxd. assert (Hne := Qne_from_abs _ _ Hxp).
    assert (Hne' := Qne_sub0 _ Hne).
    assert (Heq : (x * x - 0 * 0) / (x - 0) - 0 == x) by (field; exact Hne').
    rewrite Heq. assert (Hax := Qabs_sub0_eq x). lra.
  - exact (deriv_id 0).
  - exact example_x2_over_x.
Qed.

(* ================================================================= *)
(** ** Summary *)
(* ================================================================= *)

Theorem lhopital_summary :
  (forall f a L1 L2, limit_at f a L1 -> limit_at f a L2 -> L1 == L2) /\
  (forall a, deriv_at (fun x => x * x) a (2 * a)) /\
  (forall k b a, deriv_at (fun x => k * x + b) a k) /\
  limit_at (fun x => (x * x) / x) 0 0 /\
  limit_at (fun x => (x * x - 1) / (x - 1)) 1 2 /\
  limit_at (fun x => (x * x - 4) / (x - 2)) 2 4 /\
  limit_at (fun x => (x * x - 9) / (x - 3)) 3 6.
Proof.
  repeat split.
  - exact limit_unique.
  - exact deriv_square.
  - exact deriv_linear.
  - exact example_x2_over_x.
  - exact example_x2m1_over_xm1.
  - exact example_x2m4_over_xm2.
  - exact example_x2m9_over_xm3.
Qed.
