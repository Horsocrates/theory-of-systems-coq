(** * LieAlgebraSO3.v — the Lie algebra so(3) ≅ su(2) over Q
    Elements: rational vectors (x,y,z) ∈ Q³ — the actual algebra elements (finite data)
    Roles:    the bracket as the infinitesimal symmetry rule; e1,e2,e3 as role-axes
    Rules:    [eᵢ,eⱼ] = εᵢⱼₖ eₖ (structure constants); antisymmetry; Jacobi identity
    STATUS:   14 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Closes the Part XII gap "no Lie algebras": a COMPLETE Lie algebra over Q,
    realized as (Q³, cross product). This is simultaneously so(3) and su(2)
    (the two are isomorphic as real Lie algebras; the cross-product model is the
    common rational realization). Everything is finite rational data; the bracket
    is the infinitesimal generator of rotations. Pure ring arithmetic over Q.

    The three basis brackets ARE the structure constants of so(3):
        [e1,e2]=e3,  [e2,e3]=e1,  [e3,e1]=e2     (εᵢⱼₖ cyclic, =+1)
    and the Lie-algebra axioms hold: antisymmetry, bilinearity, Jacobi.

    HONEST SCOPE: this is the Lie ALGEBRA (infinitesimal rule) over Q, complete.
    The Lie GROUP it generates via the exponential map exp: 𝔤 → G is a continuum
    role-limit; the rational substitute (Cayley map) is a separate file (G2).
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================== Q³ as a vector space ===================== *)
Record V3 : Set := mkV3 { vx : Q ; vy : Q ; vz : Q }.

Definition Veq (a b : V3) : Prop :=
  vx a == vx b /\ vy a == vy b /\ vz a == vz b.

Definition Vadd  (a b : V3) : V3 := mkV3 (vx a + vx b) (vy a + vy b) (vz a + vz b).
Definition Vscale (k : Q) (a : V3) : V3 := mkV3 (k * vx a) (k * vy a) (k * vz a).
Definition Vneg  (a : V3) : V3 := mkV3 (- vx a) (- vy a) (- vz a).
Definition Vzero : V3 := mkV3 0 0 0.

(* ===================== the Lie bracket = cross product ===================== *)
Definition bracket (a b : V3) : V3 :=
  mkV3 (vy a * vz b - vz a * vy b)
       (vz a * vx b - vx a * vz b)
       (vx a * vy b - vy a * vx b).

(* the three generators (rotation axes) *)
Definition e1 : V3 := mkV3 1 0 0.
Definition e2 : V3 := mkV3 0 1 0.
Definition e3 : V3 := mkV3 0 0 1.

(* ===================== Veq is an equivalence ===================== *)
Lemma Veq_refl : forall a, Veq a a.
Proof. intro a. unfold Veq. repeat split; reflexivity. Qed.

Lemma Veq_sym : forall a b, Veq a b -> Veq b a.
Proof. intros a b [Hx [Hy Hz]]. unfold Veq. repeat split; symmetry; assumption. Qed.

Lemma Veq_trans : forall a b c, Veq a b -> Veq b c -> Veq a c.
Proof.
  intros a b c [Hx [Hy Hz]] [Hx' [Hy' Hz']]. unfold Veq.
  repeat split; eapply Qeq_trans; eassumption.
Qed.

(* ===================== structure constants: [eᵢ,eⱼ] = εᵢⱼₖ eₖ ============ *)
Theorem bracket_e1_e2 : Veq (bracket e1 e2) e3.
Proof. unfold Veq, bracket, e1, e2, e3; simpl; repeat split; ring. Qed.

Theorem bracket_e2_e3 : Veq (bracket e2 e3) e1.
Proof. unfold Veq, bracket, e1, e2, e3; simpl; repeat split; ring. Qed.

Theorem bracket_e3_e1 : Veq (bracket e3 e1) e2.
Proof. unfold Veq, bracket, e1, e2, e3; simpl; repeat split; ring. Qed.

(* ===================== Lie-algebra axioms ===================== *)

(* alternating: [a,a] = 0 *)
Theorem bracket_self_zero : forall a, Veq (bracket a a) Vzero.
Proof. intro a. unfold Veq, bracket, Vzero; simpl; repeat split; ring. Qed.

(* antisymmetry: [a,b] = -[b,a] *)
Theorem bracket_antisym : forall a b, Veq (bracket a b) (Vneg (bracket b a)).
Proof. intros a b. unfold Veq, bracket, Vneg; simpl; repeat split; ring. Qed.

(* bilinearity (left): additive and homogeneous in the first slot *)
Theorem bracket_add_l : forall a b c,
  Veq (bracket (Vadd a b) c) (Vadd (bracket a c) (bracket b c)).
Proof. intros a b c. unfold Veq, bracket, Vadd; simpl; repeat split; ring. Qed.

Theorem bracket_scale_l : forall k a b,
  Veq (bracket (Vscale k a) b) (Vscale k (bracket a b)).
Proof. intros k a b. unfold Veq, bracket, Vscale; simpl; repeat split; ring. Qed.

(* bilinearity (right): follows from left + antisymmetry, but proved directly *)
Theorem bracket_add_r : forall a b c,
  Veq (bracket a (Vadd b c)) (Vadd (bracket a b) (bracket a c)).
Proof. intros a b c. unfold Veq, bracket, Vadd; simpl; repeat split; ring. Qed.

Theorem bracket_scale_r : forall k a b,
  Veq (bracket a (Vscale k b)) (Vscale k (bracket a b)).
Proof. intros k a b. unfold Veq, bracket, Vscale; simpl; repeat split; ring. Qed.

(* ★ THE JACOBI IDENTITY: [a,[b,c]] + [b,[c,a]] + [c,[a,b]] = 0 *)
Theorem jacobi : forall a b c,
  Veq (Vadd (bracket a (bracket b c))
            (Vadd (bracket b (bracket c a)) (bracket c (bracket a b))))
      Vzero.
Proof. intros a b c. unfold Veq, bracket, Vadd, Vzero; simpl; repeat split; ring. Qed.

(* ===================== a concrete non-abelian witness ===================== *)
(* the algebra is genuinely non-abelian: [e1,e2] = e3 ≠ 0 = [e2,e1]+[e1,e2]? no —
   non-abelian means [e1,e2] ≠ [e2,e1]; concretely e3 ≠ -e3 since 1 ≠ -1 *)
Theorem so3_nonabelian : ~ Veq (bracket e1 e2) (bracket e2 e1).
Proof.
  unfold Veq, bracket, e1, e2; simpl. intros [_ [_ H]].
  (* H : 1*1 - 0*0 == 0*0 - 1*1, i.e. 1 == -1 *)
  lra.
Qed.

(* ===================== so(3) ≅ su(2) note (structure-constant level) ===== *)
(* su(2) has the same structure constants εᵢⱼₖ (Pauli basis Tₖ = -i σₖ/2 give
   [Tᵢ,Tⱼ] = εᵢⱼₖ Tₖ); the cross-product model above is their common rational
   realization. The basis brackets bracket_e1_e2 / e2_e3 / e3_e1 ARE that table. *)
Definition structure_constant_123 : Veq (bracket e1 e2) e3 := bracket_e1_e2.
