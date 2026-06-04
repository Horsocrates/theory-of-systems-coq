(** * IndependenceQ23.v — √3 ∉ Q[√2]: the degree-4 tower is GENUINE
    Elements: candidate representations a + b√2 of √3 inside Q[√2]
    Roles:    Q[√2] as a proper sub-extension; √3 as a genuinely new generator
    Rules:    a+b√2 squaring to 3 forces 2ab=0 and a²+2b²=3, impossible over Q
    STATUS:   3 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    Closes the KEY independence step behind [E:Q]=4: √3 ∉ Q[√2], so the tower
    Q ⊊ Q[√2] ⊊ Q[√2,√3] is non-degenerate (each step a genuine degree-2
    extension). This is PURELY ALGEBRAIC over Q — no real embedding — using
    only the irrationality of √3 (Sqrt3Irrational.v) and √6 (GeneralSqrt.v):

        if √3 = a + b√2 then squaring gives 2ab·√2 = 3 − a² − 2b² ∈ Q,
        so ab = 0; b=0 ⟹ a²=3 (√3 irr.), a=0 ⟹ (2b)²=6 (√6 irr.).

    Together with GaloisDegreeQ23.v (degree = |Gal| = 4) this makes the
    degree-4 claim genuine, not merely the dimension of a formal module.
*)

From ToS Require Import algebra.GaloisQ23.
From ToS Require Import analysis.Sqrt3Irrational.
From ToS Require Import stdlib.GeneralSqrt.
From Stdlib Require Import QArith Lqa.
Open Scope Q_scope.

(* 6 is not a rational square, in Q-literal form (bridges inject_Z once) *)
Lemma no_sq_6 : forall r : Q, ~ (r * r == 6).
Proof.
  intros r Hr. apply sqrt6_role_limit. exists r.
  rewrite Hr. vm_compute. reflexivity.
Qed.

(* No element a + b√2 of Q[√2] squares to 3 — i.e. √3 ∉ Q[√2]. *)
Theorem sqrt3_not_in_Qsqrt2 :
  ~ exists a b : Q, Eeq (Emul (mkE a b 0 0) (mkE a b 0 0)) (Eofq 3).
Proof.
  intros [a [b H]]. destruct H as [H0 [H1 _]].
  cbn in H0, H1.
  (* H0 : a*a + 2*(b*b) + ... == 3 ;  H1 : a*b + b*a + ... == 0 *)
  assert (Hc0 : a*a + 2*(b*b) == 3) by lra.
  assert (Hc1 : a*b == 0).
  { assert (Ecomm : b*a == a*b) by ring. rewrite Ecomm in H1. lra. }
  destruct (Qmult_integral a b Hc1) as [Ha | Hb].
  - (* a = 0 :  2b² = 3  ⟹  (2b)² = 6, contradicting √6 irrationality *)
    assert (Hb2 : 2*(b*b) == 3). { rewrite Ha in Hc0. lra. }
    apply (no_sq_6 (2*b)).
    assert (E2 : (2*b)*(2*b) == 2*(2*(b*b))) by ring.
    rewrite E2, Hb2. lra.
  - (* b = 0 :  a² = 3, contradicting √3 irrationality *)
    assert (Ha2 : a*a == 3). { rewrite Hb in Hc0. lra. }
    exact (no_rational_sqrt3 a Ha2).
Qed.

(* The tower Q ⊊ Q[√2] ⊊ Q[√2,√3] is genuine (the second step is nontrivial). *)
Corollary tower_nondegenerate :
  ~ exists a b : Q, Eeq (Emul (mkE a b 0 0) (mkE a b 0 0)) (Eofq 3).
Proof. exact sqrt3_not_in_Qsqrt2. Qed.
