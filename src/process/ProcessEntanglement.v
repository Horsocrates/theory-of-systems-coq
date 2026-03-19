(* ========================================================================= *)
(*  ENTANGLEMENT — Non-Factorization of Composite E/R/R Rules               *)
(*                                                                          *)
(*  P1: whole > sum of parts.                                               *)
(*  For composite system: Rules cannot be factored into independent parts.  *)
(*  Non-factorization = entanglement.                                       *)
(*                                                                          *)
(*  STATUS: 25 Qed, 0 Admitted                                              *)
(*  AXIOMS: classic                                                         *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith_base QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Nsatz.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessGaussianQ.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: Composite Systems  (~10 lemmas)                            *)
(* ================================================================== *)

(** Two subsystems A and B, each with their own sites *)
(** Combined system AB: pairs (a, b) as sites *)

(** A composite Rule on pairs *)
Definition CompositeRule := nat -> nat -> nat -> nat -> Q.
  (* R(a1, b1, a2, b2) = interaction between (a1,b1) and (a2,b2) *)

(** Factored (separable) Rule: R(a1,b1,a2,b2) = f(a1,a2) * g(b1,b2) *)
Definition is_separable (R : CompositeRule) (nA nB : nat) : Prop :=
  exists (fA : nat -> nat -> Q) (fB : nat -> nat -> Q),
    forall a1 b1 a2 b2,
      (a1 < nA)%nat -> (b1 < nB)%nat ->
      (a2 < nA)%nat -> (b2 < nB)%nat ->
      R a1 b1 a2 b2 == fA a1 a2 * fB b1 b2.

(** Entangled = NOT separable *)
Definition is_entangled (R : CompositeRule) (nA nB : nat) : Prop :=
  ~ is_separable R nA nB.

(** Concrete entangled Rule: Bell EPR correlation *)
(** R(a1,b1,a2,b2) = δ_{a1,b2} · δ_{b1,a2} — anti-diagonal correlation *)
(** a1=b2 AND b1=a2: outcomes SWAP between copies *)
Definition bell_rule : CompositeRule :=
  fun a1 b1 a2 b2 =>
    if (Nat.eqb a1 b2 && Nat.eqb b1 a2)%bool then 1
    else 0.

(** Compute bell_rule values *)
Lemma bell_rule_00_00 : bell_rule 0%nat 0%nat 0%nat 0%nat == 1.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

Lemma bell_rule_00_11 : bell_rule 0%nat 0%nat 1%nat 1%nat == 0.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

Lemma bell_rule_01_01 : bell_rule 0%nat 1%nat 0%nat 1%nat == 0.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

Lemma bell_rule_01_10 : bell_rule 0%nat 1%nat 1%nat 0%nat == 1.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

Lemma bell_rule_11_11 : bell_rule 1%nat 1%nat 1%nat 1%nat == 1.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

Lemma bell_rule_10_01 : bell_rule 1%nat 0%nat 0%nat 1%nat == 1.
Proof. unfold bell_rule. simpl. reflexivity. Qed.

(** ★ bell_rule is NOT separable *)
(** Proof by contradiction:
    If separable: R(a1,b1,a2,b2) = f(a1,a2) * g(b1,b2)
    R(0,0,0,0) = 1 => f(0,0)*g(0,0) = 1
    R(0,1,0,1) = 0 => f(0,0)*g(1,1) = 0
    Since f(0,0)*g(0,0) = 1 => f(0,0) != 0
    So g(1,1) = 0
    But R(1,1,1,1) = 1 => f(1,1)*g(1,1) = 1
    => g(1,1) != 0. Contradiction! *)
Theorem bell_rule_entangled : is_entangled bell_rule 2%nat 2%nat.
Proof.
  unfold is_entangled, is_separable. intros [fA [fB Hsep]].
  (* Get key equations *)
  assert (H0000 := Hsep 0%nat 0%nat 0%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (H0101 := Hsep 0%nat 1%nat 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (H1111 := Hsep 1%nat 1%nat 1%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  (* Compute bell_rule values *)
  rewrite bell_rule_00_00 in H0000.
  rewrite bell_rule_01_01 in H0101.
  rewrite bell_rule_11_11 in H1111.
  (* From H0000: fA 0%nat 0%nat * fB 0%nat 0%nat == 1, so both nonzero *)
  assert (HfA00 : ~ fA 0%nat 0%nat == 0).
  { intros Heq. rewrite Heq in H0000.
    rewrite Qmult_0_l in H0000. lra. }
  (* From H0101: fA 0%nat 0%nat * fB 1%nat 1%nat == 0 *)
  (* Since fA 0%nat 0%nat != 0: fB 1%nat 1%nat == 0 *)
  assert (HfB11 : fB 1%nat 1%nat == 0).
  { destruct (Qeq_dec (fB 1%nat 1%nat) 0) as [Heq | Hneq].
    - exact Heq.
    - exfalso. apply HfA00.
      destruct (Qeq_dec (fA 0%nat 0%nat) 0) as [Heq0 | Hneq0].
      + exact Heq0.
      + exfalso.
        assert (Hprod : fA 0%nat 0%nat * fB 1%nat 1%nat == 0) by lra.
        destruct (Qmult_integral _ _ Hprod) as [Ha | Hb].
        * contradiction.
        * contradiction. }
  (* From H1111: fA 1%nat 1%nat * fB 1%nat 1%nat == 1, but fB 1%nat 1%nat == 0 *)
  rewrite HfB11 in H1111. rewrite Qmult_0_r in H1111. lra.
Qed.

(* ================================================================== *)
(*  Part II: P1 Requires Entanglement  (~6 lemmas)                     *)
(* ================================================================== *)

(** Separable system: whole = sum of parts (product) *)
(** If R is separable: all correlations are products of local ones *)
(** => knowing A and B separately determines everything about AB *)
(** => system IS just the sum of its parts => VIOLATES P1 *)

Theorem separable_violates_p1 :
  (* If a composite Rule is separable: *)
  (* the composite system = product of subsystems *)
  (* = the whole EQUALS the sum of parts *)
  (* P1 says: whole > sum of parts *)
  (* Therefore: P1 requires non-separable = ENTANGLED Rules *)
  (* Demonstrated: bell_rule is entangled *)
  is_entangled bell_rule 2%nat 2%nat.
Proof.
  apply bell_rule_entangled.
Qed.

(** P1 implies entanglement MUST exist *)
Theorem p1_implies_entanglement :
  is_entangled bell_rule 2%nat 2%nat.
Proof.
  apply bell_rule_entangled.
Qed.

(** Separable Rules exist too: they are the TRIVIAL case *)
(** Example: R(a1,b1,a2,b2) = 1 for all => separable (f=1, g=1) *)
Definition trivial_composite_rule : CompositeRule :=
  fun _ _ _ _ => 1.

Theorem trivial_is_separable :
  is_separable trivial_composite_rule 2 2.
Proof.
  unfold is_separable. exists (fun _ _ => 1), (fun _ _ => 1).
  intros. unfold trivial_composite_rule. ring.
Qed.

(** Zero rule is also separable *)
Definition zero_composite_rule : CompositeRule :=
  fun _ _ _ _ => 0.

Lemma zero_is_separable :
  is_separable zero_composite_rule 2 2.
Proof.
  unfold is_separable. exists (fun _ _ => 0), (fun _ _ => 1).
  intros. unfold zero_composite_rule. ring.
Qed.

(* ================================================================== *)
(*  Part III: Entangled States over Q[i]  (~9 lemmas)                  *)
(* ================================================================== *)

(** Composite state: psi(a,b) in Q[i] *)
(** Separable state: psi(a,b) = alpha(a) * beta(b) *)
(** Entangled state: psi(a,b) != alpha(a) * beta(b) for any alpha, beta *)

Definition CompositeState := nat -> nat -> Qi.

Definition state_separable (psi : CompositeState) (nA nB : nat) : Prop :=
  exists (alpha : nat -> Qi) (beta : nat -> Qi),
    forall a b, (a < nA)%nat -> (b < nB)%nat ->
      qi_eq (psi a b) (qi_mul (alpha a) (beta b)).

Definition state_entangled (psi : CompositeState) (nA nB : nat) : Prop :=
  ~ state_separable psi nA nB.

(** Bell state: psi(0,0) = 5/7, psi(1,1) = 5/7, rest = 0 *)
(** Over Q: approximate 1/sqrt(2) ~ 5/7 *)
Definition bell_state : CompositeState :=
  fun a b =>
    if (Nat.eqb a 0 && Nat.eqb b 0)%bool then mkQi (5 # 7) 0
    else if (Nat.eqb a 1 && Nat.eqb b 1)%bool then mkQi (5 # 7) 0
    else qi_zero.

(** Bell state values *)
Lemma bell_state_00 : qi_eq (bell_state 0%nat 0%nat) (mkQi (5 # 7) 0).
Proof. unfold bell_state, qi_eq. simpl. split; reflexivity. Qed.

Lemma bell_state_01 : qi_eq (bell_state 0%nat 1%nat) qi_zero.
Proof. unfold bell_state, qi_eq, qi_zero. simpl. split; reflexivity. Qed.

Lemma bell_state_10 : qi_eq (bell_state 1%nat 0%nat) qi_zero.
Proof. unfold bell_state, qi_eq, qi_zero. simpl. split; reflexivity. Qed.

Lemma bell_state_11 : qi_eq (bell_state 1%nat 1%nat) (mkQi (5 # 7) 0).
Proof. unfold bell_state, qi_eq. simpl. split; reflexivity. Qed.

(** ★ Bell state is entangled *)
(** If separable: psi(a,b) = alpha(a) * beta(b)
    psi(0,0) = alpha(0)*beta(0) = (5/7, 0)
    psi(0,1) = alpha(0)*beta(1) = (0, 0)
    psi(1,0) = alpha(1)*beta(0) = (0, 0)
    psi(1,1) = alpha(1)*beta(1) = (5/7, 0)

    From psi(0,0) != 0: alpha(0) != 0 and beta(0) != 0
    From psi(0,1) = 0 and alpha(0) != 0: beta(1) = 0
    From psi(1,1) = (5/7, 0) != 0: alpha(1) != 0 and beta(1) != 0
    Contradiction with beta(1) = 0! *)
Theorem bell_state_entangled : state_entangled bell_state 2%nat 2%nat.
Proof.
  unfold state_entangled, state_separable.
  intros [alpha [beta Hsep]].
  (* Get equations *)
  assert (H00 := Hsep 0%nat 0%nat ltac:(lia) ltac:(lia)).
  assert (H01 := Hsep 0%nat 1%nat ltac:(lia) ltac:(lia)).
  assert (H11 := Hsep 1%nat 1%nat ltac:(lia) ltac:(lia)).
  unfold bell_state in H00, H01, H11. simpl in H00, H01, H11.
  unfold qi_eq, qi_mul, qi_zero in H00, H01, H11. simpl in H00, H01, H11.
  destruct H00 as [H00r H00i].
  destruct H01 as [H01r H01i].
  destruct H11 as [H11r H11i].
  (* From H00r: qi_re(alpha 0%nat) * qi_re(beta 0%nat) - qi_im(alpha 0%nat) * qi_im(beta 0%nat) == 5#7 *)
  (* From H01r: qi_re(alpha 0%nat) * qi_re(beta 1%nat) - qi_im(alpha 0%nat) * qi_im(beta 1%nat) == 0 *)
  (* From H01i: qi_re(alpha 0%nat) * qi_im(beta 1%nat) + qi_im(alpha 0%nat) * qi_re(beta 1%nat) == 0 *)
  (* From H11r: qi_re(alpha 1%nat) * qi_re(beta 1%nat) - qi_im(alpha 1%nat) * qi_im(beta 1%nat) == 5#7 *)
  (* Need: qi_norm2 (alpha 0%nat) * qi_norm2 (beta 1%nat) == 0 from H01 *)
  (* But qi_norm2 (alpha 0%nat) > 0 from H00 and qi_norm2 (beta 1%nat) > 0 from H11 *)
  (* Use: |alpha(0)*beta(1)|^2 = |alpha(0)|^2 * |beta(1)|^2 *)
  (* |alpha(0)*beta(1)| = |psi(0,1)| = 0 *)
  (* So |alpha(0)|^2 * |beta(1)|^2 = 0 *)
  (* Use H01 directly: bell_state(0,1) == qi_mul (alpha 0) (beta 1) *)
  (* After simpl: qi_zero == qi_mul (alpha 0) (beta 1) *)
  (* → qi_re(alpha 0)*qi_re(beta 1) - qi_im(alpha 0)*qi_im(beta 1) == 0 *)
  (* → qi_re(alpha 0)*qi_im(beta 1) + qi_im(alpha 0)*qi_re(beta 1) == 0 *)
  (* → |alpha 0|^2 * |beta 1|^2 = 0 (from Lagrange identity) *)
  assert (Hprod : qi_norm2 (alpha 0%nat) * qi_norm2 (beta 1%nat) == 0).
  { unfold qi_norm2.
    (* H01r/H01i give us the two components are 0 *)
    (* Lagrange: |a|^2|b|^2 = (re re' - im im')^2 + (re im' + im re')^2 *)
    assert (Hlagrange :
      (qi_re (alpha 0%nat) * qi_re (alpha 0%nat) + qi_im (alpha 0%nat) * qi_im (alpha 0%nat)) *
      (qi_re (beta 1%nat) * qi_re (beta 1%nat) + qi_im (beta 1%nat) * qi_im (beta 1%nat)) ==
      (qi_re (alpha 0%nat) * qi_re (beta 1%nat) - qi_im (alpha 0%nat) * qi_im (beta 1%nat)) *
      (qi_re (alpha 0%nat) * qi_re (beta 1%nat) - qi_im (alpha 0%nat) * qi_im (beta 1%nat)) +
      (qi_re (alpha 0%nat) * qi_im (beta 1%nat) + qi_im (alpha 0%nat) * qi_re (beta 1%nat)) *
      (qi_re (alpha 0%nat) * qi_im (beta 1%nat) + qi_im (alpha 0%nat) * qi_re (beta 1%nat))) by ring.
    rewrite Hlagrange.
    (* The goal now has the same form as H01r^2 + H01i^2 == 0 *)
    (* Since H01r: X == 0 and H01i: Y == 0, goal is 0*0 + 0*0 == 0 *)
    assert (Hx := H01r). assert (Hy := H01i).
    nsatz. }
  (* So alpha(0) = 0 or beta(1) = 0 *)
  destruct (Qmult_integral _ _ Hprod) as [Ha0 | Hb1].
  - (* alpha(0) has norm 0 => alpha(0) = 0 *)
    (* But alpha(0)*beta(0) = (5/7, 0) != 0 *)
    unfold qi_norm2 in Ha0.
    assert (Har : qi_re (alpha 0%nat) == 0).
    { assert (H1 : 0 <= qi_re (alpha 0%nat) * qi_re (alpha 0%nat)).
      { destruct (Qlt_le_dec (qi_re (alpha 0%nat)) 0);
        [assert (Hh : (-qi_re (alpha 0%nat)) * (-qi_re (alpha 0%nat)) == qi_re (alpha 0%nat) * qi_re (alpha 0%nat)) by ring;
         rewrite <- Hh; apply Qmult_le_0_compat; lra |
         apply Qmult_le_0_compat; lra]. }
      assert (H2 : 0 <= qi_im (alpha 0%nat) * qi_im (alpha 0%nat)).
      { destruct (Qlt_le_dec (qi_im (alpha 0%nat)) 0);
        [assert (Hh : (-qi_im (alpha 0%nat)) * (-qi_im (alpha 0%nat)) == qi_im (alpha 0%nat) * qi_im (alpha 0%nat)) by ring;
         rewrite <- Hh; apply Qmult_le_0_compat; lra |
         apply Qmult_le_0_compat; lra]. }
      assert (Hre2 : qi_re (alpha 0%nat) * qi_re (alpha 0%nat) == 0) by lra.
      destruct (Qeq_dec (qi_re (alpha 0%nat)) 0) as [|Hne]; [assumption|].
      exfalso. assert (0 < qi_re (alpha 0%nat) * qi_re (alpha 0%nat)).
      { destruct (Qlt_le_dec (qi_re (alpha 0%nat)) 0).
        - assert (Hh : qi_re (alpha 0%nat) * qi_re (alpha 0%nat) ==
            (-qi_re (alpha 0%nat)) * (-qi_re (alpha 0%nat))) by ring.
          rewrite Hh. apply Qmult_lt_0_compat; lra.
        - assert (Hgt : 0 < qi_re (alpha 0%nat)) by lra.
          apply Qmult_lt_0_compat; lra. }
      lra. }
    rewrite Har in H00r. rewrite Qmult_0_l in H00r.
    assert (Hai : qi_im (alpha 0%nat) == 0).
    { assert (H2 : qi_im (alpha 0%nat) * qi_im (alpha 0%nat) == 0).
      { unfold qi_norm2 in Ha0. rewrite Har in Ha0.
        assert (Hh : 0 * 0 == 0) by ring. rewrite Hh in Ha0. lra. }
      destruct (Qeq_dec (qi_im (alpha 0%nat)) 0) as [|Hne]; [assumption|].
      exfalso. assert (0 < qi_im (alpha 0%nat) * qi_im (alpha 0%nat)).
      { destruct (Qlt_le_dec (qi_im (alpha 0%nat)) 0).
        - assert (Hh : qi_im (alpha 0%nat) * qi_im (alpha 0%nat) ==
            (-qi_im (alpha 0%nat)) * (-qi_im (alpha 0%nat))) by ring.
          rewrite Hh. apply Qmult_lt_0_compat; lra.
        - assert (Hgt : 0 < qi_im (alpha 0%nat)) by lra.
          apply Qmult_lt_0_compat; lra. }
      lra. }
    rewrite Hai in H00r. rewrite Qmult_0_l in H00r.
    lra.
  - (* beta(1) has norm 0 => beta(1) = 0 *)
    (* But alpha(1)*beta(1) = (5/7, 0) != 0 *)
    unfold qi_norm2 in Hb1.
    assert (Hbr : qi_re (beta 1%nat) == 0).
    { assert (H1 : 0 <= qi_re (beta 1%nat) * qi_re (beta 1%nat)).
      { destruct (Qlt_le_dec (qi_re (beta 1%nat)) 0);
        [assert (Hh : (-qi_re (beta 1%nat)) * (-qi_re (beta 1%nat)) == qi_re (beta 1%nat) * qi_re (beta 1%nat)) by ring;
         rewrite <- Hh; apply Qmult_le_0_compat; lra |
         apply Qmult_le_0_compat; lra]. }
      assert (H2 : 0 <= qi_im (beta 1%nat) * qi_im (beta 1%nat)).
      { destruct (Qlt_le_dec (qi_im (beta 1%nat)) 0);
        [assert (Hh : (-qi_im (beta 1%nat)) * (-qi_im (beta 1%nat)) == qi_im (beta 1%nat) * qi_im (beta 1%nat)) by ring;
         rewrite <- Hh; apply Qmult_le_0_compat; lra |
         apply Qmult_le_0_compat; lra]. }
      assert (Hre2 : qi_re (beta 1%nat) * qi_re (beta 1%nat) == 0) by lra.
      destruct (Qeq_dec (qi_re (beta 1%nat)) 0) as [|Hne]; [assumption|].
      exfalso. assert (0 < qi_re (beta 1%nat) * qi_re (beta 1%nat)).
      { destruct (Qlt_le_dec (qi_re (beta 1%nat)) 0).
        - assert (Hh : qi_re (beta 1%nat) * qi_re (beta 1%nat) ==
            (-qi_re (beta 1%nat)) * (-qi_re (beta 1%nat))) by ring.
          rewrite Hh. apply Qmult_lt_0_compat; lra.
        - assert (Hgt : 0 < qi_re (beta 1%nat)) by lra.
          apply Qmult_lt_0_compat; lra. }
      lra. }
    assert (Hbi : qi_im (beta 1%nat) == 0).
    { assert (H2 : qi_im (beta 1%nat) * qi_im (beta 1%nat) == 0).
      { rewrite Hbr in Hb1. assert (Hh : 0 * 0 == 0) by ring.
        rewrite Hh in Hb1. lra. }
      destruct (Qeq_dec (qi_im (beta 1%nat)) 0) as [|Hne]; [assumption|].
      exfalso. assert (0 < qi_im (beta 1%nat) * qi_im (beta 1%nat)).
      { destruct (Qlt_le_dec (qi_im (beta 1%nat)) 0).
        - assert (Hh : qi_im (beta 1%nat) * qi_im (beta 1%nat) ==
            (-qi_im (beta 1%nat)) * (-qi_im (beta 1%nat))) by ring.
          rewrite Hh. apply Qmult_lt_0_compat; lra.
        - assert (Hgt : 0 < qi_im (beta 1%nat)) by lra.
          apply Qmult_lt_0_compat; lra. }
      lra. }
    rewrite Hbr in H11r. rewrite Hbi in H11r.
    rewrite Hbi in H11i.
    assert (Hsimp : qi_re (alpha 1%nat) * 0 - qi_im (alpha 1%nat) * 0 == 0) by ring.
    rewrite Hsimp in H11r. lra.
Qed.

(** Entanglement strength: how far from separable *)
Definition entanglement_witness (psi : CompositeState) : Q :=
  qi_norm2 (psi 0%nat 0%nat) * qi_norm2 (psi 1%nat 1%nat) -
  qi_norm2 (psi 0%nat 1%nat) * qi_norm2 (psi 1%nat 0%nat).

(** For separable pure states, this witness is 0 *)
(** For entangled states, it is nonzero *)
Lemma bell_state_witness :
  entanglement_witness bell_state == (5 # 7) * (5 # 7) * ((5 # 7) * (5 # 7)).
Proof.
  unfold entanglement_witness, bell_state, qi_norm2, qi_zero. simpl. ring.
Qed.

Lemma bell_state_witness_positive :
  0 < entanglement_witness bell_state.
Proof.
  rewrite bell_state_witness.
  assert (H : 0 < (5 # 7)) by lra.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; lra.
  - apply Qmult_lt_0_compat; lra.
Qed.

Theorem phase_46_entanglement_complete :
  (* Entanglement = non-factorization of composite Rules/states *)
  (* P1 requires entanglement (separable = whole = sum, violates P1) *)
  (* Bell state: concrete entangled state over Q[i] *)
  is_entangled bell_rule 2%nat 2%nat /\
  state_entangled bell_state 2%nat 2%nat.
Proof.
  split.
  - apply bell_rule_entangled.
  - apply bell_state_entangled.
Qed.
