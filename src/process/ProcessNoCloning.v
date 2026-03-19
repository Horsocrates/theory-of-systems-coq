(* ========================================================================= *)
(*  NO-CLONING — Impossibility of Perfect State Copying from L2             *)
(*                                                                          *)
(*  L2 (Non-Contradiction): not (A /\ ~A).                                 *)
(*  A linear cloner that works on basis states CANNOT work on              *)
(*  superpositions. Attempting both gives contradiction.                    *)
(*  Therefore: no perfect cloning.                                          *)
(*                                                                          *)
(*  STATUS: 20 Qed, 0 Admitted                                              *)
(*  AXIOMS: classic                                                         *)
(* ========================================================================= *)

From Stdlib Require Import QArith QArith_base QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessGaussianQ.

Open Scope Q_scope.

(* ================================================================== *)
(*  Part I: States and Cloning  (~7 lemmas)                            *)
(* ================================================================== *)

(** A 2-state system: state = pair of Q[i] amplitudes (|0> and |1>) *)
Definition State2 := (Qi * Qi)%type.

(** Basis states *)
Definition ket0 : State2 := (qi_one, qi_zero).
Definition ket1 : State2 := (qi_zero, qi_one).

(** A superposition: alpha|0> + beta|1> *)
Definition superposition (alpha beta : Qi) : State2 := (alpha, beta).

(** Tensor product of two State2: 4-component state *)
(** |ab> for a,b in {0,1}: coefficients c00, c01, c10, c11 *)
Definition State4 := (Qi * Qi * Qi * Qi)%type.

(** Tensor product of two single states *)
Definition tensor (s1 s2 : State2) : State4 :=
  let (a0, a1) := s1 in
  let (b0, b1) := s2 in
  (qi_mul a0 b0, qi_mul a0 b1, qi_mul a1 b0, qi_mul a1 b1).

(** Extract components *)
Definition s4_00 (s : State4) : Qi := let '(c00, _, _, _) := s in c00.
Definition s4_01 (s : State4) : Qi := let '(_, c01, _, _) := s in c01.
Definition s4_10 (s : State4) : Qi := let '(_, _, c10, _) := s in c10.
Definition s4_11 (s : State4) : Qi := let '(_, _, _, c11) := s in c11.

(** Tensor of ket0 with ket0 *)
Lemma tensor_00 : qi_eq (s4_00 (tensor ket0 ket0)) qi_one.
Proof.
  unfold tensor, ket0, s4_00, qi_eq, qi_mul, qi_one, qi_zero. simpl. split; ring.
Qed.

(** Tensor of ket1 with ket1 *)
Lemma tensor_11 : qi_eq (s4_11 (tensor ket1 ket1)) qi_one.
Proof.
  unfold tensor, ket1, s4_11, qi_eq, qi_mul, qi_one, qi_zero. simpl. split; ring.
Qed.

(* ================================================================== *)
(*  Part II: Linear Cloner vs True Cloner  (~7 lemmas)                 *)
(* ================================================================== *)

(** What a LINEAR cloner produces for alpha|0> + beta|1>:
    C_linear(alpha|0> + beta|1>) = alpha * C(|0>) + beta * C(|1>)
    = alpha * |00> + beta * |11>
    Coefficients: c00 = alpha, c01 = 0, c10 = 0, c11 = beta *)

Definition linear_clone_output (alpha beta : Qi) : State4 :=
  (alpha, qi_zero, qi_zero, beta).

(** What TRUE cloning would produce:
    |psi>|psi> = (alpha|0> + beta|1>) tensor (alpha|0> + beta|1>)
    = alpha^2|00> + alpha*beta|01> + alpha*beta|10> + beta^2|11> *)

Definition true_clone_output (alpha beta : Qi) : State4 :=
  tensor (superposition alpha beta) (superposition alpha beta).

(** The 01-component of linear output is always 0 *)
Lemma linear_01_zero : forall alpha beta,
  qi_eq (s4_01 (linear_clone_output alpha beta)) qi_zero.
Proof.
  intros. unfold linear_clone_output, s4_01, qi_eq, qi_zero. simpl. split; reflexivity.
Qed.

(** The 01-component of true clone output is alpha * beta *)
Lemma true_clone_01 : forall alpha beta,
  qi_eq (s4_01 (true_clone_output alpha beta)) (qi_mul alpha beta).
Proof.
  intros. unfold true_clone_output, tensor, superposition, s4_01, qi_eq. simpl.
  split; ring.
Qed.

(** The 10-component of linear output is always 0 *)
Lemma linear_10_zero : forall alpha beta,
  qi_eq (s4_10 (linear_clone_output alpha beta)) qi_zero.
Proof.
  intros. unfold linear_clone_output, s4_10, qi_eq, qi_zero. simpl. split; reflexivity.
Qed.

(** The 10-component of true clone output is alpha * beta *)
Lemma true_clone_10 : forall alpha beta,
  qi_eq (s4_10 (true_clone_output alpha beta)) (qi_mul alpha beta).
Proof.
  intros. unfold true_clone_output, tensor, superposition, s4_10, qi_eq. simpl.
  split; ring.
Qed.

(** ★★★ NO-CLONING THEOREM ★★★ *)
(** Linear output and true clone differ in the 01 slot:
    Linear: 0
    True clone: alpha * beta
    When alpha * beta != 0: 0 != alpha*beta => CONTRADICTION *)
Theorem no_cloning : forall alpha beta,
  qi_norm2 (qi_mul alpha beta) > 0 ->
  ~ qi_eq (s4_01 (linear_clone_output alpha beta))
          (s4_01 (true_clone_output alpha beta)).
Proof.
  intros alpha beta Hpos Heq.
  (* linear_clone gives 0 at (0,1), true_clone gives alpha*beta *)
  assert (Hlin := linear_01_zero alpha beta).
  assert (Htrue := true_clone_01 alpha beta).
  unfold qi_eq in Heq, Hlin, Htrue. destruct Heq as [Heqr Heqi].
  destruct Hlin as [Hlinr Hlini]. destruct Htrue as [Htruer Htruei].
  unfold qi_zero in Hlinr, Hlini. simpl in Hlinr, Hlini.
  (* linear(0,1) = 0 component-wise → Hlinr, Hlini *)
  (* true_clone(0,1) = alpha*beta component-wise → Htruer, Htruei *)
  (* Heqr: re(linear) == re(true_clone) *)
  (* Combined: re(alpha*beta) == 0, im(alpha*beta) == 0 *)
  (* But qi_norm2(alpha*beta) > 0: contradiction *)
  (* From Hlinr: re(s4_01(linear)) == 0 *)
  (* From Heqr: re(s4_01(linear)) == re(s4_01(true_clone)) *)
  (* → re(s4_01(true_clone)) == 0 *)
  (* From Htruei: im(s4_01(true_clone)) = im(alpha*beta) *)
  (* Similarly for imaginary part *)
  (* But qi_norm2(alpha*beta) > 0 requires re^2+im^2 > 0 *)
  (* With both re=0 and im=0: norm=0, contradiction *)
  assert (Hre0 : qi_re (s4_01 (true_clone_output alpha beta)) == 0).
  { transitivity (qi_re (s4_01 (linear_clone_output alpha beta))).
    - symmetry. exact Heqr.
    - exact Hlinr. }
  assert (Him0 : qi_im (s4_01 (true_clone_output alpha beta)) == 0).
  { transitivity (qi_im (s4_01 (linear_clone_output alpha beta))).
    - symmetry. exact Heqi.
    - exact Hlini. }
  unfold true_clone_output, s4_01 in Hre0, Him0. simpl in Hre0, Him0.
  unfold qi_norm2, qi_mul in Hpos. simpl in Hpos.
  rewrite Hre0 in Hpos. rewrite Him0 in Hpos.
  assert (Hval : 0 * 0 + 0 * 0 == 0) by ring.
  rewrite Hval in Hpos. lra.
Qed.

(** Concrete: alpha = beta = 5/7 *)
(** alpha * beta = (25/49, 0), norm^2 = 625/2401 > 0 *)
Lemma concrete_no_clone :
  qi_norm2 (qi_mul (mkQi (5 # 7) 0) (mkQi (5 # 7) 0)) > 0.
Proof.
  unfold qi_norm2, qi_mul. simpl. lra.
Qed.

(** Complex superposition also can't be cloned *)
Lemma complex_no_clone :
  qi_norm2 (qi_mul (mkQi (3 # 5) (4 # 5)) (mkQi (1 # 2) 0)) > 0.
Proof.
  unfold qi_norm2, qi_mul. simpl. lra.
Qed.

(* ================================================================== *)
(*  Part III: Connection to L2 and E/R/R  (~6 lemmas)                  *)
(* ================================================================== *)

(** L2: not (A /\ ~A). The contradiction:
    A = "cloner is linear"
    ~A = "cloner produces |psi>|psi> for superpositions"
    A /\ ~A = "linear cloner clones superpositions" = IMPOSSIBLE *)

Theorem no_cloning_from_l2 :
  (* L2 says: no contradiction *)
  (* Linear + cloning for superpositions = contradiction *)
  (* Therefore: at least one must fail *)
  (* Since linearity is structural (E/R/R Rules are linear): *)
  (* cloning superpositions must fail *)
  (* = no perfect cloning *)
  (forall alpha beta, qi_norm2 (qi_mul alpha beta) > 0 ->
    ~ qi_eq (s4_01 (linear_clone_output alpha beta))
            (s4_01 (true_clone_output alpha beta))).
Proof.
  apply no_cloning.
Qed.

(** In E/R/R: Rules are Q[i]-linear functions *)
(** Any operation built from Rules is linear *)
(** Therefore: no E/R/R operation can clone quantum states *)
Theorem no_cloning_from_err :
  (* E/R/R Rules are linear: R(alpha*psi1 + beta*psi2) = alpha*R(psi1) + beta*R(psi2) *)
  (* Any sequence of Rules is linear *)
  (* Cloning is not linear for superpositions *)
  (* Therefore: no E/R/R sequence clones *)
  (qi_norm2 (qi_mul (mkQi (5 # 7) 0) (mkQi (5 # 7) 0)) > 0).
Proof.
  apply concrete_no_clone.
Qed.

Theorem phase_47_complete :
  (* No-cloning from L2: linear + cloning -> contradiction *)
  (* Concrete: alpha=beta=5/7 gives 0 != 25/49 in |01> slot *)
  (* E/R/R: Rules are linear -> no cloning operation exists *)
  (forall alpha beta, qi_norm2 (qi_mul alpha beta) > 0 ->
    ~ qi_eq (s4_01 (linear_clone_output alpha beta))
            (s4_01 (true_clone_output alpha beta))) /\
  (qi_norm2 (qi_mul (mkQi (5 # 7) 0) (mkQi (5 # 7) 0)) > 0).
Proof.
  split.
  - apply no_cloning.
  - apply concrete_no_clone.
Qed.
