(** * H1RationalDegreeUniform.v — closing H37's last caveat: the degree-uniform decider at the FULL ℚ level.
       H1GeneralDegreeConstructivity decided the integer perfect-(k+1)-power sort `∃m:ℤ, mᵏ⁺¹=D` at every k.
       Its honest caveat: the ℚ-LEVEL predicate `∃r:ℚ, rᵏ⁺¹=D` was bridged only at k=2,3 (GeneralSqrt/Cbrt).
       This proves the GENERAL-k ℚ↔ℤ bridge and hence decides the ℚ-level sort at EVERY degree — the
       degree-uniform constructivity of H1 now at full ℚ resolution.

    -- The general-k ℚ→ℤ bridge --
      qpow r (S k) == inject_Z n  ⟹  n is a perfect (k+1)-th power (∃m:ℤ, n = zpow m (S k)).
      Mechanism (generalizing GeneralCbrt): reduce r to lowest terms r' = Qred r (gcd numerator denominator
      = 1); since Qmult multiplies numerators and denominators, qpow r' (S k) has Qnum = zpow (Qnum r')(S k)
      and Qden^(S k) (lemmas qpow_num/qpow_den); cross-multiplying the Qeq gives
      zpow (Qnum r')(S k) = n · zpow (Z.pos (Qden r'))(S k), and GeneralRoot.perfect_kth_power_criterion
      (induction on k) concludes n = zpow (Qnum r')(S k).

    -- Hence decidable at every ℚ degree --
      QkthElement k D := ∃r:ℚ, qpow r (S k) == inject_Z D  ⟺  ∃m:ℤ, zpow m (S k) = D  (the bridge + inject_Z),
      and the latter is decided 0-axiom by H1GeneralDegreeConstructivity.decide_perfect_power.

    WHAT THE REPO HAS (surveyed): GeneralRoot.zpow / perfect_kth_power_criterion (the ℤ engine, ∀k);
    GeneralSqrt/GeneralCbrt (the ℚ bridges at k=2,3, by simpl on the fixed power); H1GeneralDegreeConstructivity
    (the integer decider ∀k).  GAP: the general-k ℚ bridge (no fixed power to simpl — needs qpow_num/qpow_den)
    and the ℚ-level decider ∀k.  This fills it.

    ============ E/R/R разбор ============
      Elements : ℚ-степень qpow r k; предикат QkthElement k D := ∃r:ℚ, qpow r (S k)=D.
      Roles    : Element = ᵏ⁺¹√D реализуется рациональным r (терминирует); role-limit = нет (нетерминирующий корень).
      Rules    : ℚ→ℤ мост (Qred ⊕ qpow_num/den ⊕ perfect_kth_power_criterion) ⟹ QkthElement ⟺ целая степень
                 ⟹ разрешимо ∀k (через decide_perfect_power H37).
      ДИАГНОСТИКА (P4): degree-uniform конструктивность H1 — теперь на ПОЛНОМ ℚ-уровне ∀k; последняя оговорка H37
      закрыта. ЧЕСТНО: «role-limit требует РОВНО classic» всё ещё аксиом-бюджет/мета; общий сорт неразрешим (halting).
      Уровень: `синтез` (общий-k ℚ-мост ⊕ H37-целочисленный decider).

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (builds on stdlib.GeneralRoot + foundation.H1GeneralDegreeConstructivity)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Qcanon.
From ToS Require Import stdlib.GeneralRoot.
From ToS Require Import foundation.H1GeneralDegreeConstructivity.

Open Scope Z_scope.

(* ===================================================================== *)
(*  The rational k-th power, and its numerator / denominator               *)
(* ===================================================================== *)

Fixpoint qpow (r : Q) (k : nat) : Q :=
  match k with O => 1%Q | S k' => (r * qpow r k')%Q end.

(** Qmult multiplies numerators ⟹ Qnum of qpow is zpow of Qnum. *)
Lemma qpow_num : forall (r : Q) (k : nat), Qnum (qpow r k) = zpow (Qnum r) k.
Proof.
  intros r k. induction k as [| k IH]; [ reflexivity | simpl; rewrite IH; reflexivity ].
Qed.

(** ...and Qden of qpow is the power of Qden. *)
Lemma qpow_den : forall (r : Q) (k : nat), Z.pos (Qden (qpow r k)) = zpow (Z.pos (Qden r)) k.
Proof.
  intros r k. induction k as [| k IH]; [ reflexivity | simpl; rewrite Pos2Z.inj_mul, IH; reflexivity ].
Qed.

(** qpow respects ==. *)
Lemma qpow_morphism : forall (r1 r2 : Q) (k : nat), (r1 == r2)%Q -> (qpow r1 k == qpow r2 k)%Q.
Proof.
  intros r1 r2 k Heq. induction k as [| k IH]; [ reflexivity | simpl; rewrite IH, Heq; reflexivity ].
Qed.

(** qpow of an integer is the integer power. *)
Lemma qpow_inject : forall (m : Z) (j : nat), (qpow (inject_Z m) j == inject_Z (zpow m j))%Q.
Proof.
  intros m j. induction j as [| j IH]; [ reflexivity | ].
  simpl. rewrite IH, <- inject_Z_mult. reflexivity.
Qed.

(* ===================================================================== *)
(*  ★ THE GENERAL-k ℚ→ℤ BRIDGE                                            *)
(* ===================================================================== *)

(** ★ If a rational r raised to the (k+1)-th power is the integer n, then n is a perfect (k+1)-th power.
    The degree-uniform bridge (generalizes GeneralSqrt/GeneralCbrt past the fixed-power simpl). *)
Lemma rational_kth_power_is_perfect : forall (r : Q) (n : Z) (k : nat),
  (qpow r (S k) == inject_Z n)%Q -> exists m : Z, n = zpow m (S k).
Proof.
  intros r n k H.
  remember (Qred r) as r' eqn:Er'.
  assert (Hr' : (qpow r' (S k) == inject_Z n)%Q).
  { rewrite Er'. rewrite (qpow_morphism (Qred r) r (S k) (Qred_correct r)). exact H. }
  assert (Hcop : Z.gcd (Qnum r') (Z.pos (Qden r')) = 1).
  { rewrite Er'. apply Qcanon.Qred_identity2. apply Qcanon.Qred_involutive. }
  assert (Hz : zpow (Qnum r') (S k) = n * zpow (Z.pos (Qden r')) (S k)).
  { unfold Qeq in Hr'. rewrite qpow_num, qpow_den in Hr'.
    unfold inject_Z in Hr'. cbn [Qnum Qden] in Hr'.
    rewrite Z.mul_1_r in Hr'. exact Hr'. }
  apply (perfect_kth_power_criterion (Qnum r') (Z.pos (Qden r')) n k).
  - apply Pos2Z.is_pos.
  - exact Hcop.
  - exact Hz.
Qed.

(* ===================================================================== *)
(*  The ℚ-level predicate, the bridge to integers, and the decider ∀k      *)
(* ===================================================================== *)

(** The degree-(k+1) Element predicate at the ℚ level. *)
Definition QkthElement (k : nat) (D : Z) : Prop := exists r : Q, (qpow r (S k) == inject_Z D)%Q.

(** ★ The ℚ predicate is exactly the integer perfect-power predicate. *)
Lemma QkthElement_iff_intpower : forall (k : nat) (D : Z),
  QkthElement k D <-> exists m : Z, zpow m (S k) = D.
Proof.
  intros k D. split.
  - intros [r Hr]. destruct (rational_kth_power_is_perfect r D k Hr) as [m Hm].
    exists m. symmetry. exact Hm.
  - intros [m Hm]. exists (inject_Z m). rewrite qpow_inject, <- Hm. reflexivity.
Qed.

(** ★★★ Hence the ℚ-level Element/role-limit sort is a constructive total decider at EVERY degree (0-axiom). *)
Lemma decide_QkthElement : forall (k : nat) (D : Z), {QkthElement k D} + {~ QkthElement k D}.
Proof.
  intros k D. destruct (decide_perfect_power k D) as [H | H].
  - left. apply QkthElement_iff_intpower. exact H.
  - right. intro HC. apply H. apply QkthElement_iff_intpower. exact HC.
Qed.

(** ★★ The LEM-instance is a THEOREM at every ℚ degree (0-axiom). *)
Lemma Qkth_element_or_not : forall (k : nat) (D : Z), QkthElement k D \/ ~ QkthElement k D.
Proof. intros k D. destruct (decide_QkthElement k D) as [H | H]; [ left | right ]; exact H. Qed.

(* ===================================================================== *)
(*  Concrete (ℚ level): √36, ∛8 Element ; ∛2, √5, ⁴√5 role-limit          *)
(* ===================================================================== *)

Example qkth_sqrt36 : QkthElement 1%nat 36.        (* ∃r:ℚ, r² = 36 (r=6) *)
Proof. apply QkthElement_iff_intpower. exists 6. reflexivity. Qed.

Example qkth_cbrt8 : QkthElement 2%nat 8.          (* ∃r:ℚ, r³ = 8 (r=2) *)
Proof. apply QkthElement_iff_intpower. exists 2. reflexivity. Qed.

Example qkth_cbrt2_no : ~ QkthElement 2%nat 2.     (* ∛2 ∉ ℚ (Delian) *)
Proof. rewrite QkthElement_iff_intpower, <- (is_kth_power_correct 2%nat 2). vm_compute. discriminate. Qed.

Example qkth_sqrt5_no : ~ QkthElement 1%nat 5.     (* √5 ∉ ℚ *)
Proof. rewrite QkthElement_iff_intpower, <- (is_kth_power_correct 1%nat 5). vm_compute. discriminate. Qed.

Example qkth_quart5_no : ~ QkthElement 3%nat 5.    (* ⁴√5 ∉ ℚ (degree 4) *)
Proof. rewrite QkthElement_iff_intpower, <- (is_kth_power_correct 3%nat 5). vm_compute. discriminate. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** H37's last caveat closed — the degree-uniform sort at full ℚ resolution:
      (bridge)     qpow r (S k) == inject_Z n ⟹ n is a perfect (k+1)-th power (general-k ℚ→ℤ bridge);
      (iff)        the ℚ predicate ∃r:ℚ, rᵏ⁺¹=D equals the integer one ∃m:ℤ, mᵏ⁺¹=D;
      (decidable)  the ℚ-level sort is a constructive total decider at EVERY degree;
      (LEM = thm)  hence the LEM-instance is a theorem at every ℚ degree, 0-axiom;
      (concrete)   √36, ∛8 Element ; ∛2 (Delian), √5, ⁴√5 role-limit — all at the ℚ level.
    So H1's degree-uniform constructive half is now at full ℚ resolution, not just integer.  Honest: the
    "role-limit needs exactly classic" direction remains axiom-budget meta, and the GENERAL sort is
    undecidable (halting) — decidability holds exactly on the computable-criterion classes. *)
Theorem H1_rational_degree_uniform :
  (forall (r : Q) (n : Z) (k : nat), (qpow r (S k) == inject_Z n)%Q -> exists m : Z, n = zpow m (S k))
  /\ (forall (k : nat) (D : Z), QkthElement k D <-> exists m : Z, zpow m (S k) = D)
  /\ (forall (k : nat) (D : Z), QkthElement k D \/ ~ QkthElement k D)
  /\ QkthElement 1%nat 36
  /\ QkthElement 2%nat 8
  /\ ~ QkthElement 2%nat 2
  /\ ~ QkthElement 1%nat 5.
Proof.
  split. exact rational_kth_power_is_perfect.
  split. exact QkthElement_iff_intpower.
  split. exact Qkth_element_or_not.
  split. exact qkth_sqrt36.
  split. exact qkth_cbrt8.
  split. exact qkth_cbrt2_no.
  exact qkth_sqrt5_no.
Qed.
