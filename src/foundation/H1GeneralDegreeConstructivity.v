(** * H1GeneralDegreeConstructivity.v — H1's constructive half, DEGREE-UNIFORM: decidable at EVERY degree.
       H1ConstructivityDecidable (deg 2) and H1CubicConstructivity (deg 3) decided the Element/role-limit
       sort per degree.  This proves it at EVERY degree k at once: the integer perfect-(k+1)-th-power
       predicate `∃m:ℤ, mᵏ⁺¹ = D` is a CONSTRUCTIVE TOTAL DECIDER (0 axioms) for all k — so the LEM-instance
       is a THEOREM at every degree.  This matches GeneralRoot's degree-uniform BRIDGE engine (induction on
       k): the finitization boundary's constructive half is now machine-proved decidable degree-uniformly.

       The new work: an integer k-th-ROOT decider for arbitrary k (Stdlib has neither Z.sqrt-general nor
       Z.cbrt).  Any root m of mᵏ⁺¹ = D is bounded, |m| ≤ |D| (since |m| ≤ |m|ᵏ⁺¹ = |D|), so a symmetric
       bounded search over {±j : j ≤ |D|} is total and correct — parity-free (both signs are tested).

    WHAT THE REPO HAS (surveyed): GeneralRoot.v — `zpow` (integer k-th power), `perfect_kth_power_criterion`
    (reduced fraction with integer (k+1)-th power ⟹ perfect (k+1)-th power, by induction on k — the
    degree-uniform BRIDGE).  GeneralSqrt/GeneralCbrt — the ℚ↔ℤ bridges at k=2,3.  GAP: no DECIDER at general
    k (no k-th-root search, no degree-uniform LEM-instance).  This adds it (reusing GeneralRoot's `zpow`).

    ============ E/R/R разбор ============
      Elements : степень k+1, радиканд D:ℤ; целая k-я степень zpow m (S k); предикат ∃m:ℤ, zpow m (S k)=D.
      Roles    : Element = есть целый корень (терминирует) на степени k+1; role-limit = нет (ᵏ⁺¹√D нетерминирующий).
      Rules    : корень ограничен |m|≤|D| ⟹ симметричный конечный поиск ⟹ сорт вычислим, тотален, 0-акс ⟹
                 LEM-инстанс — ТЕОРЕМА на КАЖДОЙ степени (degree-uniform, как индукция GeneralRoot).
      ДИАГНОСТИКА (P4): конструктивная половина H1 разрешима DEGREE-UNIFORMLY — теорема ∀k, не наблюдение. ЧЕСТНО:
      целочисленный уровень ∀k; ℚ-мост связан на k=2,3 (GeneralSqrt/GeneralCbrt); общий-k ℚ-мост = механический
      лифт движка GeneralRoot. Уровень: `синтез` (k-й корень над ℤ ∀k ⊕ zpow GeneralRoot → degree-uniform decider).

    STATUS: 13 Qed, 0 Admitted, 0 axioms  (builds on stdlib.GeneralRoot)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Lia List Bool.
From ToS Require Import stdlib.GeneralRoot.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  zpow vs absolute value, and the root bound |m| <= |D|                   *)
(* ===================================================================== *)

(** Z.abs distributes over the integer k-th power. *)
Lemma zpow_abs : forall (m : Z) (k : nat), Z.abs (zpow m k) = zpow (Z.abs m) k.
Proof.
  intros m k. induction k as [| k IH].
  - reflexivity.
  - simpl. rewrite Z.abs_mul, IH. reflexivity.
Qed.

(** For a base ≥ 1, the (k+1)-th power dominates the base. *)
Lemma zpow_ge_base : forall (a : Z) (k : nat), 1 <= a -> a <= zpow a (S k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - simpl. nia.
  - simpl. simpl in IH. nia.
Qed.

(** ★ Any (k+1)-th root m of D is bounded: |m| ≤ |D|. *)
Lemma root_abs_bound : forall (m : Z) (k : nat) (D : Z), zpow m (S k) = D -> Z.abs m <= Z.abs D.
Proof.
  intros m k D HD. rewrite <- HD, zpow_abs.
  destruct (Z.eq_dec (Z.abs m) 0) as [Hz | Hnz].
  - rewrite Hz. assert (H0 : zpow 0 (S k) = 0) by (simpl; ring). rewrite H0. lia.
  - apply zpow_ge_base. pose proof (Z.abs_nonneg m). lia.
Qed.

(* ===================================================================== *)
(*  The symmetric bounded candidate list, and membership of any root       *)
(* ===================================================================== *)

(** Candidates for a root of D: ±j for every j ≤ |D| (both signs — parity-free). *)
Definition root_cands (D : Z) : list Z :=
  map Z.of_nat (seq 0 (S (Z.to_nat (Z.abs D))))
  ++ map (fun j => - Z.of_nat j) (seq 0 (S (Z.to_nat (Z.abs D)))).

(** Every integer bounded by |D| in absolute value is a candidate. *)
Lemma In_root_cands : forall m D : Z, Z.abs m <= Z.abs D -> In m (root_cands D).
Proof.
  intros m D Hb. unfold root_cands. apply in_or_app.
  destruct (Z_le_dec 0 m) as [Hpos | Hneg].
  - left. apply in_map_iff. exists (Z.to_nat m). split.
    + apply Z2Nat.id. exact Hpos.
    + apply in_seq. split; [ lia | ].
      rewrite Z.abs_eq in Hb by exact Hpos.
      assert (Hle : (Z.to_nat m <= Z.to_nat (Z.abs D))%nat)
        by (apply Z2Nat.inj_le; [ exact Hpos | apply Z.abs_nonneg | exact Hb ]).
      lia.
  - right. apply in_map_iff. exists (Z.to_nat (- m)). split.
    + rewrite Z2Nat.id by lia. ring.
    + apply in_seq. split; [ lia | ].
      rewrite Z.abs_neq in Hb by lia.
      assert (Hle : (Z.to_nat (- m) <= Z.to_nat (Z.abs D))%nat)
        by (apply Z2Nat.inj_le; [ lia | apply Z.abs_nonneg | exact Hb ]).
      lia.
Qed.

(* ===================================================================== *)
(*  ★★★ THE DEGREE-UNIFORM DECISION PROCEDURE                              *)
(* ===================================================================== *)

(** The running degree-(k+1) perfect-power sort: search the bounded candidates. *)
Definition is_kth_power (k : nat) (D : Z) : bool :=
  existsb (fun m => Z.eqb (zpow m k) D) (root_cands D).

Lemma is_kth_power_correct : forall (k : nat) (D : Z),
  is_kth_power (S k) D = true <-> exists m : Z, zpow m (S k) = D.
Proof.
  intros k D. unfold is_kth_power. rewrite existsb_exists. split.
  - intros [m [_ Hm]]. exists m. apply Z.eqb_eq. exact Hm.
  - intros [m Hm]. exists m. split.
    + apply In_root_cands. apply (root_abs_bound m k D). exact Hm.
    + apply Z.eqb_eq. exact Hm.
Qed.

(** ★★★ At EVERY degree k+1, the integer Element/role-limit sort is a constructive total decider, 0 axioms. *)
Lemma decide_perfect_power : forall (k : nat) (D : Z),
  {exists m : Z, zpow m (S k) = D} + {~ exists m : Z, zpow m (S k) = D}.
Proof.
  intros k D. destruct (is_kth_power (S k) D) eqn:E.
  - left. apply is_kth_power_correct. exact E.
  - right. intro H. apply is_kth_power_correct in H. rewrite H in E. discriminate.
Qed.

(** ★★ Hence the LEM-instance is a THEOREM at every degree (0-axiom). *)
Lemma perfect_power_or_not : forall (k : nat) (D : Z),
  (exists m : Z, zpow m (S k) = D) \/ ~ (exists m : Z, zpow m (S k) = D).
Proof. intros k D. destruct (decide_perfect_power k D) as [H | H]; [ left | right ]; exact H. Qed.

(* ===================================================================== *)
(*  The running sort, degree-uniform (vm_compute on the atlas numbers)     *)
(* ===================================================================== *)

(** Degree 2 (k=1): 36 = 6² Element ; 5 role-limit. *)
Example pp_sq_36 : is_kth_power 2 36 = true.
Proof. vm_compute. reflexivity. Qed.

Example pp_sq_5 : is_kth_power 2 5 = false.
Proof. vm_compute. reflexivity. Qed.

(** Degree 3 (k=2): 8 = 2³ Element ; 2 role-limit (Delian) ; −8 = (−2)³ Element (sign handled). *)
Example pp_cube_8 : is_kth_power 3 8 = true.
Proof. vm_compute. reflexivity. Qed.

Example pp_cube_2 : is_kth_power 3 2 = false.
Proof. vm_compute. reflexivity. Qed.

Example pp_cube_neg8 : is_kth_power 3 (-8) = true.
Proof. vm_compute. reflexivity. Qed.

(** Degree 4 (k=3): 16 = 2⁴ Element ; 5 role-limit — a NEW degree beyond 2,3. *)
Example pp_quart_16 : is_kth_power 4 16 = true.
Proof. vm_compute. reflexivity. Qed.

Example pp_quart_5 : is_kth_power 4 5 = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** H1's constructive half, DEGREE-UNIFORM:
      (decidable)  at EVERY degree k+1 the integer perfect-power sort is a constructive total decider;
      (LEM = thm)  hence `(∃m, mᵏ⁺¹=D) ∨ ¬(…)` is a THEOREM at every degree, 0-axiom;
      (runs)       the sort executes: deg 2 (36 Element, 5 role-limit), deg 3 (8, −8 Element; 2 role-limit),
                   deg 4 (16 Element, 5 role-limit) — each by `vm_compute`.
    So the Element side is constructively decidable degree-uniformly — the H8 degree-stratification realized
    not tier-by-tier but at all degrees at once.  Honest: this is the INTEGER level for all k; the ℚ-level
    link is established at k=2,3 (GeneralSqrt/GeneralCbrt bridges), and the general-k ℚ-bridge is the
    mechanical lift of GeneralRoot's `perfect_kth_power_criterion`. *)
Theorem H1_degree_uniform_decidable :
  (forall (k : nat) (D : Z), (exists m : Z, zpow m (S k) = D) \/ ~ (exists m : Z, zpow m (S k) = D))
  /\ is_kth_power 2 36 = true
  /\ is_kth_power 2 5 = false
  /\ is_kth_power 3 8 = true
  /\ is_kth_power 3 2 = false
  /\ is_kth_power 4 16 = true.
Proof.
  split. exact perfect_power_or_not.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  split. vm_compute; reflexivity.
  vm_compute; reflexivity.
Qed.
