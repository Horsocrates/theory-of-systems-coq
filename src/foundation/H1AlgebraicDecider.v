(** * H1AlgebraicDecider.v — the FULL decision procedure behind H1AlgebraicElement.v: a computable boolean
       that decides whether an integer polynomial has a rational root, with PROVEN soundness AND completeness,
       packaged as a Sumbool {AlgElement} + {~AlgElement}.  H1AlgebraicElement gave the criterion (a | a₀,
       b | aₙ) and decided two concrete polynomials by hand; this turns the criterion into an actual algorithm
       and proves it correct, making "Element-ness is DECIDABLE for every algebraic number" rigorous.

    -- The decider --
      The criterion confines a rational root a/b (lowest terms) to the FINITE divisor box
        a ∈ [−|a₀|, |a₀|]   (a | a₀),     b ∈ [1, |aₙ|]   (b | aₙ, b > 0).
      So enumerate that box and test each candidate:
        decideb cs a₀ aₙ = ∃ (a,b) in the box with gcd(a,b)=1 and phom cs a b = 0.
      SOUNDNESS: decideb = true ⟹ a genuine coprime root ⟹ AlgElement (any cs — the box only bounds search).
      COMPLETENESS: a₀ ≠ 0, aₙ ≠ 0, AlgElement ⟹ decideb = true (the lowest-terms root lies in the box, by
      the criterion).  Hence  decide_alg_element : {AlgElement} + {~AlgElement}  — a real decision procedure.

    -- The H1 reading --
      "Is the algebraic number presented by this integer polynomial an ELEMENT (has a rational value)?" is now
      ALGORITHMICALLY decided — the finitization boundary made effective for the whole algebraic class, the
      natural endpoint of the reduction atlas (perfect-square dial → perfect k-th power → eigenvalue → general
      rational root → THIS computable decider).  Demonstrated: decideb runs to `true` on 2x²+x−1 (root 1/2)
      and to `false` on 2x²−1 (√(1/2) a role-limit).

    WHAT THE REPO HAS (surveyed): foundation.H1AlgebraicElement (phom, rat_root, AlgElement, the criterion,
    by-hand decisions); H1GeneralDegreeConstructivity / H1RationalDegreeUniform (the per-k radical deciders,
    the existsb-over-bounded-search pattern reused here).  GAP: the general polynomial DECIDER (enumerate the
    divisor box + soundness/completeness + the Sumbool).  This adds it.

    ============ E/R/R разбор ============
      Elements : конечный бокс кандидатов (a∈[−|a₀|,|a₀|], b∈[1,|aₙ|]); булев existsb-тест (gcd=1 ∧ phom=0).
      Roles    : decideb = роль-решатель; soundness/completeness = его корректность; Sumbool = разрешимость как объект.
      Rules    : критерий (a∣a₀,b∣aₙ) запирает корень в бокс ⟹ перечислить+проверить ⟹ {Element}+{¬} разрешимо.
      ДИАГНОСТИКА (P4): Element-ность алгебр. числа — РАЗРЕШИМА алгоритмически (не только критерий): конечный бокс делителей,
      булев тест, доказанные soundness+completeness, вычисляющийся Sumbool. Финитизационная граница сделана эффективной.
      Уровень: `синтез` (алгоритмизация критерия H41 + доказанная корректность; existsh-над-боксом паттерн из H1*-файлов).

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (builds on foundation.H1AlgebraicElement)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import ZArith Znumtheory Lia List Bool.
From ToS Require Import foundation.H1AlgebraicElement.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(*  Integer ranges and their membership                                    *)
(* ===================================================================== *)

(** [zseq lo n] = [lo, lo+1, …, lo+(n−1)] as integers. *)
Definition zseq (lo : Z) (n : nat) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 n).

Lemma in_zseq_lower : forall lo n x, In x (zseq lo n) -> lo <= x.
Proof.
  intros lo n x H. unfold zseq in H. apply in_map_iff in H.
  destruct H as [k [Hk _]]. subst x. lia.
Qed.

Lemma in_zseq : forall (lo : Z) (n : nat) (x : Z),
  lo <= x -> x < lo + Z.of_nat n -> In x (zseq lo n).
Proof.
  intros lo n x Hlo Hhi. unfold zseq. apply in_map_iff.
  exists (Z.to_nat (x - lo)). split.
  - rewrite Z2Nat.id by lia. ring.
  - apply in_seq. rewrite Nat.add_0_l. split; [ lia | ].
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia.
Qed.

(** |a| ≤ |c| whenever a divides a nonzero c. *)
Lemma divide_abs_le : forall a c, c <> 0 -> (a | c) -> Z.abs a <= Z.abs c.
Proof.
  intros a c Hc Hdiv. apply Z.divide_pos_le.
  - lia.
  - apply Z.divide_abs_l. apply Z.divide_abs_r. exact Hdiv.
Qed.

(* ===================================================================== *)
(*  rel_prime ↔ Z.gcd = 1 (boolean bridge)                                 *)
(* ===================================================================== *)

Lemma gcd1_rp : forall a b, Z.gcd a b = 1 -> rel_prime a b.
Proof. intros a b H. rewrite <- Zgcd_1_rel_prime. exact H. Qed.

Lemma rp_gcd1 : forall a b, rel_prime a b -> Z.gcd a b = 1.
Proof. intros a b H. rewrite Zgcd_1_rel_prime. exact H. Qed.

(* ===================================================================== *)
(*  The decider                                                            *)
(* ===================================================================== *)

(** The finite candidate box: numerators in [−|a₀|, |a₀|], denominators in [1, |aₙ|]. *)
Definition root_candidates (a0 an : Z) : list (Z * Z) :=
  list_prod (zseq (- Z.abs a0) (Z.to_nat (2 * Z.abs a0 + 1)))
            (zseq 1 (Z.to_nat (Z.abs an))).

(** ★ The decision boolean: does some coprime candidate in the box annihilate phom? *)
Definition decideb (cs : list Z) (a0 an : Z) : bool :=
  existsb (fun ab : Z * Z =>
             andb (Z.gcd (fst ab) (snd ab) =? 1) (phom cs (fst ab) (snd ab) =? 0))
          (root_candidates a0 an).

(* ===================================================================== *)
(*  Soundness and completeness                                             *)
(* ===================================================================== *)

(** ★★ SOUND: if the decider fires, the polynomial really has a rational root (a coprime candidate in the box
    with positive denominator annihilating phom is a genuine lowest-terms root). *)
Lemma decideb_sound : forall cs a0 an, decideb cs a0 an = true -> AlgElement cs.
Proof.
  intros cs a0 an H. unfold decideb in H.
  apply existsb_exists in H. destruct H as [[a b] [Hin Hf]].
  apply andb_true_iff in Hf. destruct Hf as [Hg Hp]. simpl in Hg, Hp.
  apply in_prod_iff in Hin. destruct Hin as [_ Hinb].
  apply in_zseq_lower in Hinb.
  exists a, b. unfold rat_root. split; [ lia | split ].
  - apply gcd1_rp. apply Z.eqb_eq. exact Hg.
  - apply Z.eqb_eq. exact Hp.
Qed.

(** ★★ COMPLETE: if the polynomial a₀ :: mid ++ [aₙ] (a₀ ≠ 0, aₙ ≠ 0) has a rational root, the decider fires —
    the lowest-terms root lies in the divisor box (criterion) and passes the coprime / phom test. *)
Lemma decideb_complete : forall a0 mid an,
  a0 <> 0 -> an <> 0 ->
  AlgElement (a0 :: (mid ++ [an])) -> decideb (a0 :: (mid ++ [an])) a0 an = true.
Proof.
  intros a0 mid an Ha0 Han [a [b Hr]].
  destruct (rational_root_criterion a0 mid an a b Hr) as [Hpa Hqan].
  destruct Hr as [Hbpos [Hrp Hroot]].
  assert (Hla : Z.abs a <= Z.abs a0) by (apply (divide_abs_le a a0 Ha0 Hpa)).
  assert (Hlb : Z.abs b <= Z.abs an) by (apply (divide_abs_le b an Han Hqan)).
  unfold decideb. apply existsb_exists. exists (a, b). split.
  - apply in_prod_iff. split.
    + apply in_zseq.
      * lia.
      * rewrite Z2Nat.id by lia. lia.
    + apply in_zseq.
      * lia.
      * rewrite Z2Nat.id by lia. lia.
  - simpl. apply andb_true_iff. split.
    + apply Z.eqb_eq. apply rp_gcd1. exact Hrp.
    + apply Z.eqb_eq. exact Hroot.
Qed.

(* ===================================================================== *)
(*  The Sumbool decision procedure                                         *)
(* ===================================================================== *)

(** ★★ A genuine DECISION PROCEDURE: for a₀ ≠ 0, aₙ ≠ 0, decide whether the algebraic number presented by
    a₀ :: mid ++ [aₙ] is an Element (has a rational root) — Element-ness made algorithmic. *)
Definition decide_alg_element (a0 : Z) (mid : list Z) (an : Z)
  (Ha0 : a0 <> 0) (Han : an <> 0) :
  {AlgElement (a0 :: (mid ++ [an]))} + {~ AlgElement (a0 :: (mid ++ [an]))}.
Proof.
  destruct (decideb (a0 :: (mid ++ [an])) a0 an) eqn:Hd.
  - left. apply (decideb_sound _ a0 an). exact Hd.
  - right. intro Hae.
    pose proof (decideb_complete a0 mid an Ha0 Han Hae) as Htrue.
    rewrite Hd in Htrue. discriminate.
Defined.

(* ===================================================================== *)
(*  The decider RUNS                                                       *)
(* ===================================================================== *)

(** ★ ELEMENT decided positively: 2x² + x − 1 has the rational root 1/2 — decideb computes to true. *)
Example decideb_quad_true : decideb [-1; 1; 2] (-1) 2 = true.
Proof. vm_compute. reflexivity. Qed.

(** ★ ROLE-LIMIT decided negatively: 2x² − 1 has no rational root — decideb computes to false (√(1/2) irrational). *)
Example decideb_sqrt_half_false : decideb [-1; 0; 2] (-1) 2 = false.
Proof. vm_compute. reflexivity. Qed.

(** ★ A higher-degree run: 2x³ − x − 1 = (x−1)(2x²+2x+1) has the rational root 1 — decideb true. *)
Example decideb_cubic_true : decideb [-1; -1; 0; 2] (-1) 2 = true.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The decidable finitization boundary, made ALGORITHMIC for all algebraic numbers:
      (sound)      decideb = true ⟹ the polynomial has a rational root (AlgElement);
      (complete)   a₀,aₙ ≠ 0 and AlgElement ⟹ decideb = true (the root is in the divisor box);
      (decision)   decide_alg_element : {AlgElement} + {~AlgElement} — a real decision procedure;
      (runs)       true on 2x²+x−1 (root 1/2), false on 2x²−1 (√(1/2) a role-limit).
    So "is this algebraic number an Element?" is not merely DECIDABLE in principle (the criterion) but
    EFFECTIVELY computed — the finitization boundary as an algorithm, the endpoint of the reduction atlas.
    Level: synthesis — algorithmising the H41 criterion with proven soundness/completeness. *)
Theorem h1_algebraic_decider :
  (forall cs a0 an, decideb cs a0 an = true -> AlgElement cs)
  /\ (forall a0 mid an, a0 <> 0 -> an <> 0 ->
        AlgElement (a0 :: (mid ++ [an])) -> decideb (a0 :: (mid ++ [an])) a0 an = true)
  /\ decideb [-1; 1; 2] (-1) 2 = true
  /\ decideb [-1; 0; 2] (-1) 2 = false.
Proof.
  split; [ exact decideb_sound | ].
  split; [ exact decideb_complete | ].
  split; [ exact decideb_quad_true | exact decideb_sqrt_half_false ].
Qed.
