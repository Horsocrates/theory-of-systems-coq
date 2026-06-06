(** * DiscriminantCompleteEigenvalue.v — atlas exhaustion: the discriminant is the COMPLETE (and, with H37,
       DECIDABLE) invariant for rational eigenvalues of a 2×2.  The reduction atlas compressed everything to
       the master valve "Δ = tr²−4det a perfect square?"; H37 made that valve a constructive decider.  This
       proves the valve is also COMPLETE: a 2×2 has a RATIONAL EIGENVALUE iff Δ is a perfect (rational)
       square — a biconditional by completing the square (pure ℚ algebra).  Combined with H37, the question
       "does this integer 2×2 have a rational eigenvalue?" is a DECISION THEOREM (run is_element_b on Δ).

    -- The completeness biconditional (over ℚ) --
      char poly of [[a,b],[c,d]] is x² − t·x + e with t = a+d (trace), e = ad−bc (det).
      x is a rational eigenvalue  ⟺  Δ = t²−4e is a rational square:
        (⟹)  if x²−tx+e=0 then (2x−t)² = 4(x²−tx+e) + (t²−4e) = t²−4e = Δ  — Δ is the square (2x−t)²;
        (⟸)  if s²=Δ then x = (t+s)/2 is a root: 4(x²−tx+e) = s²−Δ = 0.
      Both directions are pure ℚ algebra (ring), no continuum.

    -- With H37: decidable --
      For an INTEGER matrix Δ = t²−4e is an integer, and "∃s:ℚ, s²=Δ" is `ElementZ Δ`, decided 0-axiom by
      `decide_elementZ` (H37).  So `has_rat_eig` of an integer 2×2 is decidable — the valve is complete AND
      decidable.

    WHAT THE REPO HAS (surveyed): ReductionAtlasSynthesis `eigenvalue_forces_square_disc` (the ⟹ direction,
    one matrix); H1ConstructivityDecidable (ElementZ, decide_elementZ, rolelimit_5).  GAP: the full
    biconditional (both directions, general t,e) packaged as "Δ is the COMPLETE eigenvalue invariant", and
    its combination with the H37 decider into a rational-eigenvalue decision theorem.  This adds it.

    ============ E/R/R разбор ============
      Elements : 2×2 через (tr t, det e); харполином x²−tx+e; дискриминант Δ=t²−4e.
      Roles    : рациональное собств. значение = реализация корня в ℚ; Δ-квадрат = мастер-вентиль атласа.
      Rules    : x собств. ⟺ Δ=(2x−t)² полный квадрат (completing the square, чистая ℚ-алгебра); целая матрица ⟹ разрешимо (H37).
      ДИАГНОСТИКА (P4): Δ-вентиль ПОЛОН (биусловие рациональное-собств-значение ⟺ Δ-квадрат) И РАЗРЕШИМ (H37) ⟹
      вопрос про рациональное собств. значение целой 2×2 — решающая теорема; атлас исчерпан (один инвариант Δ полон
      и вычислим). ЧЕСТНО: 2×2 (вентиль атласа); общие n×n — дальше. Уровень: `синтез`.

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (builds on foundation.H1ConstructivityDecidable)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.H1ConstructivityDecidable.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Characteristic polynomial, rational eigenvalue, discriminant (over ℚ)  *)
(* ===================================================================== *)

Definition charval (t e x : Q) : Q := x * x - t * x + e.
Definition has_rat_eig (t e : Q) : Prop := exists x : Q, charval t e x == 0.
Definition discQ (t e : Q) : Q := t * t - 4 * e.
Definition disc_is_square_Q (t e : Q) : Prop := exists s : Q, s * s == discQ t e.

(* ===================================================================== *)
(*  ★★ THE COMPLETENESS BICONDITIONAL (completing the square)              *)
(* ===================================================================== *)

(** ⟹ a rational eigenvalue forces Δ to be a perfect square: Δ = (2x − t)². *)
Lemma eig_to_square : forall t e : Q, has_rat_eig t e -> disc_is_square_Q t e.
Proof.
  intros t e [x Hx]. exists (2 * x - t). unfold discQ. unfold charval in Hx.
  assert (Hid : (2 * x - t) * (2 * x - t) == 4 * (x * x - t * x + e) + (t * t - 4 * e)) by ring.
  rewrite Hid, Hx. ring.
Qed.

(** ⟸ a square discriminant yields the rational eigenvalue x = (t + s)/2. *)
Lemma square_to_eig : forall t e : Q, disc_is_square_Q t e -> has_rat_eig t e.
Proof.
  intros t e [s Hs]. exists ((t + s) * (1 # 2)). unfold charval. unfold discQ in Hs.
  assert (Hid : ((t + s) * (1 # 2)) * ((t + s) * (1 # 2)) - t * ((t + s) * (1 # 2)) + e
                == (1 # 4) * (s * s - (t * t - 4 * e))) by ring.
  rewrite Hid, Hs. ring.
Qed.

(** ★★ The discriminant is the COMPLETE invariant: rational eigenvalue ⟺ Δ a rational square. *)
Theorem rational_eigenvalue_iff_disc_square : forall t e : Q,
  has_rat_eig t e <-> disc_is_square_Q t e.
Proof. intros t e. split; [ apply eig_to_square | apply square_to_eig ]. Qed.

(* ===================================================================== *)
(*  With H37: rational eigenvalues of an INTEGER 2×2 are DECIDABLE          *)
(* ===================================================================== *)

(** The ℚ-discriminant of an integer matrix is inject_Z of the integer discriminant. *)
Lemma disc_bridge : forall t e : Z,
  discQ (inject_Z t) (inject_Z e) == inject_Z (t * t - 4 * e).
Proof.
  intros t e. unfold discQ, inject_Z, Qeq, Qminus, Qmult, Qplus, Qopp. simpl. ring.
Qed.

(** ★ Hence: whether an integer 2×2 (trace t, det e) has a rational eigenvalue is DECIDABLE (run the H37
    decider on Δ = t²−4e) — the master valve is complete AND decidable. *)
Lemma decide_rational_eigenvalue_Z : forall t e : Z,
  {has_rat_eig (inject_Z t) (inject_Z e)} + {~ has_rat_eig (inject_Z t) (inject_Z e)}.
Proof.
  intros t e. destruct (decide_elementZ (t * t - 4 * e)) as [HE | HR].
  - left. apply square_to_eig. destruct HE as [r Hr]. exists r.
    rewrite Hr. symmetry. apply disc_bridge.
  - right. intro Heig. apply HR. apply eig_to_square in Heig.
    destruct Heig as [s Hs]. exists s. rewrite Hs. apply disc_bridge.
Qed.

(* ===================================================================== *)
(*  Concrete: the atlas matrices, sorted by the complete invariant         *)
(* ===================================================================== *)

(** Element: the 3-4-5 boost [[5,3],[3,5]] (t=10, e=16, Δ=36) HAS the rational eigenvalue 8. *)
Example boost345_has_eig : has_rat_eig (inject_Z 10) (inject_Z 16).
Proof. exists (inject_Z 8). unfold charval. vm_compute. reflexivity. Qed.

(** role-limit: the Fibonacci matrix [[1,1],[1,0]] (t=1, e=−1, Δ=5) has NO rational eigenvalue (√5). *)
Example fibonacci_no_eig : ~ has_rat_eig (inject_Z 1) (inject_Z (-1)).
Proof.
  rewrite rational_eigenvalue_iff_disc_square. intros [s Hs].
  assert (Hd : discQ (inject_Z 1) (inject_Z (-1)) == inject_Z 5) by (vm_compute; reflexivity).
  rewrite Hd in Hs. apply rolelimit_5. exists s. exact Hs.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Atlas exhaustion — the discriminant is the COMPLETE and DECIDABLE eigenvalue invariant of a 2×2:
      (complete)   has_rat_eig t e ⟺ Δ is a rational square (both directions, by completing the square);
      (decidable)  for an integer matrix, has_rat_eig is decidable (H37 decider on Δ);
      (Element)    the 3-4-5 boost (Δ=36) has the rational eigenvalue 8;
      (role-limit) the Fibonacci matrix (Δ=5) has none (√5).
    So the reduction atlas's master valve is not only decidable (H37) but COMPLETE: one invariant Δ both
    classifies (rational eigenvalue ⟺ square) and is computable.  Honest: 2×2 (the atlas valve); general
    n×n is the next frontier. *)
Theorem discriminant_complete_eigenvalue :
  (forall t e : Q, has_rat_eig t e <-> disc_is_square_Q t e)
  /\ (forall t e : Z, discQ (inject_Z t) (inject_Z e) == inject_Z (t * t - 4 * e))
  /\ has_rat_eig (inject_Z 10) (inject_Z 16)
  /\ ~ has_rat_eig (inject_Z 1) (inject_Z (-1)).
Proof.
  split. exact rational_eigenvalue_iff_disc_square.
  split. exact disc_bridge.
  split. exact boost345_has_eig.
  exact fibonacci_no_eig.
Qed.
