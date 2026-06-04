(** * HeliumBoundary.v — why hydrogen is EXACT and helium is NOT: the A<->B bridge.

    The strongest cross-link found in the Part-B audit, made machine-checkable.  It applies the
    Part-A flagship criterion (ThreeFormulaBoundary.spectrum_element_iff_square_disc) to the two
    simplest atoms and recovers a textbook fact: hydrogen's spectrum is Element (exact rational),
    helium's correlation energy is role-limit (irrational, needs approximation).

    THE DIAL is the off-diagonal (electron-electron) coupling H12:
      * H12 = 0  (no coupling, hydrogen-like): disc = (H11 - H22)^2 is ALWAYS a perfect square
        (diagonal_spectrum_element) -> ELEMENT -> the spectrum is exact rational.
      * H12 != 0 (real e-e coupling, helium CI): disc can leave the perfect squares.  For the He
        CI matrix the discriminant is exactly 117/65536, and 117 = 9*13 is NOT a perfect square,
        so the eigenvalues lie in Q(sqrt 13) -> ROLE-LIMIT -> the correlation energy is not exact
        rational, hence the variational / CI approximation.

    So "hydrogen exact, helium approximate" is not an accident of technique: it is the
    finitization boundary (Part A) on the atomic spectrum, dialed by the e-e coupling.  The
    role-limit verdict is completed by the cited surd fact "117 is not a perfect square"
    (= sqrt 13 not in Q; GeneralSqrt.v / Sqrt thread, atlas page I), taken here as a hypothesis.

    He CI entries replicated from src/stdlib/qphysics/HeCIMatrix.v (H11=-729/256, H22=-45/16,
    H12=H21=-3/256) — replicated locally per the project's stale-.vo policy, with this citation.

    Elements: the hydrogen-like diagonal matrix; the helium CI matrix; the numbers (disc 117/65536)
    Roles:    the exactness status — Element (exact) vs role-limit (approximate) — set by the disc
    Rules:    spectrum Element iff disc a perfect square; H12 (e-e coupling) is the dial

    ============ E/R/R разбор ============
      Rules (L5): спектр CI-гамильтониана Element ⟺ disc полный квадрат; связь H12 — ручка
                  (H12=0 ⟹ disc=(H11−H22)² квадрат ⟹ точно; H12≠0 ⟹ может уйти ⟹ role-limit).
      Roles (L4): слот «статус точности» (точно/аппроксимация) по вердикту дискриминанта.
      Elements  : водородоподобная диагональ (Element); CI-матрица He (role-limit, disc 117/65536).
    ДИАГНОСТИКА (P4): «H точен, He нет» = граница финитизации на спектре, крутится e-e-связью;
    корреляция He = √13-иррациональна (role-limit) ⟹ аппроксимация; критерий флагмана A на атомах.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
From ToS Require Import foundation.ThreeFormulaMethod.
From ToS Require Import foundation.ThreeFormulaBoundary.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Hydrogen side: NO coupling (H12 = 0) -> Element (exact)                 *)
(* ===================================================================== *)

(** ★ A diagonal rule (no off-diagonal coupling) always has a perfect-square discriminant:
    disc = (a11 - a22)^2.  No electron-electron coupling => Element => exact rational spectrum. *)
Lemma diagonal_spectrum_element (M : Mat2) :
  a12 M == 0 -> a21 M == 0 -> is_square (disc M).
Proof.
  intros H12 H21. exists (a11 M - a22 M).
  unfold disc, tr, det. rewrite H12, H21. ring.
Qed.

(** Hydrogen-like: diagonal E_1 = -1/2, E_2 = -1/8, no coupling -> Element (exact). *)
Definition hydrogenlike : Mat2 := mk2 (- (1 # 2)) 0 0 (- (1 # 8)).

Lemma hydrogenlike_element : is_square (disc hydrogenlike).
Proof. apply diagonal_spectrum_element; reflexivity. Qed.

(* ===================================================================== *)
(*  Helium side: real coupling (H12 != 0) -> disc 117/65536 -> role-limit  *)
(* ===================================================================== *)

(** The helium CI 2x2 matrix (entries from HeCIMatrix.v). *)
Definition heCI : Mat2 := mk2 (- (729 # 256)) (- (3 # 256)) (- (3 # 256)) (- (45 # 16)).

(** ★ its discriminant is exactly 117/65536. *)
Lemma heCI_disc : disc heCI == 117 # 65536.
Proof. vm_compute. reflexivity. Qed.

(** the He spectrum has a rational eigenvalue iff 117/65536 is a perfect square. *)
Lemma heCI_eigenvalue_iff_square :
  (exists x, char_poly heCI x == 0) <-> is_square (117 # 65536).
Proof.
  rewrite (spectrum_element_iff_square_disc heCI).
  unfold is_square. split; intros [r Hr]; exists r.
  - rewrite <- heCI_disc. exact Hr.
  - rewrite heCI_disc. exact Hr.
Qed.

(** the denominator 65536 = 256^2 is a square, so squareness reduces to the numerator 117. *)
Lemma he_square_iff_117 :
  is_square (117 # 65536) <-> is_square (117 # 1).
Proof.
  unfold is_square. split; intros [r Hr].
  - exists (256 * r).
    assert (Hsq : (256 * r) * (256 * r) == 65536 * (r * r)) by ring.
    rewrite Hsq, <- Hr. vm_compute. reflexivity.
  - exists (r * (1 # 256)).
    assert (Hsq : (r * (1 # 256)) * (r * (1 # 256)) == (r * r) * (1 # 65536)) by ring.
    rewrite Hsq, <- Hr. vm_compute. reflexivity.
Qed.

(** ★ THE VERDICT: given that 117 is not a perfect square (sqrt 13 not in Q — atlas page I),
    the helium spectrum has NO rational eigenvalue: its correlation energy is role-limit. *)
Lemma helium_role_limit :
  ~ is_square (117 # 1) -> ~ (exists x, char_poly heCI x == 0).
Proof.
  intros Hns Hex. apply Hns.
  apply (proj1 he_square_iff_117).
  apply (proj1 heCI_eigenvalue_iff_square).
  exact Hex.
Qed.

(* ===================================================================== *)
(*  Capstone: hydrogen exact vs helium approximate, one criterion          *)
(* ===================================================================== *)

(** The bridge:
      (no coupling)  a diagonal rule has a perfect-square discriminant -> Element/exact
                     (hydrogen: no e-e coupling);
      (He coupling)  the He CI matrix has disc 117/65536;
      (He verdict)   the He spectrum is Element iff 117 is a perfect square — i.e. role-limit
                     (since 117 = 9*13 is not, sqrt 13 not in Q), hence approximation.
    "Hydrogen exact, helium approximate" = the finitization boundary on the atomic spectrum,
    dialed by the electron-electron coupling H12. *)
Theorem helium_vs_hydrogen_boundary :
  (forall M, a12 M == 0 -> a21 M == 0 -> is_square (disc M))
  /\ disc heCI == 117 # 65536
  /\ ((exists x, char_poly heCI x == 0) <-> is_square (117 # 1)).
Proof.
  split; [ exact diagonal_spectrum_element | ].
  split; [ exact heCI_disc | ].
  rewrite heCI_eigenvalue_iff_square. exact he_square_iff_117.
Qed.
