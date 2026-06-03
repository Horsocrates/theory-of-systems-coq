(** * ConstructiblePolygons.v — the Element-side of constructibility: the regular
      PENTAGON is constructible (2cos72° is a quadratic surd in ℚ[√5], degree 2)
      while the HEPTAGON is not (2cos(2π/7) is a cubic irrational, degree 3).  The
      constructibility boundary for regular n-gons runs at the H8 degree tier,
      between n=5 and n=7.

    Elements: the rational coordinates (−½, ½) of ℚ[√5]; the rational 5; the degree
              (2 for the pentagon, 3 for the heptagon) (L1 + P4)
    Roles:    2cos72° = the DEGREE-2 role-limit (a quadratic surd in ℚ[√5] = the
              constructible Element-side of ruler-and-compass) vs 2cos(2π/7) = the
              DEGREE-3 role-limit (not a power of 2, not constructible); the pentagon
              (n=5) vs the heptagon (n=7) = constructible vs not
    Rules:    the minimal polynomials x²+x−1 (pentagon) and y³+y²−2y−1 (heptagon);
              ℚ[√5] arithmetic; (2x+1)²=5; constructible ⟺ degree a power of 2

    THE DEEP POINT — the H8 degree tier DOES WORK: it determines which regular
    polygons are constructible.  The Greek triad (`AngleTrisection.v`) showed three
    DEGREE-3 role-limits that are NOT constructible.  Here is the complementary
    Element-side: the regular pentagon IS constructible, because 2cos72° = (√5−1)/2
    is a DEGREE-2 surd — it lives in ℚ[√5] (`pentagon_in_Qsqrt5`: it satisfies
    x²+x−1=0 there; `pentagon_eq_half`: 2·(2cos72°)+1 = √5, so it is exactly
    (√5−1)/2).  Degree 2 = 2¹ is a power of 2, so ruler and compass (which adjoin one
    square root at a time) reach it.  The heptagon's 2cos(2π/7) is degree 3
    (`heptagon_no_rational`), not a power of 2, so the 7-gon is NOT constructible.
    The boundary runs between n=5 (yes) and n=7 (no) — exactly the degree-2/degree-3
    tier boundary of H8.

    A nuance on √5: the SAME √5 that forbids the order-5 / icosahedral RATIONAL
    rotation (④, `CrystallographicRestriction.v`) and is the golden process
    (`GoldenFibonacci.v`) appears here at DEGREE 2.  It blocks the order-5 rotation
    over ℚ (its matrix entry cos72° is irrational), yet the pentagon is still
    constructible because √5 is reachable by a single quadratic step.  Role-limit
    over ℚ, Element-reachable by degree-2 construction.

    ============ E/R/R разбор ============
      Rules (L5): мин. многочлены x²+x−1 (пентагон), y³+y²−2y−1 (гептагон); ℚ[√5];
                  (2x+1)²=5; построимо ⟺ степень 2ᵏ.
      Roles (L4): 2cos72° = role-limit степени 2 (в ℚ[√5] = построимая Element-сторона)
                  vs 2cos(2π/7) = role-limit степени 3 (не построим); пентагон vs гептагон.
      Elements  : координаты ℚ[√5] (−½,½); рац. 5; степень 2 vs 3 (L1+P4).
    ДИАГНОСТИКА (P4): граница построимости n-угольников = ТИР степени (H8): n=5 (степень 2,
    в ℚ[√5]) построим vs n=7 (степень 3) нет. Та же √5 (④/φ), здесь степени 2: блокирует
    рациональный поворот порядка 5, но достижима построением степени 2.

    STATUS: 5 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lia ZArith Lqa.
From ToS Require Import analysis.Sqrt5Irrational.
From ToS Require Import stdlib.AngleTrisection.

Open Scope Q_scope.

(* ===================================================================== *)
(*  ℚ[√5] = (a, b) meaning a + b√5  (multiplication uses (√5)² = 5)        *)
(* ===================================================================== *)

Definition RQ : Type := (Q * Q)%type.
Definition radd (z w : RQ) : RQ := (fst z + fst w, snd z + snd w).
Definition rmul (z w : RQ) : RQ :=
  (fst z * fst w + 5 * (snd z * snd w), fst z * snd w + snd z * fst w).
Definition rneg (z : RQ) : RQ := (- fst z, - snd z).
Definition req (z w : RQ) : Prop := fst z == fst w /\ snd z == snd w.
Definition rsq (z : RQ) : RQ := rmul z z.

Definition r0 : RQ := (0, 0).
Definition r1 : RQ := (1, 0).
Definition r5 : RQ := (0, 1).             (* the adjoined √5 *)
Definition g5 : RQ := (-(1#2), 1#2).      (* (√5−1)/2 = 2cos72° *)

(** √5 is named in ℚ[√5]: (0,1)² = 5. *)
Lemma sqrt5_named : req (rsq r5) (5, 0).
Proof. vm_compute. split; reflexivity. Qed.

(* ===================================================================== *)
(*  The pentagon: 2cos72° = (√5−1)/2 is a DEGREE-2 surd in ℚ[√5]          *)
(* ===================================================================== *)

(** ★ 2cos72° lives in ℚ[√5]: g5 satisfies x²+x−1 = 0 there — a quadratic surd,
    hence the regular pentagon is constructible by ruler and compass. *)
Lemma pentagon_in_Qsqrt5 :
  req (radd (radd (rsq g5) g5) (rneg r1)) r0.
Proof. vm_compute. split; reflexivity. Qed.

(** g5 is exactly (√5−1)/2: 2·g5 + 1 = √5 (the generator). *)
Lemma pentagon_eq_half :
  req (radd (radd g5 g5) r1) r5.
Proof. vm_compute. split; reflexivity. Qed.

(** 2cos72° is irrational — but a QUADRATIC irrational: x²+x−1=0 ⟹ (2x+1)²=5,
    which has no rational root (via √5).  Quadratic ⟹ still constructible. *)
Theorem pentagon_no_rational : ~ (exists q : Q, q * q + q - 1 == 0).
Proof.
  intros [q Hq]. apply sqrt5_not_in_Q. exists (2 * q + 1).
  assert (H : (2 * q + 1) * (2 * q + 1) == 4 * (q * q + q - 1) + 5) by ring.
  rewrite H, Hq. ring.
Qed.

(* ===================================================================== *)
(*  Synthesis: the constructibility boundary runs at the degree tier      *)
(* ===================================================================== *)

(** Which regular n-gons are constructible, by the H8 degree tier:
      (a) the PENTAGON (n=5): 2cos72° satisfies x²+x−1=0 in ℚ[√5] — a degree-2
          surd, exactly (√5−1)/2 — CONSTRUCTIBLE (degree 2 = 2¹);
      (b) it is irrational (quadratic, not rational) — but degree 2, so still
          reachable by one square-root step;
      (c) the HEPTAGON (n=7): 2cos(2π/7) is a root of y³+y²−2y−1 with NO rational
          root — a degree-3 irrational, NOT constructible (3 not a power of 2). *)
Theorem constructible_polygons_synthesis :
  req (radd (radd (rsq g5) g5) (rneg r1)) r0
  /\ req (radd (radd g5 g5) r1) r5
  /\ ~ (exists q : Q, q * q + q - 1 == 0)
  /\ ~ (exists q : Q, q * q * q == - (q * q) + 2 * q + 1).
Proof.
  split; [ exact pentagon_in_Qsqrt5 | ].
  split; [ exact pentagon_eq_half | ].
  split; [ exact pentagon_no_rational | exact heptagon_no_rational ].
Qed.
