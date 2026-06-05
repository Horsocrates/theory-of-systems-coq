(** * DimensionRoleLimit.v — the floor of Q3: the wall (the Hauptvermutung) is itself an instance of H1.
      The dimension recovered from the count (VolumeDimension.v: count = s^D) is EITHER an integer (a clean
      manifold dimension = Element) OR there is NO integer D (the count falls strictly between consecutive
      powers — a FRACTAL dimension = role-limit, no manifold).  So "does the sprinkling converge to a
      manifold?" (the Hauptvermutung) IS the finitization boundary applied to dimension: integer dimension
      = Element/manifold vs fractal dimension = role-limit/no-manifold.

    -- The dichotomy --
      A count c at linear size s has an INTEGER dimension iff c = s^D for some integer D (Element: a clean
      d-dimensional volume, a manifold).  If c falls strictly between consecutive powers s^D < c < s^(D+1),
      there is NO integer dimension — the "dimension" log_s(c) is non-integer (a FRACTAL, a role-limit, like
      the trit log_2(3) of DyadicBits.v): no manifold.
        - 16 at size 2 = 2^4 : integer dimension D=4 (Element / manifold);
        - 5 at size 2 : 2^2 < 5 < 2^3, no integer dimension (role-limit / fractal, no manifold).

    -- The Hauptvermutung as H1 --
      The open question "when does a causal set converge to a continuum manifold?" is exactly "when is the
      count-scaling a clean integer power (Element) rather than a fractal (role-limit)?".  The wall flagged
      Conjectural in VolumeDimension.v is thereby placed ON the project's axis (H1), not left as a bare
      "open" — it asks which side of the finitization boundary the sprinkling's dimension lies on.

    -- HONEST scope --
      This makes the wall an H1 instance and machine-checks the dichotomy on integers (integer power =
      Element, strictly-between-powers = role-limit).  It does NOT resolve the Hauptvermutung (whether a
      given physical sprinkling lands on the Element side) — that remains open; it only reframes it.

    Elements: dim_is_element s c := exists D, s^D = c; 16=2^4 Element; 5 between 2^2,2^3 role-limit
    Roles:    integer dimension = Element/manifold; fractal (between powers) = role-limit/no-manifold
    Rules:    dimension is Element (integer power) or role-limit (fractal); Hauptvermutung = H1(dimension)

    ============ E/R/R разбор ============
      Rules (L5): размерность из счёта (c=s^D) либо ЦЕЛАЯ (есть D: чистое многообразие = Element) либо нет
                  целого D (счёт строго между степенями = фрактал = role-limit, нет многообразия).
                  Hauptvermutung = это правило (сходимость к многообразию <=> целая размерность).
      Roles (L4): целая размерность = Element/многообразие; фрактал (между степенями) = role-limit; зазор
                  s^D..s^(S D) = ничейная земля = граница; Hauptvermutung = H1, приложенная к размерности.
      Elements  : dim_is_element s c := exists D, s^D=c; 16=2^4 Element; 5 между 2^2,2^3 role-limit.
    ДИАГНОСТИКА (P4): стена Q3 (Hauptvermutung) -- инстанс H1: целая размерность = Element/многообразие,
    фрактал = role-limit/нет многообразия.  Открытая гипотеза поставлена на ось проекта (граница финитизации),
    а не "просто открыта".  Связь с DyadicBits (трит log_2(3) = role-limit = фрактальная размерность).
    ЧЕСТНО: переобрамляю стену как H1-инстанс; саму Hauptvermutung не решаю.

    STATUS: 6 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  The dimension dichotomy: integer (Element) vs fractal (role-limit)     *)
(* ===================================================================== *)

(** A count c at linear size s has an INTEGER dimension iff c = s^D for some D — a clean manifold
    dimension (Element). *)
Definition dim_is_element (s c : nat) : Prop := exists D, s ^ D = c.

(** Element / manifold examples: 16 = 2^4 (dimension 4), 8 = 2^3 (dimension 3). *)
Lemma dim_element_16 : dim_is_element 2 16.
Proof. exists 4%nat. reflexivity. Qed.

Lemma dim_element_8 : dim_is_element 2 8.
Proof. exists 3%nat. reflexivity. Qed.

(** ★ A count strictly between consecutive powers has NO integer dimension — a FRACTAL (role-limit): there
    is no manifold.  (s^D < c < s^(D+1) forces the would-be exponent strictly between D and D+1.) *)
Lemma between_powers_role_limit : forall s c D,
  2 <= s -> s ^ D < c -> c < s ^ (S D) -> ~ dim_is_element s c.
Proof.
  intros s c D Hs Hlo Hhi [E HE].
  rewrite <- HE in Hlo. rewrite <- HE in Hhi.
  assert (HDE : D < E).
  { destruct (Nat.le_gt_cases E D) as [H | H]; [ | lia ].
    assert (s ^ E <= s ^ D) by (apply Nat.pow_le_mono_r; [ lia | exact H ]).
    lia. }
  assert (HES : E < S D).
  { destruct (Nat.le_gt_cases (S D) E) as [H | H]; [ | lia ].
    assert (s ^ S D <= s ^ E) by (apply Nat.pow_le_mono_r; [ lia | exact H ]).
    lia. }
  lia.
Qed.

(** Role-limit / fractal examples: 5 and 7 each fall strictly between 2^2 = 4 and 2^3 = 8. *)
Lemma dim_role_limit_5 : ~ dim_is_element 2 5.
Proof. apply (between_powers_role_limit 2 5 2); [ lia | cbn; lia | cbn; lia ]. Qed.

Lemma dim_role_limit_7 : ~ dim_is_element 2 7.
Proof. apply (between_powers_role_limit 2 7 2); [ lia | cbn; lia | cbn; lia ]. Qed.

(* ===================================================================== *)
(*  Capstone: the Hauptvermutung is H1 applied to dimension                *)
(* ===================================================================== *)

(** Q3's wall is an H1 instance:
      (Element)    integer dimensions exist (16 = 2^4, 8 = 2^3) — clean manifolds;
      (role-limit) counts strictly between powers (5, 7) have NO integer dimension — fractal, no manifold;
      (general)    every strict gap between consecutive powers is role-limit.
    So "does the sprinkling converge to a manifold?" (the Hauptvermutung) IS the finitization boundary
    applied to dimension: integer dimension = Element/manifold vs fractal = role-limit/no-manifold.  The
    open wall is placed on the project's axis (H1), not left bare. *)
Theorem dimension_is_finitization_boundary :
  dim_is_element 2 16
  /\ dim_is_element 2 8
  /\ ~ dim_is_element 2 5
  /\ ~ dim_is_element 2 7
  /\ (forall s c D, 2 <= s -> s ^ D < c -> c < s ^ (S D) -> ~ dim_is_element s c).
Proof.
  split; [ exact dim_element_16 | ].
  split; [ exact dim_element_8 | ].
  split; [ exact dim_role_limit_5 | ].
  split; [ exact dim_role_limit_7 | exact between_powers_role_limit ].
Qed.
