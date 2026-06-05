(** * MinimalLengthDispersion.v — the FALSIFIABLE EDGE of the finitization programme: if spacetime is
      discrete at a minimal length ell (P4), the dispersion relation gets a definite, ENERGY-DEPENDENT
      rational correction — so a minimal length is, in principle, a measurable number, and a null
      observation becomes an explicit upper bound on ell.  This is what turns "P4 = the cure for quantum
      gravity" from an internal-consistency framing into a (toy-level) empirical prediction.

    -- The physics --
      Continuum dispersion: omega = k.  On a lattice of spacing ell: omega = (2/ell) sin(ell k / 2)
      = k (1 - (ell k)^2 / 24 + ...).  The leading FRACTIONAL deviation (the signal) is
          corr ell k = (ell k)^2 / 24,
      and the un-normalized deviation factor is  frac_signal ell k = (ell k)^2.  Two consequences make it
      falsifiable: (i) the signal is ENERGY-DEPENDENT (grows with k) — the time-of-flight signature that
      gamma-ray-burst photon experiments (Fermi-LAT) look for; (ii) an observational ceiling eps on the
      fractional deviation forces  (ell k)^2 <= 24 eps  — an explicit upper bound on the minimal length.

    -- HONEST scope (loudly) --
      This is a TOY / structural model, NOT a reproduction of the Fermi-LAT analysis (no redshift
      integration, no source modelling, leading-order only; sin is replaced by its rational Taylor head).
      The numbers are ILLUSTRATIVE.  What is machine-checked is the SHAPE of the falsifiable prediction:
      discreteness => nonzero, energy-dependent signal => observational ceiling => explicit length bound.
      Note the H1 touch: the bound on (ell k)^2 is rational (Element), while ell itself = sqrt(24 eps)/k
      is a root (role-limit) — the bound on the SQUARE is derivable, ell itself sits past the wall.
      Complementary to the transfer-matrix dispersion in stdlib/ProcessLatticeDispersion.v (which computes
      dispersion_D from the gauge transfer matrix); this file adds the falsifiability layer.

    Elements: the rational signal frac_signal = (ell k)^2 and corr = (ell k)^2/24; concrete values
    Roles:    ell = minimal length (the sought finite number); k = probe energy; eps = observational ceiling
    Rules:    discreteness => nonzero energy-dependent signal => ceiling eps forces (ell k)^2 <= 24 eps

    ============ E/R/R разбор ============
      Rules (L5): дисперсия на решётке omega = k(1 - (ell k)^2/24 + ...) вместо omega = k; сигнал =
                  corr = (ell k)^2/24.  Дискретность (P4, шаг ell>0) => ненулевой энергозависимый сигнал;
                  континуум = предел ell->0 (сигнал->0).
      Roles (L4): ell (мин. длина, искомое конечное число) и k (энергия зонда).  Наблюдательный потолок eps
                  играет роль ОГРАНИЧИТЕЛЯ => переводится в ВЕРХНЮЮ ГРАНИЦУ на ell: (ell k)^2 <= 24 eps.
      Elements  : рациональные значения: corr(1,1)=1/24; энергозависимость corr(1,1)<corr(1,2)<corr(1,3);
                  граница (ell k)^2 <= 24 eps (рациональна = Element; сама ell = корень = role-limit).
    ДИАГНОСТИКА (P4): ТОЙ/структурная модель, НЕ воспроизведение Fermi-LAT (нет красного смещения, источника,
    только ведущий порядок).  Машинно-честно: (i) сигнал ненулевой, (ii) РАСТЁТ с энергией (time-of-flight
    smoking gun), (iii) потолок eps => явная граница на (ell k)^2.  Это ФОРМА фальсифицируемого предсказания --
    выводит финитизацию на эмпирику, числа иллюстративны.  H1-штрих: граница на КВАДРАТ выводима (Element),
    сама ell за стеной (корень = role-limit).

    STATUS: 15 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Small rational facts about the constant 24                             *)
(* ===================================================================== *)

Lemma Q24_pos : (0:Q) < 24.
Proof. vm_compute. reflexivity. Qed.

Lemma Q24_nz : ~ ((24:Q) == 0).
Proof. unfold Qeq. simpl. discriminate. Qed.

Lemma Hid24 : forall x : Q, (x / 24) * 24 == x.
Proof.
  intro x. unfold Qdiv. rewrite <- Qmult_assoc.
  rewrite (Qmult_comm (/24) 24), (Qmult_inv_r 24 Q24_nz). apply Qmult_1_r.
Qed.

(** Strict monotonicity of squaring on the nonnegative rationals (the workhorse). *)
Lemma Qsqr_lt : forall a b, 0 <= a -> a < b -> a * a < b * b.
Proof.
  intros a b Ha Hab.
  rewrite Qlt_minus_iff.
  assert (Heq : b * b + - (a * a) == (b + - a) * (b + a)) by ring.
  rewrite Heq.
  apply Qmult_lt_0_compat.
  - rewrite <- Qlt_minus_iff. exact Hab.
  - apply Qlt_le_trans with b.
    + apply Qle_lt_trans with a; [ exact Ha | exact Hab ].
    + rewrite Qle_minus_iff.
      assert (Hr : (b + a) + - b == a) by ring.
      rewrite Hr. exact Ha.
Qed.

(* ===================================================================== *)
(*  The dispersion signal                                                  *)
(* ===================================================================== *)

(** Un-normalized leading deviation factor (ell k)^2; the fractional signal is this over 24. *)
Definition frac_signal (ell k : Q) : Q := (ell * k) * (ell * k).
Definition corr (ell k : Q) : Q := frac_signal ell k / 24.

(** Discreteness gives a NONZERO signal: any ell>0, k>0 produces a positive deviation. *)
Lemma frac_pos : forall ell k, 0 < ell -> 0 < k -> 0 < frac_signal ell k.
Proof.
  intros ell k He Hk. unfold frac_signal.
  apply Qmult_lt_0_compat; apply Qmult_lt_0_compat; assumption.
Qed.

(** ENERGY-DEPENDENCE (the smoking gun): higher probe momentum => strictly larger signal. *)
Lemma frac_energy_dependent :
  forall ell k1 k2, 0 < ell -> 0 < k1 -> k1 < k2 -> frac_signal ell k1 < frac_signal ell k2.
Proof.
  intros ell k1 k2 He Hk1 Hk12. unfold frac_signal.
  apply Qsqr_lt.
  - apply Qlt_le_weak. apply Qmult_lt_0_compat; assumption.
  - rewrite (Qmult_comm ell k1), (Qmult_comm ell k2).
    apply Qmult_lt_compat_r; [ exact He | exact Hk12 ].
Qed.

(** Smaller minimal length => smaller signal (vanishes as ell -> 0): the continuum is the ell=0 limit. *)
Lemma frac_shrinks_with_ell :
  forall ell1 ell2 k, 0 < ell1 -> ell1 < ell2 -> 0 < k -> frac_signal ell1 k < frac_signal ell2 k.
Proof.
  intros ell1 ell2 k He1 He12 Hk. unfold frac_signal.
  apply Qsqr_lt.
  - apply Qlt_le_weak. apply Qmult_lt_0_compat; assumption.
  - apply Qmult_lt_compat_r; [ exact Hk | exact He12 ].
Qed.

(** THE FALSIFIABLE BOUND: an observational ceiling eps on the fractional signal is EQUIVALENT to the
    explicit minimal-length bound (ell k)^2 <= 24 eps. *)
Lemma corr_le_iff :
  forall ell k eps, corr ell k <= eps <-> frac_signal ell k <= 24 * eps.
Proof.
  intros ell k eps. unfold corr. split; intro H.
  - apply (proj2 (Qmult_le_r (frac_signal ell k / 24) eps 24 Q24_pos)) in H.
    rewrite Hid24, (Qmult_comm eps 24) in H. exact H.
  - apply (proj1 (Qmult_le_r (frac_signal ell k / 24) eps 24 Q24_pos)).
    rewrite Hid24, (Qmult_comm eps 24). exact H.
Qed.

(** A predicted signal that EXCEEDS the observed ceiling falsifies that ell. *)
Lemma signal_exceeds_excluded : forall s eps, eps < s -> ~ (s <= eps).
Proof. intros s eps H. apply Qlt_not_le. exact H. Qed.

(* ===================================================================== *)
(*  Concrete illustrative numbers (vm_compute)                             *)
(* ===================================================================== *)

Lemma corr_1_1 : corr 1 1 == 1 # 24.
Proof. unfold corr, frac_signal. vm_compute. reflexivity. Qed.

Lemma corr_energy_concrete : corr 1 1 < corr 1 2 /\ corr 1 2 < corr 1 3.
Proof. split; vm_compute; reflexivity. Qed.

Lemma corr_shrinks_concrete : corr (1 # 10) 1 < corr 1 1.
Proof. vm_compute. reflexivity. Qed.

(** Toy falsification: with probe k=1 and observed ceiling eps=1/100, the predicted signal at ell=1 is
    corr = 1/24 > 1/100, so a minimal length ell=1 (in these units) is EXCLUDED. *)
Lemma toy_signal_exceeds : (1 # 100) < corr 1 1.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_excluded : ~ (corr 1 1 <= (1 # 100)).
Proof. apply signal_exceeds_excluded. exact toy_signal_exceeds. Qed.

(* ===================================================================== *)
(*  Capstone: the falsifiable minimal-length prediction                    *)
(* ===================================================================== *)

(** The falsifiable edge, in one statement:
      (detectable)       discreteness gives a strictly positive signal;
      (energy-dependent) the signal grows with probe momentum (the time-of-flight signature);
      (length bound)     an observational ceiling eps is equivalent to (ell k)^2 <= 24 eps;
      (falsified)        a predicted signal above the ceiling excludes that ell.
    So a minimal length is, in principle, a measurable rational quantity — the finitization programme
    meets experiment.  (Toy/leading-order; the numbers are illustrative, not a Fermi-LAT fit.) *)
Theorem minimal_length_falsifiable :
  forall ell k eps, 0 < ell -> 0 < k ->
    0 < frac_signal ell k
    /\ (forall k2, k < k2 -> frac_signal ell k < frac_signal ell k2)
    /\ (corr ell k <= eps <-> frac_signal ell k <= 24 * eps)
    /\ (eps < corr ell k -> ~ (corr ell k <= eps)).
Proof.
  intros ell k eps He Hk. split; [| split; [| split ] ].
  - apply frac_pos; assumption.
  - intros k2 Hk2. apply frac_energy_dependent; assumption.
  - apply corr_le_iff.
  - apply Qlt_not_le.
Qed.
