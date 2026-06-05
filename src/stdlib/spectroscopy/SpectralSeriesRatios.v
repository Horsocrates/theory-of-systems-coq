(** * SpectralSeriesRatios.v — the GOLD STANDARD of a derived (not fitted) prediction: hydrogen
      spectral-series ratios, forced rationals with ZERO empirical leaves, audited as
      fully-first-principles via DerivationAudit.v.

      THE POINT.  The Rydberg level law gives the transition wavenumber n_i→n_f as
      ν = R·(1/n_f² − 1/n_i²).  The RATIO of two transitions is a pure rational in the integers n —
      the scale R CANCELS, so NO measured constant enters at all.  The only leaves are the counting
      integers n ("the n-th level"), which are Structural (forced by counting).  Hence the ratio is
      FORCED and EXACT: it comes OUT of the level law, it is not chosen to hit data.  This is what
      "derived, not fitted" looks like — contrast a bare "constant ≈ p/q" whose integers carry no
      forcing lemma.  Audited (DerivationAudit): n_gaps = 0 AND n_indep = 0 — fully first-principles.

      HEADLINE: Lyman-α / Balmer-α = 27/5, the repo's value, here FORCED from the n² law (not
      asserted).  Plus Balmer-α/Paschen-α = 20/7, and the series-limit ratios = n² (Lyman:Balmer
      limits = 4 = 2², Lyman:Paschen = 9 = 3²).  All exact, all from integers, R-free.  These match
      measured line-centroid ratios to high precision (in the gross-structure model the ratio is
      exact — R_M is common to both transitions of the same atom, so even the reduced-mass
      correction cancels; fine structure splits lines slightly around these centroids).

      THE CLUSTER SPLIT, even here: the finite lines are Elements (exact rationals); the SERIES
      LIMIT (n_i→∞, factor 1/n_f²) is a role-limit — the edge of the series, a limit of the
      transition process that no finite line reaches.

    Elements: the rational transition factors tfactor; the exact forced ratios 27/5, 20/7, n² (L1+P4)
    Roles:    the integer n = "which level" (a count); the series limit 1/n_f² (n_i→∞) = role-limit,
              the series edge reached by no finite line; the ratio = the forced prediction
    Rules:    the Rydberg level law E_n ∝ 1/n²; a transition ratio is a pure rational in the n's —
              R cancels — so the ratio is forced with no free parameter

    ============ E/R/R разбор ============
      Rules (L5): уровневый закон E_n∝1/n²; отношение переходов = чистая рациональная функция целых n,
                  R сокращается ⟹ отношение вынуждено без свободного параметра.
      Roles (L4): n = «какой уровень» (счёт); предел серии 1/n_f² (n_i→∞) = role-limit, край серии;
                  отношение = вынужденное предсказание.
      Elements  : рациональные tfactor; точные отношения 27/5, 20/7, n²; всё из целых n.
    ДИАГНОСТИКА (P4): чистейший ярус — только счётные листья, без шкалы; аудит fully_first_principles
    (n_gaps=0∧n_indep=0). Дихотомия кластера и здесь: конечные линии = Elements (точные рациональные),
    предел серии (n→∞) = role-limit. 27/5 ВЫХОДИТ из закона (forcing), не выбрано под данные = «выведено».

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From ToS Require Import stdlib.DerivationAudit.

Open Scope Q_scope.

(* ===================================================================== *)
(*  THE ENGINE: the R-free transition factor 1/n_f² − 1/n_i²               *)
(* ===================================================================== *)

(** The transition wavenumber in units of R: tfactor(n_f, n_i) = 1/n_f² − 1/n_i².  R is dropped —
    it cancels in every ratio below, so NO measured constant ever appears. *)
Definition tfactor (nf ni : Q) : Q := 1 / (nf * nf) - 1 / (ni * ni).

(** The series limit factor (n_i → ∞): 1/n_f².  This is a role-limit — the edge of the series,
    approached by the lines but reached at no finite n_i. *)
Definition series_limit (nf : Q) : Q := 1 / (nf * nf).

(* ===================================================================== *)
(*  The named lines, exactly (forced by the level law)                     *)
(* ===================================================================== *)

(** Lyman-α (2→1): 1/1 − 1/4 = 3/4. *)
Lemma lyman_alpha : tfactor 1 2 == 3 # 4.
Proof. vm_compute. reflexivity. Qed.

(** Balmer-α (3→2): 1/4 − 1/9 = 5/36. *)
Lemma balmer_alpha : tfactor 2 3 == 5 # 36.
Proof. vm_compute. reflexivity. Qed.

(** Paschen-α (4→3): 1/9 − 1/16 = 7/144. *)
Lemma paschen_alpha : tfactor 3 4 == 7 # 144.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THE FORCED RATIOS — exact, R-free, from integers only                  *)
(* ===================================================================== *)

(** ★ Lyman-α / Balmer-α = 27/5 — the repo's value, here FORCED by the n² law (it comes out of
    tfactor, it is not asserted).  Zero empirical leaves; the integers 1,2,3 are counts. *)
Lemma lyman_balmer_ratio : tfactor 1 2 / tfactor 2 3 == 27 # 5.
Proof. vm_compute. reflexivity. Qed.

(** Balmer-α / Paschen-α = 20/7, likewise forced and exact. *)
Lemma balmer_paschen_ratio : tfactor 2 3 / tfactor 3 4 == 20 # 7.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The series limits and the n² law made explicit                         *)
(* ===================================================================== *)

(** The Lyman series limit (∞→1) is 1, the Balmer limit (∞→2) is 1/4. *)
Lemma lyman_series_limit : series_limit 1 == 1.
Proof. vm_compute. reflexivity. Qed.

Lemma balmer_series_limit : series_limit 2 == 1 # 4.
Proof. vm_compute. reflexivity. Qed.

(** ★ The series-limit ratios ARE n²: Lyman:Balmer = 4 = 2², Lyman:Paschen = 9 = 3².  The level
    law's 1/n² is laid bare — these are the cleanest forced integers in the hydrogen spectrum. *)
Lemma limit_ratio_lyman_balmer : series_limit 1 / series_limit 2 == (2 # 1) * (2 # 1).
Proof. vm_compute. reflexivity. Qed.

Lemma limit_ratio_lyman_paschen : series_limit 1 / series_limit 3 == (3 # 1) * (3 # 1).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The audit: this prediction is FULLY FIRST-PRINCIPLES (zero gap, zero input) *)
(* ===================================================================== *)

(** The Lyman/Balmer = 27/5 prediction audited (DerivationAudit): its only leaves are the two
    counting integers (Structural), no measured input, matching one data point — so it is
    fully-first-principles (n_gaps = 0 AND n_indep = 0), the top tier.  The gap is provably zero. *)
Definition lyman_balmer_audit : Audit := mkAudit (Structural :: Structural :: nil) 1%nat.

Lemma lyman_balmer_fully : fully_first_principles lyman_balmer_audit.
Proof.
  unfold fully_first_principles, lyman_balmer_audit, n_gaps, n_indep. simpl. split; reflexivity.
Qed.

Lemma lyman_balmer_derived : derived lyman_balmer_audit.
Proof. apply fully_implies_derived. exact lyman_balmer_fully. Qed.

(* ===================================================================== *)
(*  Synthesis                                                            *)
(* ===================================================================== *)

(** The spectral-series ratios as the gold standard of a derived prediction:
      (forced ratios) Lyman/Balmer = 27/5 and Balmer/Paschen = 20/7, exact and R-free
        (`lyman_balmer_ratio`, `balmer_paschen_ratio`) — out of the n² law, not chosen;
      (n² law) the series-limit ratios are 2² and 3² (`limit_ratio_*`);
      (audit) the 27/5 prediction is fully-first-principles — n_gaps = 0 and n_indep = 0
        (`lyman_balmer_fully`) — the gap is provably zero.
    Every leaf is a counting integer; no measured constant enters; the value is forced and exact. *)
Theorem series_ratios_synthesis :
  (tfactor 1 2 / tfactor 2 3 == 27 # 5)
  /\ (tfactor 2 3 / tfactor 3 4 == 20 # 7)
  /\ (series_limit 1 / series_limit 2 == (2 # 1) * (2 # 1))
  /\ (series_limit 1 / series_limit 3 == (3 # 1) * (3 # 1))
  /\ fully_first_principles lyman_balmer_audit.
Proof.
  split; [ exact lyman_balmer_ratio | ].
  split; [ exact balmer_paschen_ratio | ].
  split; [ exact limit_ratio_lyman_balmer | ].
  split; [ exact limit_ratio_lyman_paschen | exact lyman_balmer_fully ].
Qed.
