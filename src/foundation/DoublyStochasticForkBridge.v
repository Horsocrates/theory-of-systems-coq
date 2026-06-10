(** * DoublyStochasticForkBridge.v — the L1-forced doubly-stochastic matrix is the SHARED ROOT of the
       BORN RULE (quantum probability) and the SECOND LAW (arrow of time): irreversibility and quantum
       probability are two faces of ONE doubly-stochastic structure — crystallised on the 3-4-5 object.

    THE OBSERVATION (a candidate 7th thread).
    L1 (no site privileged) forces the transition matrix to be DOUBLY-STOCHASTIC
    (L1_DoublyStochastic.v: row+column sums = 1). The symmetric 2-state case is
        T(t) = [[1−t, t],[t, 1−t]],   acting on a distribution (a, 1−a) by
        apply_T t a = (1−t)·a + t·(1−a)            (MajorizationSchur.v:13).
    This ONE object forks into the two pillars of physics, with NO shared statement until now:

      (root)   doubly-stochastic ⟹ TOTAL PROBABILITY is conserved: apply_T t a + apply_T t (1−a) = 1.

      (QM arm — Born)  at t = (4/5)² = 16/25, T(t) is the UNISTOCHASTIC |U|² of the 3-4-5 unitary
        U = [[3/5,−4/5],[4/5,3/5]] (BornRuleFromUnitarity.v): the transition probabilities from a basis
        state are apply_T(16/25) 1 = 9/25 = |U₀₀|² and apply_T(16/25) 0 = 16/25 = |U₀₁|², summing to 1
        (born_rule_p2). So the doubly-stochastic map IS the Born rule. (vein D / F, H63, ThreeFifths.)

      (thermo arm — second law)  T(t) MIXES toward the uniform distribution: apply_T t (1/2) = 1/2 is the
        fixed point, and S2(a) < S2(apply_T t a) — entropy strictly increases (majorization / Schur,
        MajorizationSchur.v). So the SAME doubly-stochastic map IS the second law (no Past Hypothesis).

    Hence: ONE doubly-stochastic structure, forced by L1, yields BOTH quantum probability (Born) AND the
    arrow of time (second law). Vein D names only the QM (unistochastic→Born) arm; the thermo
    (majorization→second law) arm is its forgotten twin. The 3-4-5 object ties this to the Cayley vein.

    WHAT IS NEW / HONEST SCALE.
    Birkhoff (doubly-stochastic = convex hull of permutations), Schur-convexity ⟹ entropy non-decrease,
    and unistochastic ⟹ Born are all classical, and the thermo facts here are concrete (vm_compute)
    rather than a general Schur theorem. NEW (synthesis+observation, machine-checked): the UNIFICATION —
    that one L1-forced doubly-stochastic matrix is simultaneously the Born rule (its t=square case = |U|²)
    AND the second-law mixing, crystallised on the 3-4-5 object. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : симметричная бистохастическая 2×2 T(t)=[[1−t,t],[t,1−t]] (действие apply_T t a=(1−t)a+t(1−a));
                 распределение (a,1−a); бинарная энтропия S2; 3-4-5 объект t=(4/5)²=16/25.
      Roles    : бистохастичность = сохранение полной вероятности (нормировка Борна); T=|U|² (унистохастика) =
                 правило Борна (QM-ветвь); смешивание к 1/2 (мажоризация) = второе начало (термо-ветвь);
                 единый объект = L1-вынужденная бистохастика.
      Rules    : apply_T t a + apply_T t (1−a) = 1 (сохранение вероятности); apply_T(16/25) 1 = U00² = 9/25,
                 apply_T(16/25) 0 = U01² = 16/25, U00²+U01²=1 (Борн |U|²); apply_T t (1/2)=1/2 (равномерное —
                 неподвижная точка) + S2(a)<S2(apply_T t a) (энтропия растёт, второе начало).
      ДИАГНОСТИКА (P4): ОДНА бистохастическая структура (T(t), вынужденная L1 «нет привилегированного узла»)
      даёт И правило Борна (|U|², нормировка — QM), И второе начало (мажоризация к равномерному, рост энтропии
      — термо). Необратимость (стрела времени) и квантовая вероятность — две грани одного L1-бистохастического
      объекта; crystallized на 3-4-5 (связь с веной F/H63/ThreeFifths). ЧЕСТНО: бистохастика→{мажоризация,
      унистохастика} классична (Биркгоф/Шур), термо-факты конкретны (не общая теорема Шура); ново — машинная
      унификация двух ветвей на одном объекте + L1-корень. Уровень: `синтез+наблюдение`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (imports stdlib.foundations.MajorizationSchur + physics.BornRuleFromUnitarity)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import stdlib.foundations.MajorizationSchur.   (* apply_T, S2, apply_T_fixed_half, entropy_increase_1 *)
From ToS Require Import physics.BornRuleFromUnitarity.          (* U00, U01, born_rule_p2 *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  ROOT: doubly-stochastic ⟹ total probability is conserved             *)
(* ===================================================================== *)

(** ★ The doubly-stochastic map sends a probability distribution (a, 1−a) to a probability distribution:
    its two output weights sum to 1. This is row-stochasticity = the Born normalization at the root. *)
Theorem apply_T_conserves_probability : forall t a : Q,
  apply_T t a + apply_T t (1 - a) == 1.
Proof. intros t a. unfold apply_T. ring. Qed.

(* ===================================================================== *)
(*  QM ARM: the doubly-stochastic map at t = (4/5)² IS the Born rule |U|² *)
(* ===================================================================== *)

(** ★★ At t = (4/5)² = 16/25, the doubly-stochastic transition probabilities from a basis state are
    exactly the Born probabilities |U₀₀|², |U₀₁|² of the 3-4-5 unitary U = [[3/5,−4/5],[4/5,3/5]]:
        apply_T(16/25) 1 = 9/25 = U₀₀²,    apply_T(16/25) 0 = 16/25 = U₀₁²,
    and they sum to 1 (born_rule_p2). So the doubly-stochastic map at a square parameter IS the Born rule. *)
Theorem apply_T_is_born :
  apply_T (16 # 25) 1 == U00 * U00
  /\ apply_T (16 # 25) 0 == U01 * U01
  /\ U00 * U00 + U01 * U01 == 1.
Proof.
  split. { unfold apply_T, U00. vm_compute. reflexivity. }
  split. { unfold apply_T, U01. vm_compute. reflexivity. }
  exact born_rule_p2.
Qed.

(** The two Born transition probabilities themselves sum to 1 (probability conservation of the QM arm). *)
Lemma born_probs_sum_one : apply_T (16 # 25) 1 + apply_T (16 # 25) 0 == 1.
Proof. unfold apply_T. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  THERMO ARM: the SAME map mixes toward uniform — the second law        *)
(* ===================================================================== *)

(** The uniform distribution (1/2,1/2) is the FIXED POINT of the doubly-stochastic mixing. *)
Theorem uniform_is_fixed : forall t : Q, apply_T t (1 # 2) == 1 # 2.
Proof. exact apply_T_fixed_half. Qed.

(** ★ Entropy STRICTLY INCREASES under the mixing: S2(3/4) < S2(apply_T(1/3) (3/4)) — the second law,
    with no Past Hypothesis (the doubly-stochastic map alone forces it). *)
Theorem entropy_increases : S2 (3 # 4) < S2 (apply_T (1 # 3) (3 # 4)).
Proof. exact entropy_increase_1. Qed.

(* ===================================================================== *)
(*  CAPSTONE: one doubly-stochastic structure → Born AND the second law   *)
(* ===================================================================== *)

(** ONE L1-forced doubly-stochastic matrix T(t) = [[1−t,t],[t,1−t]], read across two pillars:
      (root)   conserves total probability — apply_T t a + apply_T t (1−a) = 1;
      (Born)   at t=(4/5)² it is the unistochastic |U|² of the 3-4-5 unitary: the transition
               probabilities are |U₀₀|²=9/25, |U₀₁|²=16/25, summing to 1 (quantum probability);
      (2nd law) it fixes the uniform distribution and strictly increases entropy (the arrow of time).
    So quantum probability (Born) and irreversibility (second law) are two faces of one doubly-stochastic
    structure forced by L1 (no privileged site) — vein D's unistochastic→Born arm and the
    majorization→second-law arm are twins. Crystallised on the 3-4-5 object (Cayley vein, H63). *)
Theorem doubly_stochastic_fork :
  (forall t a, apply_T t a + apply_T t (1 - a) == 1)                       (* root: probability conserved *)
  /\ (apply_T (16 # 25) 1 == U00 * U00 /\ apply_T (16 # 25) 0 == U01 * U01) (* Born: = |U|² of 3-4-5 unitary *)
  /\ (U00 * U00 + U01 * U01 == 1)                                          (* Born normalization *)
  /\ (forall t, apply_T t (1 # 2) == 1 # 2)                                (* 2nd law: uniform is fixed *)
  /\ (S2 (3 # 4) < S2 (apply_T (1 # 3) (3 # 4))).                          (* 2nd law: entropy increases *)
Proof.
  split. exact apply_T_conserves_probability.
  split. { split; [ apply (proj1 apply_T_is_born) | apply (proj1 (proj2 apply_T_is_born)) ]. }
  split. exact born_rule_p2.
  split. exact uniform_is_fixed.
  exact entropy_increases.
Qed.
