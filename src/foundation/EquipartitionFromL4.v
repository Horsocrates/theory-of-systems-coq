(** * EquipartitionFromL4.v — digging UNDER the equipartition residual of EnergyAsActualizationRate.v.
       The "softest principle" REDUCES to a CORE ToS law: equipartition / indifference is the CONTRAPOSITIVE
       of L4 (Sufficient Reason).  Undistinguished alternatives get EQUAL weight because a weight-DIFFERENCE
       requires a distinguishing REASON (L4); absent one, no difference.  The VALUE 1/N follows from
       normalization.  So equipartition is not a soft separate bottom -- it is L4.

    THE REDUCTION.
      L4 (Sufficient Reason):  ~ (weight a == weight b) -> distinguishes a b.
        (to weight a over b is to make a distinction A>B; without a grounding distinction it is forbidden.)
      INDIFFERENCE (= contrapositive, derived):  ~ distinguishes a b -> weight a == weight b.
        (undistinguished alternatives carry equal weight.)  Constructive (Qeq is decidable -> 0 axioms).
      NORMALIZATION:  k equal weights summing to 1 are each 1/k -- the equipartition VALUE.
      Together: equipartition = L4 (qualitative indifference) + normalization (the 1/N value).  This closes
      the qualitative->quantitative gap EquipartitionBedrock.v flagged: the qualitative half is L4.

    HONEST RESIDUAL (watched closely -- the method has caught over-reductions 3x).
      (1) This yields indifference for UNDISTINGUISHED configs.  The full statistical-mechanics equipartition
          (DISTINGUISHABLE microstates equally likely) additionally needs EQUILIBRIUM = the P4-arrow endpoint
          (max distinctions, where the microstates are effectively symmetric) -- i.e. the arrow we derived.
      (2) The OTHER residual of the Boltzmann bridge -- "energy = rate of succession" -- would reduce via L5
          (fixed update rule) + discrete Noether, but that is markedly MORE SPECULATIVE than this L4 reduction
          and is NOT formalized here (honestly: a reading, not a deduction).
      (3) We are deep in interpretive territory; the tight structural force of the early results (e.g. the
          Lorentzian signature forced by P4) is no longer present here.

    Elements: configs ; the weight (a priori weight) ; the distinguishes-relation.
    Roles:    L4 = a weight-difference needs a distinguishing reason ; indifference = its contrapositive ;
              normalization = weights sum to 1.
    Rules:    L4 + (Qeq decidable) => undistinguished => equal weight ; + normalization => each = 1/N.

    ============ E/R/R разбор ============
      Elements (L1): конфиги; вес weight; отношение distinguishes.
      Roles    (L4): L4 = различие веса требует различающей причины; индифферентность = контрапозиция;
                     нормировка = веса в сумме 1.
      Rules    (L5): L4 + (Qeq разрешимо) => недистингвировано => равный вес; + нормировка => каждый = 1/N.
      ДИАГНОСТИКА (P4): равнораспределение ⟸ L4 (Достаточное основание) + нормировка — ЯДРОВОЙ закон, не мягкое
      дно. Разрыв qual→quant закрыт: качественная половина = L4. ОСТАТОК: (1) различимые микросостояния равновероятны
      нужно равновесие = конец P4-стрелы; (2) энергия=темп — L5/Нётер, спекулятивнее, не формализую; (3) глубоко
      в интерпретации, тугой ранней структуры тут нет. Уровень: `редукция равнораспределения к L4 + честные остатки`.

    STATUS: 3 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only; uses Qeq decidability, no `classic`)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  Indifference is the contrapositive of L4 (Sufficient Reason)           *)
(* ===================================================================== *)

Section Indifference.

Variable Config : Type.
(** Is there a distinction between a and b (a grounding reason to treat them differently)? *)
Variable distinguishes : Config -> Config -> Prop.
(** The a priori weight (probability density) assigned to a configuration. *)
Variable weight : Config -> Q.

(** L4 (Sufficient Reason): a DIFFERENCE in weight REQUIRES a distinguishing reason. *)
Hypothesis L4_sufficient_reason :
  forall a b, ~ (weight a == weight b) -> distinguishes a b.

(** * INDIFFERENCE = the contrapositive of L4: undistinguished alternatives carry EQUAL weight.  Derived
    constructively from L4 via the decidability of Qeq (no `classic` -- 0 axioms). *)
Theorem indifference_from_L4 :
  forall a b, ~ distinguishes a b -> weight a == weight b.
Proof.
  intros a b Hu. destruct (Qeq_dec (weight a) (weight b)) as [Heq | Hne].
  - exact Heq.
  - exfalso. apply Hu. apply L4_sufficient_reason. exact Hne.
Qed.

End Indifference.

(* ===================================================================== *)
(*  Normalization gives the equipartition VALUE 1/N                        *)
(* ===================================================================== *)

(** Concrete N=2: two equal weights summing to 1 are each 1/2. *)
Theorem equipartition_value_2 : forall w, (2 # 1) * w == 1 -> w == 1 # 2.
Proof. intros w H. lra. Qed.

(** * General N: k equal weights summing to 1 are each 1/k -- the equipartition value, from normalization. *)
Theorem equipartition_value :
  forall (k : positive) (w : Q), inject_Z (Zpos k) * w == 1 -> w == 1 / inject_Z (Zpos k).
Proof.
  intros k w H.
  assert (Hpos : 0 < inject_Z (Zpos k)) by (unfold Qlt; simpl; lia).
  assert (Hk : ~ (inject_Z (Zpos k) == 0)) by lra.
  rewrite <- H. field. exact Hk.
Qed.
