(** * EntropyCountDefinitional.v — the LAST input of the arrow analysis, examined: "entropy = distinction
       count" is DEFINITIONAL in ToS, not a substantive import.  The information-entropy in bits = the
       distinction count = log2(W), because in ToS a configuration IS its distinction-set (W = 2^count) and
       indifference (EquipartitionRule) gives S = log W.  The ONLY genuine import is Boltzmann's hypothesis
       (information-entropy = thermodynamic HEAT entropy) + the k_B unit -- and that is about HEAT, not the
       arrow.  So the INFORMATION arrow is fully ToS; only the heat-reading imports Boltzmann.

    THE SPLIT.
      (definitional, ToS)  W = 2^count : a configuration is a set of distinctions, so the number of
                           distinguishable configurations of n binary distinctions is 2^n.  Hence the count
                           IS log2(W) (2^count = W) -- the information-entropy in bits.
      (definitional, ToS)  entropy ADDS while W MULTIPLIES (entropy(n+m)=n+m, W(n+m)=W(n)*W(m)) -- so the
                           "log" is just the additive<->multiplicative bridge (extensivity), forced once
                           configs are distinction-sets; nothing extra.
      (ToS, EquipartitionRule) indifference (uniform microstates) gives Shannon S = log W = count.
      (UNIT)               k_B ln2 : a pure dimensional conversion (bit -> Joule/Kelvin); a units choice.
      (THE IMPORT)         Boltzmann's hypothesis: information-entropy = thermodynamic (heat) entropy
                           (dS = dQ/T).  This links distinction-counting to HEAT / temperature -- a SEPARATE
                           physical layer (energy/temperature are not distinction-counts).  This is the one
                           genuine import, and it concerns HEAT, not the directional arrow.

    NET RESULT for the whole arrow analysis.
      INFORMATION arrow (the distinction count grows) reduces ENTIRELY to ToS: P4 (append-only accumulation,
        RecordingFromP4) + L2 (binarity) + indifference (EquipartitionRule) + the origin (ArrowSignFromOrigin).
        NO substantive import.
      THERMODYNAMIC (heat) arrow additionally needs Boltzmann's info=heat hypothesis + k_B units -- the one
        irreducible physics import, the SAME one physics has (S = k log W is a postulate there too).
      So the true bedrock is NOT "entropy=count" (definitional) but the information<->heat link (Boltzmann).

    HONEST CAVEAT.  Indifference is ToS-affine (EquipartitionRule/EquipartitionBedrock) but the softest ToS
    principle (a qualitative->quantitative gap, weaker than P4).  And "config = distinction-set => W=2^count"
    is near-definitional but assumes the distinctions are INDEPENDENT (no constraints) -- the free/max-entropy
    case.  The information arrow rests on these (ToS-internal); only HEAT needs Boltzmann.

    Elements: distinction count n ; configuration count W = 2^n ; entropy in bits = n.
    Roles:    n = info-entropy (bits) = distinction count ; W = distinguishable configs ; log = additive<->mult bridge.
    Rules:    config = distinction-set => W = 2^count ; indifference => S = log W = count ; entropy adds, W multiplies.

    ============ E/R/R разбор ============
      Elements (L1): счёт различений n; число конфигураций W=2^n; энтропия в битах = n.
      Roles    (L4): n = инфо-энтропия (бит) = счёт различений; W = различимые конфиги; log = мост аддит.<->мульт.
      Rules    (L5): конфиг = набор различений => W=2^count; индифферентность => S=log W=count; счёт складывается, W перемножается.
      ДИАГНОСТИКА (P4): «энтропия=счёт» ОПРЕДЕЛИТЕЛЬНА в ToS (W=2^count из конфиг=набор-различений; индифферентность
      => S=log W; счёт аддитивен/W мультипликативна => log-мост). НЕ субстантивный импорт. Настоящий импорт =
      Больцман (инфо-энтропия = ТЕПЛОВАЯ энтропия) + k_B-единицы — про ТЕПЛО, не про стрелу. Инфо-стрела = целиком
      ToS (P4+L2+индифферентность+происхождение); тепловая добавляет Больцмана. ЧЕСТНО: индифферентность —
      мягчайший ToS-принцип; W=2^count предполагает независимые различения (max-энтропия). Уровень: `определительная
      редукция + локализация истинного (Больцман/тепло) импорта`.

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  W = 2^count, entropy = count : the definitional identification         *)
(* ===================================================================== *)

(** The number of DISTINGUISHABLE configurations of n independent binary distinctions: W = 2^n.
    (A configuration IS its distinction-set, so distinguishable configs are counted by their distinctions.) *)
Definition config_count (n : nat) : nat := 2 ^ n.

(** Information-entropy in bits = the distinction count (= log2 W). *)
Definition entropy_bits (n : nat) : nat := n.

(** * The count IS log2(W): 2^count = W.  So "entropy = distinction count" just says count = log2(W). *)
Theorem count_is_log2_of_W : forall n, 2 ^ (entropy_bits n) = config_count n.
Proof. intro n. unfold entropy_bits, config_count. reflexivity. Qed.

Theorem W_eq_two_pow_count : forall n, config_count n = 2 ^ n.
Proof. intro n. reflexivity. Qed.

(* ===================================================================== *)
(*  Entropy ADDS while W MULTIPLIES -- the log is the additive<->mult bridge *)
(* ===================================================================== *)

(** * Information-entropy (the count) is ADDITIVE (extensive): entropy(n+m) = entropy(n) + entropy(m). *)
Theorem entropy_additive : forall n m, entropy_bits (n + m) = entropy_bits n + entropy_bits m.
Proof. intros n m. unfold entropy_bits. reflexivity. Qed.

(** * ...while the configuration count W is MULTIPLICATIVE: W(n+m) = W(n)*W(m).  So entropy = log W is FORCED
    as the additive<->multiplicative bridge (extensivity) -- nothing beyond "configs are distinction-sets". *)
Theorem W_multiplicative : forall n m, config_count (n + m) = config_count n * config_count m.
Proof. intros n m. unfold config_count. apply Nat.pow_add_r. Qed.

(* ===================================================================== *)
(*  CAPSTONE — entropy=count is definitional; the import is Boltzmann/heat  *)
(* ===================================================================== *)

(** "Entropy = distinction count" is DEFINITIONAL in ToS:
      (count = log2 W)  2^count = W -- the count is the base-2 log of the configuration count;
      (W = 2^count)     a configuration is a distinction-set, so W = 2^count;
      (entropy adds)    the count (info-entropy) is additive/extensive;
      (W multiplies)    while W is multiplicative -- so the "log" is just the additive<->mult bridge.
    Given indifference (EquipartitionRule, ToS), Shannon S = log W = count.  So entropy=count is NOT a
    substantive import; the only genuine import is Boltzmann's info-entropy = thermodynamic HEAT entropy
    (+ the k_B unit), which concerns HEAT, not the arrow.  Hence the INFORMATION arrow is fully ToS
    (P4 + L2 + indifference + origin); only the heat reading imports Boltzmann. *)
Theorem entropy_count_is_definitional :
  (forall n, 2 ^ (entropy_bits n) = config_count n)
  /\ (forall n, config_count n = 2 ^ n)
  /\ (forall n m, entropy_bits (n + m) = entropy_bits n + entropy_bits m)
  /\ (forall n m, config_count (n + m) = config_count n * config_count m).
Proof.
  split; [ exact count_is_log2_of_W | ].
  split; [ exact W_eq_two_pow_count | ].
  split; [ exact entropy_additive | exact W_multiplicative ].
Qed.
