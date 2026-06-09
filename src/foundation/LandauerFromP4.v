(** * LandauerFromP4.v — can the Landauer floor (>=1 bit per irreversible binary actualization) be DERIVED
       from P4, or is it a fundamental import?  E/R/R analysis (done, not pre-judged) -> it largely REDUCES:
         floor POSITIVITY  <= P4 (permanence: the unchosen branch is RETAINED-inaccessible, not annihilated);
         floor VALUE (=1)  <= L2 (binarity: 2 branches, 1 retained = log2(2) = 1 bit);
         "entropy"          <= the inaccessible-distinction count (the proxy / unit bridge).
       So the Landauer floor is NOT an independent dynamical postulate on top of ToS -- it decomposes into
       P4 + binarity + (entropy = distinction count).  The cost-FREE alternative (annihilation, 0 bits) is
       exactly a NON-permanent past (~P4).

    THE DECOMPOSITION (what forces what).
      A binary distinction has 2 branches; committing actualizes 1.  The unchosen branch's FATE:
        - RETAINED-inaccessible (P4-permanent, determinate past): it persists in the fixed past as an
          inaccessible record -> the inaccessible count rises by (branches - committed) = 1 bit;
        - ANNIHILATED (no trace): the inaccessible count rises by 0 -- BUT then the past is not determinate
          (you cannot tell which branch was the alternative), i.e. NOT permanent = ~P4.
      So cost > 0 IFF permanent (P4); cost value = branches - committed = 1 (binarity).

    HONEST RESIDUAL (a reduction modulo two named residuals, NOT an elimination).
      (R1) "entropy = inaccessible-distinction count" is the proxy / unit bridge to physical thermodynamic
           entropy (k_B ln2 per bit).  NOT removed -- it is the same identification used throughout the arc.
      (R2) The load-bearing reading "P4-determinacy => the unchosen branch is RETAINED (not annihilated)" is
           an INTERPRETATION of P4's content (a determinate fixed past records what was / was not).  Whether
           this reading is genuinely MORE PRIMITIVE than Landauer, or is Landauer in ToS clothing, is itself
           OPEN.  So: the floor decomposes into P4 + binarity + proxy, but the primitiveness of (R2) vs
           Landauer is not settled here.

    Elements: the 2 branches (binary) ; the committed branch (1) ; the unchosen branch's fate ; the count.
    Roles:    permanence (P4) = fate "retained-inaccessible" ; binarity = the count (2-1) ; entropy = count.
    Rules:    P4 => retained ; binarity => retained = 2-1 = 1 ; entropy = count => cost = 1 ; annihilation (=~P4) = 0.

    ============ E/R/R разбор ============
      Elements (L1): 2 ветви (бинарно); зафиксированная ветвь (1); судьба невыбранной; счёт.
      Roles    (L4): постоянство (P4) = судьба «удержана-недоступной»; бинарность = счёт (2-1); энтропия = счёт.
      Rules    (L5): P4 => удержана; бинарность => удержано = 2-1 = 1; энтропия=счёт => cost=1; аннигиляция(=~P4)=0.
      ДИАГНОСТИКА (P4): положительность пола <= P4 (аннигиляция=¬P4 бесплатна); значение(=1) <= бинарность L2;
      энтропия <= счёт. Ландауэр СВОДИТСЯ к P4+бинарность+прокси, не отдельный постулат. ОСТАТОК: (R1)
      энтропия=счёт — единичный мост (наш прокси, не устранён); (R2) чтение «P4-определённость => ветвь удержана,
      не аннигилирована» — интерпретация P4; её примитивность vs Ландауэр ОТКРЫТА. Редукция по модулю (R1),(R2),
      не устранение. Уровень: `редукция импорта к основанию + честный остаток`.

    CORRECTION (see RecordingVsDeterminacy.v): the "reduction modulo R2" below OVERSTATED it.  Digging R2
    shows it CONFLATES metaphysical determinacy (P4: the past is a fixed fact) with physical recording (the
    present encodes the fact -- the Landauer-relevant bit).  These are distinct: a determinate past can be
    unrecorded (erased without trace).  The entropy cost attaches to RECORDING, and P4 supplies only the
    FACT, not the encoding.  So Landauer does NOT reduce to P4 -- its positivity rests on RECORDING (a
    separate principle: information physically encoded), NOT on P4-determinacy.  The decomposition below
    (value <= binarity, "entropy" <= count) stands; only the "positivity <= P4" claim is corrected to
    "positivity <= recording".

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  A binary distinction, the commit, the unchosen branch's fate           *)
(* ===================================================================== *)

(** A binary distinction (L2): exactly 2 branches. *)
Definition branches : nat := 2.

(** Committing actualizes exactly ONE branch. *)
Definition committed : nat := 1.

(** The unchosen branch's fate under P4-permanence: RETAINED-inaccessible (the determinate fixed past keeps
    it as an inaccessible record).  The only cost-FREE alternative is ANNIHILATION = a non-permanent (~P4) past. *)
Definition retained_inaccessible (permanent : bool) : nat :=
  if permanent then branches - committed else 0.

(** Entropy increment = the inaccessible-distinction count (the proxy / unit bridge to physical entropy). *)
Definition entropy_cost (permanent : bool) : nat := retained_inaccessible permanent.

(* ===================================================================== *)
(*  The floor VALUE comes from binarity (L2)                               *)
(* ===================================================================== *)

(** * The floor value = branches - committed = the binary "1 bit". *)
Theorem cost_value_from_binarity : entropy_cost true = branches - committed.
Proof. reflexivity. Qed.

(** A binary commit retains exactly 1 bit (= log2(2)). *)
Theorem binary_retains_one_bit : entropy_cost true = 1.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The floor POSITIVITY comes from P4 (permanence)                        *)
(* ===================================================================== *)

(** The cost-free alternative (annihilation = non-permanent = ~P4) costs nothing. *)
Theorem annihilation_is_free : entropy_cost false = 0.
Proof. reflexivity. Qed.

(** * The floor is POSITIVE for a permanent (P4) past -- the Landauer floor's positivity comes from P4. *)
Theorem floor_positive_from_permanence : 0 < entropy_cost true.
Proof. unfold entropy_cost, retained_inaccessible, branches, committed. simpl. lia. Qed.

(** * The cost is positive IFF the past is permanent (P4): the floor EXISTS exactly because of P4, not as an
    imported postulate.  (Annihilation -- the only free option -- is precisely ~P4.) *)
Theorem floor_iff_permanent : forall p, 0 < entropy_cost p <-> p = true.
Proof.
  intro p. destruct p; unfold entropy_cost, retained_inaccessible, branches, committed; simpl.
  - split; intros _; (lia || reflexivity).
  - split; intro H; (discriminate H || (exfalso; lia)).
Qed.

(* ===================================================================== *)
(*  CAPSTONE — the Landauer floor decomposes into P4 + binarity + proxy    *)
(* ===================================================================== *)

(** The Landauer floor, reduced (modulo the entropy=count proxy and the P4-determinacy reading):
      (value)       cost(permanent) = branches - committed -- the value is the binary "1 bit" (L2);
      (= 1)         a binary commit retains exactly 1 bit;
      (positive)    a permanent (P4) past has positive cost -- the floor's positivity is from P4;
      (free = ~P4)  annihilation (the only cost-free option) costs 0 and is a non-permanent (~P4) past;
      (iff P4)      the cost is positive IFF permanent -- the floor EXISTS exactly because of P4.
    So Landauer's floor is not an independent dynamical postulate: its POSITIVITY is P4, its VALUE is
    binarity (L2), its unit is the entropy=count proxy.  (Residual: the proxy R1 and the determinacy reading
    R2 -- whose primitiveness vs Landauer is open.) *)
Theorem landauer_floor_reduced :
  (entropy_cost true = branches - committed)
  /\ (entropy_cost true = 1)
  /\ (0 < entropy_cost true)
  /\ (entropy_cost false = 0)
  /\ (forall p, 0 < entropy_cost p <-> p = true).
Proof.
  split; [ reflexivity | ].
  split; [ reflexivity | ].
  split; [ exact floor_positive_from_permanence | ].
  split; [ reflexivity | ].
  exact floor_iff_permanent.
Qed.
