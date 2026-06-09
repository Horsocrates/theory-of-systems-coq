(** * GravityArrowEntropy.v — deepening the gravity<->time link to the ARROW: the gravitational arrow
       (fall toward slower time = higher distinction density K) and the THERMODYNAMIC arrow (entropy up)
       are ONE tendency toward higher distinction density.  P4 forces the temporal DIRECTION (stage-count
       up); the SIGN (density/entropy up rather than down) is the low-density-past POSIT, inherited from
       ArrowGroundingDescent.v and NOT derived; the ceiling is the holographic / black-hole maximum.

    THE CHAIN CONTINUED (from GravityIsTimeGradient.v).
      gravity = fall toward slower time  (GravityIsTimeGradient.v)
      slower time = higher distinction density K  (PolarizableVacuumIndex.v: time_rate = 1/K)
      higher distinction density = more distinguishable configurations = higher ENTROPY
        (HolographicEntropy.v: S = A/l_P^2 = boundary distinction count; 1 bit per binary distinction)
      ==> gravity (fall toward slower time) = motion toward higher entropy.
      The endpoint of gravitational collapse = the black hole = the MAXIMUM distinction density (holographic
      bound) = maximum entropy (Penrose's gravitational-entropy picture).

    WHAT IS DERIVED vs WHAT STAYS A POSIT (the crucial honesty, mirroring ArrowGroundingDescent.v).
      DERIVED (P4): the temporal DIRECTION -- the stage-count strictly increases (succession is irreversible).
      NOT DERIVED (posit): the SIGN -- whether density/entropy INCREASES (clustering) or DECREASES
        (dispersing) is NOT fixed by P4; BOTH trajectories advance the stage-count.  Entropy increase needs
        the low-density (smooth) initial condition -- the SAME low-entropy-past posit ArrowGroundingDescent.v
        isolated for the thermodynamic arrow.  So this UNIFIES the gravitational and thermodynamic arrows
        (one density tendency) and shows they SHARE the one posit; it does NOT resolve the arrow of time.

    HONEST SCOPE.  "entropy = distinction density" is the Element-side PROXY; the rigorous version is the
    holographic boundary count (field + radiation entropy included).  Local clustering can look ordering;
    the total (with the black-hole endpoint) is entropy-increasing.  This file formalizes the UNIFICATION
    and the shared sign-posit, not a derivation of the thermodynamic arrow.

    Elements: stage count K ; distinction density rho ; entropy S = rho (holographic count) ; holo_max.
    Roles:    K = arrow direction (P4) ; rho = density = gravity's target (high K) = entropy ;
              the two trajectories (cluster / disperse) = the sign ambiguity.
    Rules:    P4 => stage-count up (direction) ; gravity => fall toward higher rho ; entropy = rho ;
              sign NOT forced (both trajectories advance) => low-density past needed ; rho <= holo_max.

    ============ E/R/R разбор ============
      Elements (L1): счёт стадий K; плотность различений rho; энтропия S=rho (голографич. счёт); holo_max.
      Roles    (L4): K = направление стрелы (P4); rho = плотность = цель гравитации (высокое K) = энтропия;
                     две траектории (кластеризация/рассеяние) = неоднозначность знака.
      Rules    (L5): P4 => счёт стадий растёт (направление); гравитация => падение к большему rho;
                     энтропия = rho; знак НЕ форсирован => нужен низкоплотный старт; rho <= holo_max.
      ДИАГНОСТИКА (P4): объединяет грав. и термо. стрелы как ОДНУ тенденцию плотности; ЧЕСТНО — направление
      выведено (P4), ЗНАК постулирован (низкая плотность в прошлом, тот же пробел, что ArrowGroundingDescent),
      потолок голографический. НЕ решает проблему стрелы; изолирует выведенное vs постулированное.
      ЧЕСТНО: энтропия=плотность — Element-прокси (строго — голографич. граница). Уровень: `синтез + честный пробел`.

    STATUS: 8 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Stage (P4 arrow), distinction density, entropy, holographic ceiling    *)
(* ===================================================================== *)

(** The P4 stage-count = the time direction (number of actualized distinction-stages). *)
Definition stage (K : nat) : nat := K.

(** Entropy = distinction count (holographic, HolographicEntropy.v: S = A/l_P^2, 1 bit per distinction). *)
Definition entropy (rho : nat) : nat := rho.

(** Clustering trajectory (gravity + low-density start): density grows with the stage. *)
Definition rho_cluster (rho0 K : nat) : nat := rho0 + K.

(** Dispersing trajectory (the OTHER P4-consistent option): density falls with the stage. *)
Definition rho_disperse (rho0 K : nat) : nat := rho0 - K.

(** Finite holographic / black-hole ceiling on distinction density (illustrative bit-bound). *)
Definition holo_max : nat := 100.

Definition capped_entropy (rho : nat) : nat := Nat.min (entropy rho) holo_max.

(* ===================================================================== *)
(*  Direction is forced (P4); entropy = density; fall raises entropy        *)
(* ===================================================================== *)

(** * P4: the stage-count strictly increases -- the temporal DIRECTION is forced. *)
Theorem arrow_direction_forced : forall K, stage K < stage (S K).
Proof. intro K. unfold stage. lia. Qed.

(** Entropy IS the distinction count (the Element-side identification). *)
Theorem entropy_is_distinction_density : forall rho, entropy rho = rho.
Proof. intro rho. reflexivity. Qed.

(** * Falling toward slower time = toward higher distinction density (gravity's target) = higher ENTROPY. *)
Theorem falling_increases_entropy :
  forall rho_far rho_near, rho_far < rho_near -> entropy rho_far < entropy rho_near.
Proof. intros rf rn H. unfold entropy. exact H. Qed.

(** Along the clustering trajectory (gravity + low start), entropy strictly increases with the stage. *)
Theorem clustering_raises_entropy :
  forall rho0 K, entropy (rho_cluster rho0 K) < entropy (rho_cluster rho0 (S K)).
Proof. intros rho0 K. unfold entropy, rho_cluster. lia. Qed.

(* ===================================================================== *)
(*  The SIGN is NOT forced (the honest gap, shared with the thermo arrow)  *)
(* ===================================================================== *)

(** * THE HONEST CORE: P4 forces the DIRECTION (stage-count up) but NOT the SIGN -- the clustering trajectory
    raises entropy while the dispersing trajectory lowers it, and BOTH advance the stage-count.  Entropy
    increase requires the low-density (smooth) past -- the same posit ArrowGroundingDescent.v isolated. *)
Theorem sign_not_forced :
  (forall K, stage K < stage (S K))
  /\ entropy (rho_cluster 10 0) < entropy (rho_cluster 10 1)
  /\ entropy (rho_disperse 10 1) < entropy (rho_disperse 10 0).
Proof.
  split; [ intro K; unfold stage; lia | ].
  split; [ unfold entropy, rho_cluster; lia | unfold entropy, rho_disperse; lia ].
Qed.

(* ===================================================================== *)
(*  Holographic ceiling; gravitational collapse reaches the maximum        *)
(* ===================================================================== *)

(** Distinction density (entropy) is bounded above by the holographic / black-hole maximum. *)
Theorem holographic_ceiling : forall rho, capped_entropy rho <= holo_max.
Proof. intro rho. unfold capped_entropy. apply Nat.le_min_r. Qed.

(** * Gravitational collapse from low density REACHES the holographic maximum (the black-hole end state =
    maximum distinction density = maximum entropy). *)
Theorem collapse_reaches_max : exists K, capped_entropy (rho_cluster 0 K) = holo_max.
Proof. exists 100%nat. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                              *)
(* ===================================================================== *)

(** The gravitational arrow = the thermodynamic arrow = one distinction-density tendency:
      (direction)   the stage-count strictly increases -- P4 forces the temporal direction;
      (fall=S up)   falling toward slower time (higher density) raises entropy;
      (clustering)  along gravity + low start, entropy increases with the stage;
      (SIGN free)   but P4 does NOT force the sign -- dispersing also advances the stage while entropy falls;
                    entropy increase needs the low-density past (the shared posit, ArrowGroundingDescent.v);
      (ceiling)     entropy is bounded by the holographic / black-hole maximum;
      (collapse)    gravitational collapse reaches that maximum (the black-hole end state).
    Gravity, the arrow, and entropy are ONE tendency toward higher distinction density; the direction is
    derived (P4), the SIGN is the low-density-past posit.  This unifies the arrows; it does not resolve them. *)
Theorem gravity_entropy_arrow :
  (forall K, stage K < stage (S K))
  /\ (forall rf rn, rf < rn -> entropy rf < entropy rn)
  /\ (forall rho0 K, entropy (rho_cluster rho0 K) < entropy (rho_cluster rho0 (S K)))
  /\ ((forall K, stage K < stage (S K))
       /\ entropy (rho_cluster 10 0) < entropy (rho_cluster 10 1)
       /\ entropy (rho_disperse 10 1) < entropy (rho_disperse 10 0))
  /\ (forall rho, capped_entropy rho <= holo_max)
  /\ (exists K, capped_entropy (rho_cluster 0 K) = holo_max).
Proof.
  split; [ exact arrow_direction_forced | ].
  split; [ exact falling_increases_entropy | ].
  split; [ exact clustering_raises_entropy | ].
  split; [ exact sign_not_forced | ].
  split; [ exact holographic_ceiling | ].
  exact collapse_reaches_max.
Qed.
