(** * ERREntanglementMeasure.v — the QUANTITATIVE tier of "entanglement = non-product": enrich the
      Roles of a composite from a Prop-relation (ERREntanglement.v) to a Q-VALUED amplitude matrix,
      and exhibit a RATIONAL number — the determinant (= concurrence up to normalization) — that is 0
      exactly on categorical products and nonzero on the entangled witness.

    ERREntanglement.v proved, at the QUALITATIVE tier, that the parity (Bell/GHZ core) correlation is
    not a categorical product (separable) of its parts.  The user's question was sharper: are there
    real NUMBERS here, or only structure?  This file answers it by enriching the Roles tier.

    Enriched Roles = a Q-valued amplitude/correlation matrix  E : bool -> bool -> Q  (the two bools
    index the two components / two measurement settings).  Then:

      ★ factorizable E  — E = f (x) g (y): the Q-level PRODUCT (separable), the amplitude matrix has
                          rank <= 1.  This is the Q-analog of ERREntanglement's prod_rel.
      ★ q_det E         — the 2x2 determinant E00*E11 - E01*E10: a RATIONAL number, the quantitative
                          non-separability measure (= the concurrence, up to the irrational
                          normalization sqrt of the sum of squares).
      ★ q_swap_closed E — the multiplicative swap identity E00*E11 == E10*E01: the EXACT Q-analog of
                          ERREntanglement's swap_closed (Prop tier).
      ★ factorizable_swap / factorizable_det_zero — product => swap identity / det 0 (rank <= 1).
      ★ det_nonzero_not_factorizable — det /= 0 => NOT a product (detector SOUNDNESS).
      ★ det_zero_factorizable_pivot — det 0 => product (generic pivot): detector COMPLETENESS, so on
                          the generic stratum det 0 <=> product (a complete rational separability test).
      ★ ent             — the entangled witness = the 2x2 Walsh-Hadamard matrix [[1,1],[1,-1]] (the
                          amplitude/sign cousin of ERREntanglement's XOR parity); ent_det == -2 /= 0,
                          so ent_not_factorizable: a concrete RATIONAL nonzero measure of entanglement.

    So the SEPARATING quantity (the determinant) is rational and exact — there genuinely are numbers.
    What stays irrational is only the EXTREMAL amount: the optimal (maximally entangled) amplitudes
    1/sqrt 2 and the Tsirelson bound 2*sqrt 2 are role-limits (see src/.../BellTsirelson.v — cited,
    not re-proved here).  This is exactly the project's H1/role-limit theme: the BOUNDARY (separable
    vs not) is rational/decidable; the metric AMOUNT is the role-limit.

    ============================== E/R/R разбор ==============================
    Rules (the generative rule first):
      (1) the enriched Roles are Q-VALUED amplitudes E : bool -> bool -> Q (not a Prop-relation);
      (2) a composite is a Q-PRODUCT (separable) iff E factorizes as f (x) g (y) — rank <= 1;
      (3) rank <= 1 <=> the determinant q_det E = 0; equivalently the multiplicative swap identity
          holds; so the determinant is the quantitative non-separability measure;
      (4) the entangled witness (Walsh-Hadamard) has q_det = -2 /= 0 — a concrete rational measure.
    Roles (L4): factorizable = the Q-product; q_det = the measure (determinant/concurrence);
      q_swap_closed = the Q swap identity; ent = the Walsh-Hadamard amplitude witness.
    Elements (L1+P4): the carrier bool (components/settings); the Q amplitudes; the witness table.
    P4 diagnostic (could it be otherwise, under the SAME rules?):
      the amplitude matrix is NOT forced to be rank-1.  Under the same Elements (bool) and the same
      Rules tier (Q amplitudes), it can be rank-1 (separable, det 0) OR rank-2 (entangled, det /= 0),
      and the det is a RATIONAL number deciding it — the quantitative upgrade of the Prop-tier "Roles
      can exceed prod_rel" (ERREntanglement).
    Honesty wall:
      q_det = the concurrence ONLY up to the irrational normalization sqrt(sum of squares).  The
      VANISHING (the separability test) and the det VALUE are rational and exact (0 axioms); but the
      normalized measure and the Tsirelson optimum 2*sqrt 2 are role-limits — cited from BellTsirelson,
      NOT re-proved.  We prove detector SOUNDNESS (factorizable => det 0; det /= 0 => not factorizable);
      COMPLETENESS (det 0 => factorizable) is the classical 2x2 rank fact, noted not proved (it needs
      Q-division case analysis — deliberately avoided).  This does NOT put genuine quantum amplitudes
      over Q (the 1/sqrt 2 wall stays); it puts the rational SEPARATOR and the rational det VALUE over
      Q.  Bridges the Prop tier: the capstone carries both ~ separable parity_roles (ERREntanglement)
      and ~ factorizable ent — one phenomenon, two tiers.  0 axioms.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith.
From ToS Require Import foundation.ERREntanglement.  (* separable, parity_roles, parity_not_separable *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  THE ENRICHED ROLES — a Q-valued amplitude matrix                       *)
(* ===================================================================== *)

(** A Q-valued correlation/amplitude matrix over two binary components (or two measurement settings):
    the Roles tier upgraded from a Prop-relation to numbers. *)
Definition QCorr := bool -> bool -> Q.

(** Q-level PRODUCT (separable): the amplitude factorizes, E x y = f x * g y — rank <= 1. *)
Definition factorizable (E : QCorr) : Prop :=
  exists f g : bool -> Q, forall x y, E x y == f x * g y.

(** The 2x2 determinant of the amplitude matrix = the (unnormalized) concurrence: a RATIONAL number
    measuring non-separability. *)
Definition q_det (E : QCorr) : Q :=
  E false false * E true true - E false true * E true false.

(** The multiplicative swap identity — the EXACT Q-analog of ERREntanglement's swap_closed. *)
Definition q_swap_closed (E : QCorr) : Prop :=
  forall x y x' y', E x y * E x' y' == E x' y * E x y'.

(* ===================================================================== *)
(*  PRODUCT => the structural fingerprints (swap identity, det 0)          *)
(* ===================================================================== *)

(** ★★ A Q-product satisfies the swap identity (rank-1 amplitudes recombine multiplicatively) — the
    quantitative upgrade of separable_swap_closed. *)
Lemma factorizable_swap : forall E, factorizable E -> q_swap_closed E.
Proof.
  intros E [f [g Hfg]] x y x' y'.
  rewrite !Hfg. ring.
Qed.

(** ★★ A Q-product has ZERO determinant (rank <= 1) — concurrence 0, the separable case. *)
Lemma factorizable_det_zero : forall E, factorizable E -> q_det E == 0.
Proof.
  intros E [f [g Hfg]]. unfold q_det. rewrite !Hfg. ring.
Qed.

(** ★★ Detector SOUNDNESS: a NONZERO rational determinant certifies non-separability — the composite
    is NOT a categorical product of its parts. *)
Lemma det_nonzero_not_factorizable : forall E, ~ q_det E == 0 -> ~ factorizable E.
Proof.
  intros E Hd Hf. apply Hd. apply factorizable_det_zero. exact Hf.
Qed.

(** ★★ Detector COMPLETENESS (generic pivot): if the (false,false) amplitude is nonzero, a zero
    determinant FORCES factorizability — so on the generic stratum the rational determinant is a
    COMPLETE separability test (det 0 <=> product), not merely sound.  (The pivot hypothesis is the
    only genuine restriction; the degenerate E false false == 0 case is the classical rank fact.) *)
Lemma det_zero_factorizable_pivot : forall E,
  ~ E false false == 0 -> q_det E == 0 -> factorizable E.
Proof.
  intros E Hpiv Hdet. unfold q_det in Hdet. unfold factorizable.
  assert (Hkey : E false false * E true true == E false true * E true false).
  { rewrite <- (Qplus_0_l (E false true * E true false)).
    rewrite <- Hdet. ring. }
  exists (fun x : bool => if x then E true false / E false false else 1).
  exists (fun y : bool => if y then E false true else E false false).
  intros x y. destruct x, y; simpl.
  - assert (Htt : E true true == (E false true * E true false) / E false false).
    { rewrite <- Hkey. field. exact Hpiv. }
    rewrite Htt. field. exact Hpiv.
  - field. exact Hpiv.
  - ring.
  - ring.
Qed.

(* ===================================================================== *)
(*  THE ENTANGLED WITNESS — the 2x2 Walsh-Hadamard amplitude matrix        *)
(* ===================================================================== *)

(** The Walsh-Hadamard matrix [[1,1],[1,-1]] — the sign/amplitude cousin of ERREntanglement's XOR
    parity (entry = (-1)^(x AND y)). *)
Definition ent : QCorr := fun x y => if andb x y then Qopp 1 else 1.

(** ★ Its determinant is the concrete rational number -2 (nonzero) — a measured amount of
    entanglement. *)
Lemma ent_det : q_det ent == Qopp (inject_Z 2).
Proof. vm_compute. reflexivity. Qed.

(** ★★ Hence the witness is NOT a categorical product: a rational, exact certificate of entanglement. *)
Lemma ent_not_factorizable : ~ factorizable ent.
Proof.
  apply det_nonzero_not_factorizable.
  rewrite ent_det. intro C. vm_compute in C. discriminate C.
Qed.

(** ★ It also fails the swap identity at (false,false,true,true) — the quantitative twin of
    ERREntanglement's parity_not_swap_closed. *)
Lemma ent_not_swap_closed : ~ q_swap_closed ent.
Proof.
  intro H. specialize (H false false true true).
  vm_compute in H. discriminate H.
Qed.

(* ===================================================================== *)
(*  CAPSTONE — two tiers, one phenomenon                                   *)
(* ===================================================================== *)

(** ★★★ ENTANGLEMENT, QUANTITATIVE tier: enrich the Roles to a Q-valued amplitude matrix; then a
    RATIONAL number (the determinant = concurrence up to normalization) is the separator:
      (product fingerprint)  every Q-product satisfies the swap identity;
      (separable => det 0)   every Q-product has zero determinant (rank <= 1);
      (soundness)            a nonzero determinant certifies non-separability;
      (completeness)         on the generic stratum, det 0 forces a product (det 0 <=> product);
      (witness, a NUMBER)    the Walsh-Hadamard matrix has determinant -2 /= 0;
      (so it is entangled)   hence it is not a categorical product;
      (Prop companion)       and the qualitative tier agrees (~ separable parity_roles).
    The separating quantity is rational and exact — there genuinely are numbers; only the EXTREMAL
    amount (1/sqrt 2 amplitudes, Tsirelson 2*sqrt 2) is the role-limit. *)
Theorem err_entanglement_measure :
  (forall E, factorizable E -> q_swap_closed E)
  /\ (forall E, factorizable E -> q_det E == 0)
  /\ (forall E, ~ q_det E == 0 -> ~ factorizable E)
  /\ (forall E, ~ E false false == 0 -> q_det E == 0 -> factorizable E)
  /\ q_det ent == Qopp (inject_Z 2)
  /\ ~ factorizable ent
  /\ ~ separable parity_roles.
Proof.
  split; [ exact factorizable_swap | ].
  split; [ exact factorizable_det_zero | ].
  split; [ exact det_nonzero_not_factorizable | ].
  split; [ exact det_zero_factorizable_pivot | ].
  split; [ exact ent_det | ].
  split; [ exact ent_not_factorizable | exact parity_not_separable ].
Qed.

Print Assumptions ent_not_factorizable.
Print Assumptions err_entanglement_measure.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  8 Qed, 0 Admitted, 0 axioms.                                             *)
(*  Quantitative tier of "entanglement = non-product": Roles enriched from a  *)
(*  Prop-relation (ERREntanglement) to a Q-valued amplitude matrix QCorr.      *)
(*  factorizable (Q-product, rank<=1); q_det (determinant = concurrence up to  *)
(*  normalization, a RATIONAL number); q_swap_closed (Q swap identity).        *)
(*  factorizable_swap / factorizable_det_zero (product => fingerprints);       *)
(*  det_nonzero_not_factorizable (detector SOUNDNESS);                          *)
(*  det_zero_factorizable_pivot (COMPLETENESS, generic pivot => det 0 <=>       *)
(*  product, a complete rational separability test).  Witness ent = 2x2        *)
(*  Walsh-Hadamard [[1,1],[1,-1]]: ent_det == -2 /= 0 => ent_not_factorizable  *)
(*  (a concrete rational certificate), ent_not_swap_closed (twin of            *)
(*  parity_not_swap_closed).  Capstone err_entanglement_measure carries BOTH   *)
(*  tiers (~ factorizable ent AND ~ separable parity_roles).  HONEST: the      *)
(*  separator (det) and its value are rational/exact (0 ax); the normalized    *)
(*  measure and Tsirelson 2*sqrt2 are role-limits (cited, not re-proved);      *)
(*  detector COMPLETENESS (det 0 => factorizable) is the classical 2x2 rank    *)
(*  fact, noted not proved (avoids Q-division).  No quantum amplitudes over Q  *)
(*  (1/sqrt2 wall stays) — only the rational separator/value.                 *)
(* ========================================================================= *)
