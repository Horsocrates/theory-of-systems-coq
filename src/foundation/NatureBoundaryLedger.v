(** * NatureBoundaryLedger.v — confronting the finitization boundary with NATURE: a machine-checked
      ledger that, window by window, asks whether observation puts nature on the Element (finite) side or
      the role-limit (continuum) side — and is honest enough to let the check REFUTE the naive realization
      of P4.  The headline: the empirical confrontation DISCIPLINES the theory, it does not crown it.

    -- Why this file --
      MinimalLengthDispersion.v gave the falsifiable edge (a minimal length is a measurable number).  This
      file takes the next, harder step: it lines the edge up against the ACTUAL observational numbers.  Coq
      cannot observe nature; what it CAN do is encode the real published bounds and the boundary's
      predictions side by side and render verdicts, machine-checking the arithmetic.

    -- The five windows and their verdicts --
      (1) Observable quantization  -> SupportsFinite.  Atomic spectra and angular momentum are observed to
          be DISCRETE, with RATIONAL ratios (hydrogen E_2/E_1 = 1/4, SHO ladder 2n+1) — the Element side at
          the level of OBSERVABLES.  (HONEST: observable-level discreteness is NOT spacetime discreteness.)
      (2) Lorentz dispersion       -> RefutesNaiveLattice.  Fermi-LAT GRB 090510 (Abdo et al., Nature 462,
          331, 2009) gives M_QG,1 / M_Planck > 1.2 (linear).  A naive REGULAR spatial lattice generically
          predicts linear Lorentz violation at the lattice scale, i.e. ratio = 1.  Since 1 < 6/5, the naive
          value falls BELOW the observed floor: the regular-lattice realization of P4 is EXCLUDED at the
          Planck scale.  (The check cuts AGAINST the naive theory — its sharpest tooth.)
      (3) Spatial finiteness       -> Undecided.  Curvature is observed near-flat; compatible with a finite
          OR an infinite universe — observation does not decide.
      (4) Lambda value             -> NotDerived.  The observed cosmological constant is ~10^-122 in Planck
          units; GravityFinitization.v only proves an O(1) per-mode bound — many orders of magnitude away.
      (5) Holographic information   -> SupportsFinite (theoretical).  The Bekenstein bound S <= A/4 says a
          finite region holds a FINITE, definite amount of information — finite actuality.  (HONEST: this is
          theoretical consensus, not a direct measurement.)

    -- The honest synthesis --
      Nature AFFIRMS finite actuality where it has been tested at the observable level (quantization) and in
      holographic finiteness, but REFUTES the naive regular-lattice SUBSTRATE (Fermi-LAT), and leaves the
      deepest cosmological questions (spatial finiteness, Lambda) open.  So the empirical check SELECTS the
      Lorentz-invariant (causal-set-like, Sorkin) realization of P4 and REJECTS the preferred-frame lattice.
      Checking nature does not crown ToS — it disciplines it.  The finitization "furniture" cannot be a
      regular lattice.

    Elements: the real numbers — Fermi-LAT 6/5 bound vs naive 1; hydrogen 1/4; the O(1) vs ~10^-122 gap
    Roles:    each window plays a verdict; observable-finiteness (affirmed) vs substrate-discreteness (lattice refuted)
    Rules:    confront prediction with observation; the check disciplines (can refute), it does not crown

    ============ E/R/R разбор ============
      Rules (L5): правило конфронтации — для каждого окна вердикт {Element / role-limit / не определено /
                  не выведено}; проверка НЕ коронует теорию, она ДИСЦИПЛИНИРУЕТ (вплоть до опровержения).
      Roles (L4): квантование+голография => подтверждает конечную сторону; Lorentz-дисперсия (Fermi-LAT) =>
                  опровергает наивную решётку; конечность пространства => не определено; Lambda => не выведено.
                  Различение: конечность НАБЛЮДАЕМЫХ (подтверждено) != дискретность СУБСТРАТА (решётка опров.).
      Elements  : реальные числа — Fermi-LAT 6/5 против наивного 1; водород 1/4; O(1) против ~10^-122.
    ДИАГНОСТИКА (P4): природа ПОДТВЕРЖДАЕТ конечную актуальность на уровне наблюдаемых и в голографии, но
    ОПРОВЕРГАЕТ наивную регулярную решётку (Fermi-LAT) на уровне субстрата.  Жизнеспособная финитизация =
    Lorentz-инвариантная (causal-set).  Космология открыта.  Проверка ДИСЦИПЛИНИРУЕТ, не коронует:
    «мебель» финитизации не может быть регулярной решёткой.

    STATUS: 11 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa List.
Import ListNotations.

Local Open Scope Q_scope.

(* ===================================================================== *)
(*  The windows and their verdicts                                         *)
(* ===================================================================== *)

Inductive Window :=
  | ObservableQuantization   (* atomic spectra, angular momentum: discrete *)
  | LorentzDispersion        (* Fermi-LAT GRB photon time-of-flight *)
  | SpatialFiniteness        (* is the universe spatially finite? *)
  | LambdaValue              (* the ~10^-122 cosmological constant *)
  | HolographicInfo.         (* Bekenstein finite information *)

Inductive Verdict :=
  | SupportsFinite           (* nature sits on the Element side here *)
  | RefutesNaiveLattice      (* nature rejects the regular-lattice realization of P4 *)
  | Undecided
  | NotDerived.

Definition verdict (w : Window) : Verdict :=
  match w with
  | ObservableQuantization => SupportsFinite
  | LorentzDispersion      => RefutesNaiveLattice
  | SpatialFiniteness      => Undecided
  | LambdaValue            => NotDerived
  | HolographicInfo        => SupportsFinite
  end.

Lemma verdicts_assigned :
  verdict ObservableQuantization = SupportsFinite
  /\ verdict LorentzDispersion = RefutesNaiveLattice
  /\ verdict SpatialFiniteness = Undecided
  /\ verdict LambdaValue = NotDerived
  /\ verdict HolographicInfo = SupportsFinite.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Window 2 — the sharpest tooth: Fermi-LAT REFUTES the naive lattice      *)
(* ===================================================================== *)

(** A naive regular spatial lattice puts the quantum-gravity scale AT the Planck mass: ratio = 1. *)
Definition naive_lattice_ratio : Q := 1.

(** Fermi-LAT GRB 090510 (Abdo et al., Nature 2009): observed M_QG,1 / M_Planck > 1.2 = 6/5. *)
Definition fermi_lower_bound : Q := 12 # 10.

(** The naive value lies BELOW the observed floor. *)
Lemma naive_lattice_excluded : naive_lattice_ratio < fermi_lower_bound.
Proof. unfold naive_lattice_ratio, fermi_lower_bound. vm_compute. reflexivity. Qed.

(** ...so the regular-lattice realization of P4 is RULED OUT (predicted below the observed floor). *)
Lemma naive_lattice_ruled_out : ~ (fermi_lower_bound <= naive_lattice_ratio).
Proof. apply Qlt_not_le. exact naive_lattice_excluded. Qed.

(* ===================================================================== *)
(*  Window 1 — observed quantization is Element-side (rational, discrete)   *)
(* ===================================================================== *)

(** Hydrogen bound-state energies E_n ~ -1/n^2: the observed spectrum is DISCRETE with RATIONAL ratios.
    E_2/E_1 = (1/2)^2 = 1/4 — Element side at the level of observables. *)
Definition hydrogen_ratio_2_1 : Q := (1 # 2) * (1 # 2).

Lemma hydrogen_ratio_rational : hydrogen_ratio_2_1 == 1 # 4.
Proof. unfold hydrogen_ratio_2_1. vm_compute. reflexivity. Qed.

(** SHO ladder gaps are the exact integer sequence 2n+1 (observed, structural) — counted = Element. *)
Definition sho_gap (n : nat) : Q := inject_Z (Z.of_nat (2 * n + 1)%nat).

Lemma sho_gap_0 : sho_gap 0 == 1.
Proof. unfold sho_gap. vm_compute. reflexivity. Qed.

Lemma sho_gap_1 : sho_gap 1 == 3.
Proof. unfold sho_gap. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Window 4 — Lambda NOT derived; Window 5 — holographic finiteness        *)
(* ===================================================================== *)

(** The O(1) per-mode vacuum bound (1/2, from GravityFinitization.v) is nowhere near the observed
    ~10^-122 — not even as small as 10^-6.  So Lambda's value is NOT explained. *)
Lemma lambda_not_explained : ~ ((1 # 2) <= (1 # 1000000)).
Proof. apply Qlt_not_le. vm_compute. reflexivity. Qed.

(** Bekenstein bound S <= A/4: a finite region holds a FINITE, definite amount of information.
    (Theoretical consensus, not a direct measurement.)  Area 4 -> entropy 1. *)
Definition bekenstein (A : Q) : Q := A / 4.

Lemma bekenstein_finite : bekenstein 4 == 1.
Proof. unfold bekenstein. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  The ledger balance                                                     *)
(* ===================================================================== *)

Definition all_windows : list Window :=
  [ObservableQuantization; LorentzDispersion; SpatialFiniteness; LambdaValue; HolographicInfo].

Definition is_supports (w : Window) : bool :=
  match verdict w with SupportsFinite => true | _ => false end.
Definition is_refutes (w : Window) : bool :=
  match verdict w with RefutesNaiveLattice => true | _ => false end.

Definition n_supports : nat := length (filter is_supports all_windows).
Definition n_refutes  : nat := length (filter is_refutes all_windows).

Lemma n_supports_eq : n_supports = 2%nat.
Proof. reflexivity. Qed.

Lemma n_refutes_eq : n_refutes = 1%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: nature disciplines the boundary                              *)
(* ===================================================================== *)

(** The confrontation, in one statement:
      (observables)  the observed spectrum is quantized with rational ratios (E_2/E_1 = 1/4) — Element side;
      (substrate)    the naive regular lattice is REFUTED by Fermi-LAT (predicted ratio 1 < observed 6/5);
      (Lambda)       the O(1) vacuum bound is nowhere near the observed ~10^-122 — not derived;
      (balance)      a MIXED ledger: 2 windows support the finite side, 1 refutes the naive lattice, 2 open.
    Nature affirms finite actuality at the observable level but rejects the preferred-frame lattice
    realization of P4 — the viable finitization is Lorentz-invariant (causal-set-like).  The empirical
    check DISCIPLINES the theory; it does not crown it. *)
Theorem nature_disciplines_boundary :
  hydrogen_ratio_2_1 == 1 # 4
  /\ ~ (fermi_lower_bound <= naive_lattice_ratio)
  /\ ~ ((1 # 2) <= (1 # 1000000))
  /\ n_supports = 2%nat
  /\ n_refutes = 1%nat.
Proof.
  split; [ exact hydrogen_ratio_rational | ].
  split; [ exact naive_lattice_ruled_out | ].
  split; [ exact lambda_not_explained | ].
  split; [ exact n_supports_eq | exact n_refutes_eq ].
Qed.
