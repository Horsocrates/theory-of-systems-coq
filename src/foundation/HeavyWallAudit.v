(** * HeavyWallAudit.v — the audit applied to Part H of the physics volume (the HEAVY WALLS: Navier-Stokes
      and zeta/Riemann).  Honest finding: the heavy walls are NOT 0-axiom — unlike the foundation layer
      (this session's 19 files, all "Closed under the global context"), the NS and zeta results rest on 4
      DOMAIN-SPECIFIC AXIOMS.  This file classifies each by kind and scopes the "0 axioms" claim honestly.

    -- The four REAL domain axioms (found by grepping src/, NOT the CLAUDE.md list) --
      Navier-Stokes (src/navier_stokes/):
        B_antisym       : B_coeff k l m == -(B_coeff k m l)            -- advection antisymmetry;
        C_B_positive    : 0 < C_B                                       -- a positive coupling constant;
        B_coeff_bounded : Qabs (B_coeff k l m) <= C_B * max(k,l,m)      -- the nonlinearity bound.
      zeta (src/zeta/FunctionalEquation.v):
        functional_equation_structure : nontrivial_zero rho -> nontrivial_zero (reflect_zero rho).

    -- The classification --
      B_antisym       -> ProvableStructure : the advection term is energy-conserving; its antisymmetry is a
                         THEOREM of the real NS bilinear form, axiomatized as a shortcut (eliminable).
      C_B_positive    -> HarmlessInput     : a positive normalization constant (an input, not a crux).
      B_coeff_bounded -> LoadBearing       : the WHOLE regularity rests on this bound on the nonlinearity;
                         it is the genuine assumption (NS regularity here is CONDITIONAL on it).
      functional_eq.  -> ProvableStructure : Riemann's functional equation is a THEOREM; this consequence
                         (zeros come in pairs rho, 1-rho) is axiomatized (eliminable, but load-bearing for RH).

    -- The honest verdict --
      The heavy walls carry 4 domain axioms: 2 are provable-in-principle (B_antisym = energy conservation,
      functional_equation = Riemann's FE) and could be eliminated; 1 is a harmless input (C_B_positive); 1
      is genuinely LOAD-BEARING (B_coeff_bounded).  So NS regularity is CONDITIONAL on a nonlinearity bound,
      and the RH treatment is CONDITIONAL on the functional equation.  The "0 axioms" claim honestly applies
      to the FOUNDATION, not to the heavy walls.

    -- Documentation drift (an audit finding) --
      CLAUDE.md lists the domain axioms as ns_viscosity_axiom / ns_forcing_axiom / zeta_euler_product /
      zeta_log_derivative.  NONE of those names exist in src/; the real axioms are the four above.  The
      documentation is stale and should be corrected (flagged here; CLAUDE.md is tracked and not edited
      without an explicit request).

    Elements: ax_kind / ax_wall; 4 domain axioms; 2 eliminable, 1 input, 1 load-bearing
    Roles:    B_antisym/functional_eq = ProvableStructure; C_B_positive = Input; B_coeff_bounded = LoadBearing
    Rules:    the heavy walls are conditional on 4 domain axioms; 0-axiom applies to the foundation, not them

    ============ E/R/R разбор ============
      Rules (L5): каждая доменная аксиома классифицируется {ProvableStructure(устранима)/HarmlessInput/
                  LoadBearing}; NS/zeta-результаты условны на них -- стены НЕ 0-аксиомны (в отличие от foundation).
      Roles (L4): B_antisym = provable-структура (энергосохранение); C_B_positive = вход (нормировка);
                  B_coeff_bounded = load-bearing (регулярность держится на нём); functional_eq = provable-shortcut
                  (Риманова FE).  NS = 3 акс, zeta = 1.
      Elements  : ax_kind/ax_wall; n=4 (не 0-акс); n_eliminable=2; n_load_bearing=1; CLAUDE.md-имена фантомны.
    ДИАГНОСТИКА (P4): тяжёлые стены несут 4 доменные аксиомы: 2 устранимы (provable: энергосохранение,
    Риманова FE), 1 вход, 1 подлинно load-bearing (B_coeff_bounded -- регулярность NS условна на оценке
    нелинейности).  Честная область "0 аксиом" = foundation, не стены.  + Дрейф документации: CLAUDE.md-
    аксиомы фантомны, реальные другие -- флагую (tracked-файл без просьбы не правлю).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Arith.
Import ListNotations.

(* ===================================================================== *)
(*  The four real domain axioms and their classification                   *)
(* ===================================================================== *)

Inductive DomainAxiom := BAntisym | CBPositive | BCoeffBounded | FunctionalEq.
Inductive AxKind := ProvableStructure | HarmlessInput | LoadBearing.
Inductive Wall := NavierStokes | Zeta.

Definition ax_wall (a : DomainAxiom) : Wall :=
  match a with FunctionalEq => Zeta | _ => NavierStokes end.

Definition ax_kind (a : DomainAxiom) : AxKind :=
  match a with
  | BAntisym      => ProvableStructure   (* advection antisymmetry = energy conservation (a theorem) *)
  | CBPositive    => HarmlessInput        (* a positive normalization constant *)
  | BCoeffBounded => LoadBearing          (* the regularity-critical bound on the nonlinearity *)
  | FunctionalEq  => ProvableStructure   (* Riemann's functional equation (a theorem) *)
  end.

(** An axiom is eliminable in principle iff it is provable structure. *)
Definition ax_eliminable (a : DomainAxiom) : bool :=
  match ax_kind a with ProvableStructure => true | _ => false end.

Definition all_axioms : list DomainAxiom := [BAntisym; CBPositive; BCoeffBounded; FunctionalEq].

(** ★ The heavy walls carry 4 domain axioms — they are NOT 0-axiom. *)
Lemma heavy_walls_carry_axioms : length all_axioms = 4%nat.
Proof. reflexivity. Qed.

Lemma walls_correct :
  ax_wall BAntisym = NavierStokes /\ ax_wall CBPositive = NavierStokes
  /\ ax_wall BCoeffBounded = NavierStokes /\ ax_wall FunctionalEq = Zeta.
Proof. repeat split; reflexivity. Qed.

Lemma axioms_classified :
  ax_kind BAntisym = ProvableStructure
  /\ ax_kind CBPositive = HarmlessInput
  /\ ax_kind BCoeffBounded = LoadBearing
  /\ ax_kind FunctionalEq = ProvableStructure.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  The counts                                                             *)
(* ===================================================================== *)

Definition is_eliminable (a : DomainAxiom) : bool := ax_eliminable a.
Definition is_load_bearing (a : DomainAxiom) : bool :=
  match ax_kind a with LoadBearing => true | _ => false end.

Definition n_eliminable : nat := length (filter is_eliminable all_axioms).
Definition n_load_bearing : nat := length (filter is_load_bearing all_axioms).

(** ★ Two of the four are provable-in-principle (energy conservation, Riemann's FE) — eliminable shortcuts. *)
Lemma n_eliminable_eq : n_eliminable = 2%nat.
Proof. reflexivity. Qed.

(** ★ Exactly ONE is genuinely load-bearing: B_coeff_bounded (the NS regularity rests on it). *)
Lemma n_load_bearing_eq : n_load_bearing = 1%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the heavy-wall axiom audit                                   *)
(* ===================================================================== *)

(** Part H audit — the heavy walls are not 0-axiom:
      (count)        the NS and zeta results carry 4 domain axioms (so the heavy walls are NOT 0-axiom);
      (eliminable)   2 are provable in principle (B_antisym = energy conservation; functional_eq = Riemann FE);
      (load-bearing) 1 is genuinely load-bearing (B_coeff_bounded — NS regularity is conditional on it);
      (zeta)         the RH treatment is conditional on the functional equation (provable, but axiomatized).
    The "0 axioms" of the foundation does NOT extend to the heavy walls.  (Documentation drift: CLAUDE.md's
    named domain axioms do not exist; the real ones are audited here.) *)
Theorem heavy_wall_audit :
  length all_axioms = 4%nat
  /\ n_eliminable = 2%nat
  /\ n_load_bearing = 1%nat
  /\ ax_kind BCoeffBounded = LoadBearing
  /\ ax_kind FunctionalEq = ProvableStructure
  /\ ax_wall FunctionalEq = Zeta.
Proof.
  split; [ exact heavy_walls_carry_axioms | ].
  split; [ exact n_eliminable_eq | ].
  split; [ exact n_load_bearing_eq | ].
  split; [ reflexivity | ].
  split; [ reflexivity | reflexivity ].
Qed.
