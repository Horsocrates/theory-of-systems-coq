(** * AdvectionEnergyConservation.v — DESCENT: the energy-conservation content of the
      Navier-Stokes axiom `B_antisym` (GalerkinSystem.v) is a 0-AXIOM THEOREM of our base,
      derived from discrete summation-by-parts / telescoping (FiniteDifference.v), NOT postulated.

   Reading 2 of NS (Galerkin regularity) rides on 3 domain axioms; one of them, `B_antisym`
   (the advection term conserves energy: B(k,l,m) = -B(k,m,l) => triple_sum = 0), is the ELIMINABLE
   one.  Here we DESCEND to where the base actually grounds it: the discrete derivative `fd` and the
   summation-by-parts identity `abel_self_periodic` / telescoping `sum_fd` (both 0-axiom in
   FiniteDifference.v).  We prove that the energy flux of discrete transport (quadratic) and of the
   discrete Burgers advection (cubic -- the direct analogue of `triple_sum = 0`) VANISHES for
   periodic fields, purely by telescoping.  So energy conservation is DERIVED, not postulated.

   -- transport flux (u_i + u_{i+1}) * fd(u)_i = fd(u^2)_i  => sum = u(N)^2 - u(0)^2 = 0 (periodic).
      This IS discrete summation-by-parts: it equals `abel_self_periodic` (see transport_via_abel).
   -- Burgers flux (u_i^2 + u_i u_{i+1} + u_{i+1}^2) * fd(u)_i = fd(u^3)_i  => sum = 0 (periodic).
      Cubic telescoping (a^2+ab+b^2)(b-a) = b^3-a^3; the direct grid analogue of triple_sum = 0.

   HONEST SCOPE (the break-off).  This DEMONSTRATES the descent for the ENERGY side (B_antisym's
   content) in physical (grid) space; it does NOT rebuild the full GalerkinSystem modal coupling
   (that needs a spectral mode<->grid bridge, absent in the base).  And it does NOT touch the OTHER
   axiom, `B_coeff_bounded` (the cascade magnitude / the alpha=2 wall): that is the genuine
   BREAK-OFF -- a structure-grounded hypothesis (the one-derivative scaling of advection) entangled
   with Reading 1 (the classical Clay statement).  This file closes only the ELIMINABLE half,
   honestly; the load-bearing half stays open.  We deliberately do NOT import GalerkinSystem (it
   carries the axioms) -- this file is 0-axiom on the GridFunction/FiniteDifference substrate alone.

   Elements: grid field u : nat -> Q; the transport flux; the Burgers flux; periodicity.
   Roles:    energy densities u^2 (quadratic) and u^3 (cubic) as conserved potentials; fd = the
             discrete derivative; periodicity = boundary closure.
   Rules:    conservation = telescoping: each flux term is fd(potential)_i, so the sum collapses to
             potential(N) - potential(0) = 0 for periodic (= discrete summation-by-parts / abel).

   ============ E/R/R разбор ============
     Rules (L5): сохранение = телескопирование: член потока = fd(плотность) => Σ = плотн(N)-плотн(0)=0
                 для периодических (= суммирование по частям / abel_self_periodic).
     Roles (L4): плотности u^2 (квадрат) и u^3 (куб) -- сохраняемые потенциалы; fd -- дискр. производная;
                 периодичность -- замыкание границы.
     Elements  : поле u:nat->Q; транспортный поток; бюргерсов поток; периодичность.
   ДИАГНОСТИКА (P4): СПУСК. Содержание постулата B_antisym (нелинейность сохраняет энергию) <=
   sum_fd/abel (substrate, 0-акс) -- ВЫВОД, не постулат. ЧЕСТНО: это лишь устранимая половина
   (энергия); B_coeff_bounded (каскад/стена alpha=2) -- ОБРЫВ базы, сцеплен с Reading 1, здесь не трогается.

   STATUS: 7 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith QArith.Qabs Lia ZArith.
From Stdlib Require Import Lqa.
From ToS Require Import navier_stokes.GridFunction.
From ToS Require Import navier_stokes.FiniteDifference.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Summation is extensional (congruence under pointwise equality)         *)
(* ===================================================================== *)

Lemma sum_ns_congr : forall (f g : nat -> Q) N,
  (forall i, f i == g i) -> sum_Q_ns f N == sum_Q_ns g N.
Proof.
  intros f g N H. induction N as [|n IH].
  - simpl. reflexivity.
  - rewrite !sum_ns_S. rewrite IH. rewrite (H n). reflexivity.
Qed.

(* ===================================================================== *)
(*  The two advection energy fluxes (physical / grid space)                *)
(* ===================================================================== *)

(** Transport (linear advection) energy flux: density weight = u_i + u_{i+1}. *)
Definition energy_flux_transport (u : grid_fn) (i : nat) : Q :=
  (u i + u (S i)) * fd u i.

(** Burgers (nonlinear advection) energy flux: weight = u_i^2 + u_i u_{i+1} + u_{i+1}^2. *)
Definition energy_flux_burgers (u : grid_fn) (i : nat) : Q :=
  (u i * u i + u i * u (S i) + u (S i) * u (S i)) * fd u i.

(* ===================================================================== *)
(*  Each flux term is a discrete derivative of an energy density           *)
(* ===================================================================== *)

(** ★ Transport flux telescopes: (u_i + u_{i+1})*fd(u)_i = fd(u^2)_i = u_{i+1}^2 - u_i^2. *)
Lemma transport_flux_telescopes : forall (u : grid_fn) i,
  energy_flux_transport u i == fd (fun j => u j * u j) i.
Proof. intros. unfold energy_flux_transport, fd. cbv beta. ring. Qed.

(** ★ Burgers flux telescopes: (u_i^2+u_i u_{i+1}+u_{i+1}^2)*fd(u)_i = fd(u^3)_i = u_{i+1}^3-u_i^3. *)
Lemma burgers_flux_telescopes : forall (u : grid_fn) i,
  energy_flux_burgers u i == fd (fun j => u j * u j * u j) i.
Proof. intros. unfold energy_flux_burgers, fd. cbv beta. ring. Qed.

(* ===================================================================== *)
(*  Conservation: the energy flux sums to zero for periodic fields         *)
(* ===================================================================== *)

(** ★ TRANSPORT conserves energy: for periodic u, the transport energy flux sums to 0.
    Derived by telescoping (= the discrete fundamental theorem of calculus, `sum_fd`). *)
Theorem transport_conserves_energy : forall (u : grid_fn) N,
  is_periodic N u ->
  sum_Q_ns (energy_flux_transport u) N == 0.
Proof.
  intros u N Hper. unfold is_periodic in Hper.
  rewrite (sum_ns_congr (energy_flux_transport u)
                        (fd (fun j => u j * u j)) N (transport_flux_telescopes u)).
  rewrite sum_fd. cbv beta. rewrite Hper. ring.
Qed.

(** The transport energy flux IS discrete summation-by-parts: it equals `abel_self_periodic`
    (the generator we descended to). This exhibits the образующая explicitly. *)
Lemma transport_via_abel : forall (u : grid_fn) N,
  is_periodic N u ->
  sum_Q_ns (fun i => fd u i * u i) N
  == - sum_Q_ns (fun i => u (S i) * fd u i) N.
Proof. intros u N Hper. exact (abel_self_periodic N u Hper). Qed.

(** ★ BURGERS (nonlinear advection) conserves energy: for periodic u, the cubic energy flux
    sums to 0. This is the direct grid analogue of GalerkinSystem's `triple_sum = 0`
    (the content of the axiom `B_antisym`) -- here DERIVED, 0-axiom, by cubic telescoping. *)
Theorem burgers_conserves_energy : forall (u : grid_fn) N,
  is_periodic N u ->
  sum_Q_ns (energy_flux_burgers u) N == 0.
Proof.
  intros u N Hper. unfold is_periodic in Hper.
  rewrite (sum_ns_congr (energy_flux_burgers u)
                        (fd (fun j => u j * u j * u j)) N (burgers_flux_telescopes u)).
  rewrite sum_fd. cbv beta. rewrite Hper. ring.
Qed.

(* ===================================================================== *)
(*  Capstone: advection energy conservation is DERIVED, not postulated     *)
(* ===================================================================== *)

(** The descent result:
      (transport) the linear-transport energy flux vanishes for periodic fields;
      (Burgers)   the nonlinear-advection (cubic) energy flux vanishes -- the grid analogue of
                  `triple_sum = 0`, the content postulated by `B_antisym` in GalerkinSystem.v.
    Both are DERIVED from the 0-axiom substrate (telescoping `sum_fd` / summation-by-parts
    `abel_self_periodic`).  The energy-conservation postulate is thus a theorem of our base.
    NOT addressed (the honest break-off): `B_coeff_bounded` (cascade magnitude / alpha=2 wall),
    which is entangled with Reading 1. *)
Theorem advection_energy_conservation_derived : forall (u : grid_fn) N,
  is_periodic N u ->
  sum_Q_ns (energy_flux_transport u) N == 0
  /\ sum_Q_ns (energy_flux_burgers u) N == 0.
Proof.
  intros u N Hper. split.
  - exact (transport_conserves_energy u N Hper).
  - exact (burgers_conserves_energy u N Hper).
Qed.
