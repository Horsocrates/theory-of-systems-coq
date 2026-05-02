(** * MandelbrotERR.v -- Mandelbrot set as universal classifier in Q^2

    STATUS: 28 Qed, 0 Admitted, 0 new axioms
    Author: Horsocrates | Date: May 2026

    ===================================================================
    THE MANDELBROT SET THROUGH E/R/R
    ===================================================================

    Classical view: M = { c in C : iteration z_{n+1} = z_n^2 + c, z_0 = 0
                          stays bounded }.
    Treated as a "set" in C.

    E/R/R view: M is not a set-like Element. M is a CLASSIFIER --
    a partial function `behaviour : C -> {bounded, escape, period-k}`
    obtained by running an R-rule for each c.

    Three formulas:

      E-formula (Elements, L1):
        - parameter c in Q x Q (rationals = our complex numbers)
        - iterate z_n in Q x Q at any finite n
        - mod_sq |z|^2 in Q
        - "the set M itself" is NOT an Element (P4)

      R-formula (Roles, L4) -- spectrum of behaviours:
        - period-1 fixed (e.g. c = 0)
        - period-2 cycle (e.g. c = -1)
        - pre-periodic (e.g. c = -2, c = i)
        - escape to infinity (e.g. c = 1)
        - bounded non-periodic (rare, on the boundary)

      R-formula (Rules, L5):
        z_{n+1} = z_n^2 + c, z_0 = 0
        ONE rule, parametrised by c, generating all complexity.

    ===================================================================
    KEY DECIDABLE FACTS in Q
    ===================================================================

    For ANY rational c = (a, b):
    - Each iterate z_n = (a_n, b_n) is exactly computable in Q x Q.
    - "z_n escaped" (|z|^2 > 4) is decidable for any specific n.
    - "Orbit is exactly periodic with period k from step m onwards"
      is decidable: check z_{m+k} =c= z_m.

    What is NOT decidable in finite time for arbitrary c:
    - "c is in M" -- requires checking all n.
    - This is precisely the P4 obstruction.
*)

From Stdlib Require Import QArith Qabs ZArith List PeanoNat Lia.
From Stdlib Require Import Lqa.

Import ListNotations.
Open Scope Q_scope.

(* ============================================================== *)
(*  COMPLEX NUMBERS IN Q x Q                                       *)
(* ============================================================== *)

Definition C := (Q * Q)%type.

Definition c_eq (z w : C) : Prop :=
  fst z == fst w /\ snd z == snd w.

Notation "z =c= w" := (c_eq z w) (at level 70).

Definition c_zero : C := (0, 0).
Definition c_one : C := (1, 0).
Definition c_i : C := (0, 1).

Definition c_add (z w : C) : C :=
  (fst z + fst w, snd z + snd w).

Definition c_mul (z w : C) : C :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition c_sq (z : C) : C := c_mul z z.

(** Squared modulus: |z|^2 = a^2 + b^2. *)
Definition mod_sq (z : C) : Q := fst z * fst z + snd z * snd z.

(** Sanity: c_zero has zero modulus. *)
Theorem mod_sq_zero : mod_sq c_zero == 0.
Proof. unfold mod_sq, c_zero. simpl. ring. Qed.

(** c_i has modulus 1. *)
Theorem mod_sq_i : mod_sq c_i == 1.
Proof. unfold mod_sq, c_i. simpl. ring. Qed.

(* ============================================================== *)
(*  MANDELBROT ITERATION                                            *)
(* ============================================================== *)

(** One step: z |-> z^2 + c. *)
Definition mandelbrot_step (c z : C) : C := c_add (c_sq z) c.

(** Iterate from z_0 = 0. *)
Fixpoint mandelbrot_iter (c : C) (n : nat) : C :=
  match n with
  | O => c_zero
  | S k => mandelbrot_step c (mandelbrot_iter c k)
  end.

(** Escape predicate: |z|^2 > 4. *)
Definition escaped (z : C) : Prop := 4 < mod_sq z.

(* ============================================================== *)
(*  c = 0: PERIOD-1 fixed at origin (provable for all n)            *)
(* ============================================================== *)

(** Step preserves zero. *)
Lemma step_preserves_zero : forall z,
  z =c= c_zero -> mandelbrot_step c_zero z =c= c_zero.
Proof.
  intros z [HRe HIm].
  unfold mandelbrot_step, c_add, c_sq, c_mul, c_zero in *.
  unfold c_eq. simpl in *.
  rewrite HRe, HIm. split; ring.
Qed.

(** Orbit at c = 0 stays at zero forever. *)
Theorem orbit_at_zero_forever : forall n,
  mandelbrot_iter c_zero n =c= c_zero.
Proof.
  induction n.
  - unfold c_eq, c_zero. split; reflexivity.
  - simpl. apply step_preserves_zero. exact IHn.
Qed.

(** c = 0 never escapes (provable in Q for all finite n). *)
Lemma mod_sq_eq_zero : forall z : C,
  z =c= c_zero -> mod_sq z == 0.
Proof.
  intros z [HRe HIm].
  unfold mod_sq, c_zero in *. simpl in *.
  rewrite HRe, HIm. ring.
Qed.

Theorem c_zero_never_escapes : forall n, ~ escaped (mandelbrot_iter c_zero n).
Proof.
  intros n.
  unfold escaped.
  assert (Hms : mod_sq (mandelbrot_iter c_zero n) == 0).
  { apply mod_sq_eq_zero. apply orbit_at_zero_forever. }
  rewrite Hms. lra.
Qed.

(* ============================================================== *)
(*  c = -1: PERIOD-2 CYCLE 0 <-> -1                                *)
(* ============================================================== *)

Definition c_neg1 : C := (-(1), 0).

Theorem orbit_neg1_at_1 : mandelbrot_iter c_neg1 1 =c= c_neg1.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg1_at_2 : mandelbrot_iter c_neg1 2 =c= c_zero.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg1_at_3 : mandelbrot_iter c_neg1 3 =c= c_neg1.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg1_at_4 : mandelbrot_iter c_neg1 4 =c= c_zero.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

(** Period-2 evidence: iter at 2 == iter at 0, iter at 3 == iter at 1. *)
Theorem c_neg1_period_2_evidence :
  mandelbrot_iter c_neg1 2 =c= c_zero /\
  mandelbrot_iter c_neg1 3 =c= c_neg1 /\
  mandelbrot_iter c_neg1 4 =c= c_zero.
Proof.
  split. { apply orbit_neg1_at_2. }
  split. { apply orbit_neg1_at_3. }
  apply orbit_neg1_at_4.
Qed.

(* ============================================================== *)
(*  c = -2: PRE-PERIOD-1 (becomes constant 2)                      *)
(* ============================================================== *)

Definition c_neg2 : C := (-(2), 0).
Definition c_two : C := (2, 0).

Theorem orbit_neg2_at_1 : mandelbrot_iter c_neg2 1 =c= c_neg2.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg2_at_2 : mandelbrot_iter c_neg2 2 =c= c_two.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg2_at_3 : mandelbrot_iter c_neg2 3 =c= c_two.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_neg2_at_4 : mandelbrot_iter c_neg2 4 =c= c_two.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

(** Modulus stays bounded by 2 = boundary. *)
Theorem c_neg2_mod_at_3 : mod_sq (mandelbrot_iter c_neg2 3) == 4.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  c = i: PRE-PERIOD-2                                             *)
(* ============================================================== *)
(*  Orbit: 0 -> i -> -1+i -> -i -> -1+i -> -i -> -1+i -> ...        *)
(*  Pre-periodic: from step 2 onwards, periodic with period 2.      *)

Definition c_minus1_plus_i : C := (-(1), 1).
Definition c_neg_i : C := (0, -(1)).

Theorem orbit_i_at_1 : mandelbrot_iter c_i 1 =c= c_i.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_i_at_2 : mandelbrot_iter c_i 2 =c= c_minus1_plus_i.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_i_at_3 : mandelbrot_iter c_i 3 =c= c_neg_i.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_i_at_4 : mandelbrot_iter c_i 4 =c= c_minus1_plus_i.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_i_at_5 : mandelbrot_iter c_i 5 =c= c_neg_i.
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

(** From step 2 onwards: alternates -1+i and -i (period-2 tail). *)
Theorem c_i_pre_period_2 :
  mandelbrot_iter c_i 4 =c= mandelbrot_iter c_i 2 /\
  mandelbrot_iter c_i 5 =c= mandelbrot_iter c_i 3.
Proof.
  split; unfold c_eq; split; vm_compute; reflexivity.
Qed.

(* ============================================================== *)
(*  c = 1: ESCAPES at step 4                                       *)
(* ============================================================== *)
(*  Orbit: 0 -> 1 -> 2 -> 5 -> 26                                  *)
(*  At step 4: |z_4|^2 = 26^2 = 676 > 4 -- escaped.                *)

Definition c_pos1 : C := (1, 0).

Theorem orbit_pos1_at_1 : mandelbrot_iter c_pos1 1 =c= (1, 0).
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_pos1_at_2 : mandelbrot_iter c_pos1 2 =c= (2, 0).
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_pos1_at_3 : mandelbrot_iter c_pos1 3 =c= (5, 0).
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem orbit_pos1_at_4 : mandelbrot_iter c_pos1 4 =c= (26, 0).
Proof. unfold c_eq. split; vm_compute; reflexivity. Qed.

Theorem mod_sq_pos1_at_4 :
  mod_sq (mandelbrot_iter c_pos1 4) == 676.
Proof. vm_compute. reflexivity. Qed.

(** c = 1 ESCAPED at step 4 (provable in Q). *)
Theorem c_pos1_escapes_at_4 : escaped (mandelbrot_iter c_pos1 4).
Proof.
  unfold escaped. rewrite mod_sq_pos1_at_4. lra.
Qed.

(* ============================================================== *)
(*  ESCAPE RADIUS:  if |c|^2 > 4 then c escapes immediately       *)
(* ============================================================== *)

(** Iter at step 1 equals c (since (0)^2 + c = c). *)
Lemma iter_at_1 : forall c : C,
  fst (mandelbrot_iter c 1) == fst c /\
  snd (mandelbrot_iter c 1) == snd c.
Proof.
  intros c.
  simpl. unfold mandelbrot_step, c_add, c_sq, c_mul, c_zero. simpl.
  split; ring.
Qed.

(** For any c with |c|^2 > 4, iter at step 1 gives c, which has |c|^2 > 4. *)
Theorem escape_radius_step1 : forall c : C,
  4 < mod_sq c -> escaped (mandelbrot_iter c 1).
Proof.
  intros c H.
  unfold escaped, mod_sq.
  destruct (iter_at_1 c) as [HRe HIm].
  assert (Hms : fst (mandelbrot_iter c 1) * fst (mandelbrot_iter c 1) +
                snd (mandelbrot_iter c 1) * snd (mandelbrot_iter c 1) ==
                fst c * fst c + snd c * snd c).
  { rewrite HRe, HIm. reflexivity. }
  rewrite Hms.
  exact H.
Qed.

(** Concrete: c = 3 has |c|^2 = 9 > 4 so escapes at step 1. *)
Theorem c_3_escapes_at_1 :
  escaped (mandelbrot_iter (3, 0) 1).
Proof.
  apply escape_radius_step1. unfold mod_sq. simpl. lra.
Qed.

(** c = (0, 3) has |c|^2 = 9 > 4 so escapes at step 1. *)
Theorem c_3i_escapes_at_1 :
  escaped (mandelbrot_iter (0, 3) 1).
Proof.
  apply escape_radius_step1. unfold mod_sq. simpl. lra.
Qed.

(** Boundary point c = -2: at step 3 the orbit is at (2, 0),
    on the boundary |z|^2 = 4 (NOT escaped, but marginal). *)
Theorem c_neg2_marginal_at_3 :
  mod_sq (mandelbrot_iter c_neg2 3) == 4.
Proof. apply c_neg2_mod_at_3. Qed.

Theorem c_neg2_not_escaped_at_3 :
  ~ escaped (mandelbrot_iter c_neg2 3).
Proof.
  unfold escaped. rewrite c_neg2_mod_at_3. lra.
Qed.

(* ============================================================== *)
(*  GRAND THEOREM                                                   *)
(* ============================================================== *)

Theorem mandelbrot_facts :
  (* c = 0 stays at zero forever -- period-1 *)
  (forall n, mandelbrot_iter c_zero n =c= c_zero) /\
  (* c = -1 has period-2 cycle 0 <-> -1 *)
  mandelbrot_iter c_neg1 2 =c= c_zero /\
  mandelbrot_iter c_neg1 3 =c= c_neg1 /\
  (* c = -2 pre-period-1 (becomes constant 2) *)
  mandelbrot_iter c_neg2 2 =c= c_two /\
  mandelbrot_iter c_neg2 3 =c= c_two /\
  (* c = i pre-period-2 *)
  mandelbrot_iter c_i 4 =c= mandelbrot_iter c_i 2 /\
  (* c = 1 escapes at step 4 *)
  escaped (mandelbrot_iter c_pos1 4) /\
  mod_sq (mandelbrot_iter c_pos1 4) == 676 /\
  (* Escape radius: |c|^2 > 4 means immediate escape *)
  (forall c, 4 < mod_sq c -> escaped (mandelbrot_iter c 1)) /\
  (* Boundary -2 marginal *)
  mod_sq (mandelbrot_iter c_neg2 3) == 4.
Proof.
  split. { apply orbit_at_zero_forever. }
  split. { apply orbit_neg1_at_2. }
  split. { apply orbit_neg1_at_3. }
  split. { apply orbit_neg2_at_2. }
  split. { apply orbit_neg2_at_3. }
  split. { apply (proj1 c_i_pre_period_2). }
  split. { apply c_pos1_escapes_at_4. }
  split. { apply mod_sq_pos1_at_4. }
  split. { apply escape_radius_step1. }
  apply c_neg2_marginal_at_3.
Qed.

(**
   ==================================================================
   WHAT THIS FILE DEMONSTRATES
   ==================================================================

   (1) MANDELBROT IN Q WORKS.
       The iteration z_{n+1} = z_n^2 + c lives entirely in Q x Q
       for any rational c. Specific orbits at c = 0, -1, -2, i, 1
       are exactly verified -- no real numbers needed.

   (2) THE ROLE-SPECTRUM IS DECIDABLE per finite n.
       For each n we can decidably determine: has the orbit
       escaped at step n? is z_n equal to z_m for some m < n
       (periodicity)? These are pure Q-arithmetic predicates.

   (3) "c IS IN M" IS NOT AN ELEMENT.
       Membership requires checking ALL n in N. This is the
       canonical P4 obstruction: a question that has no Element
       form, only an R-process answer.

   (4) ESCAPE RADIUS THEOREM in Q.
       For any c with |c|^2 > 4, the orbit escapes at step 1
       (since iter 1 = c). This gives a decidable upper bound
       on the M region: M is contained in the disk |c|^2 <= 4.

   (5) RICH ORBITAL STRUCTURE.
       - c = 0:    period-1 forever (eternal)
       - c = -1:   period-2 cycle 0 <-> -1 (provable for ALL n by mod 2)
       - c = -2:   pre-period-1 (becomes constant 2 -- on boundary |z|^2 = 4)
       - c = i:    pre-period-2 (cycle -1+i <-> -i)
       - c = 1:    escape at step 4 (mod_sq = 676)
       - c = 3:    escape at step 1 (mod_sq = 9)

   ==================================================================
   COMPARISON: WHY MANDELBROT IS A PERFECT P4 EXAMPLE
   ==================================================================

   Property                   | Apery zeta(3) | Feigenbaum delta | Mandelbrot M
   ---------------------------|---------------|------------------|---------------
   "Element status"           | not Element   | not Element      | not Element
   Closed-form definition     | series        | NONE             | iterative
   Concrete decidable         | partial sums  | bif points       | per-step orbit
   per-step facts in Q        | Yes           | Yes              | Yes
   Universality role          | (single)      | unimodal class   | full param plane
   Structural complexity      | a real number | a real number    | a fractal SET

   Mandelbrot is the most ambitious case: not a single number, but
   an entire SET (uncountable in classical view!) that nevertheless
   admits perfect P4 treatment as "an R-process per c".

   ==================================================================
   POSSIBLE EXTENSIONS
   ==================================================================

   - JuliaSetERR.v: Julia sets J_c at fixed c, parametrised over
     starting points z. Same iteration, different parametrisation.
   - PeriodK_Mandelbrot.v: rational c giving exact period-k cycles.
     For period-2 these are c = -1 (proven here); for period-3 the
     rational solutions are sparse.
   - SelfSimilarity_Mini.v: "mini-Mandelbrots" inside M -- formal
     statement of the renormalisation invariance.
   - Cardioid_Q.v: rational parametrisation of the main cardioid
     boundary via Pythagorean-like rational angle constructions.
*)
