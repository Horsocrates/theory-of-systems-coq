(** * FinitizationPrinciple.v — ③ INTEGRATION: the finitization boundary is ONE
      principle across all arenas, not a list of separate results.  And the deep
      payoff: the finitization boundary COINCIDES with the constructivity boundary.

    Elements: the 0-axiom demarcation theorems of each arena (kinematic ①,
              information ②, higher-dimensional ④, operator) — the constructive,
              Element-side results (L1 + P4)
    Roles:    "arena" = a role the one boundary plays; "principle" = the role that
              unifies the arenas; the constructive vs classical split = the logical
              shadow of the Element vs role-limit split
    Rules:    in EVERY arena a TERMINATION CRITERION (L5) sorts objects into Element
              (terminating process) vs role-limit (non-terminating), with NOTHING
              between — the same dichotomy, different engines

    ONE PRINCIPLE, NOT SIX RESULTS.  The cluster's demarcations look separate but are
    one P4 boundary in six arenas:
      ① kinematics  : an orbit closes (Z₄) vs never closes (3-4-5; √2,√3)
      ② information : probability is rational (½, Σp²) vs amplitude is a role-limit (√2)
      ④ higher dim  : the trace-orbit closes (orders {1,2,3,4,6}) vs not (icosahedron; √5)
      operator      : [A,B]=c·I forces c=0 in finite N — quantum iℏ is a role-limit
                      (here the 2×2 trace obstruction; general N: no_finite_ccr,
                       process/ProcessCanonicalCommutator.v)
      spectral      : the spectrum is discrete (enumerable) or continuous (Cantor),
                      NOTHING between (physics/SpectralDichotomy.v — uses PCH)
      continuum     : a process terminates (rational approximants) vs the √2-process /
                      the uncountable [0,1] (ShrinkingIntervals_ERR.v — uses classic)

    "NOTHING BETWEEN" = a dichotomy in every arena.  The spectral dichotomy's "no
    intermediate cardinality" is NOT a separate fact — it is the SAME "nothing
    between" as FinitizationBoundary.v.  The finitization boundary IS a dichotomy,
    everywhere; the spectral version is its sharpest form.

    ★ THE FINITIZATION BOUNDARY = THE CONSTRUCTIVITY BOUNDARY.  Observe the axiom
    bookkeeping: ①②④ and the operator obstruction are 0-AXIOM (constructive — this
    file's `Print Assumptions` is "Closed under the global context").  The spectral
    dichotomy and the uncountability of [0,1] use `classic` (L3) + `L4_witness` (L4),
    inherited from the Process Continuum Hypothesis.  This is no accident: LEM is
    needed EXACTLY to speak of the completed continuum — the role-limit / non-
    terminating side (a perfect subset, an uncountable set).  The terminating
    (Element) side is constructive, axiom-free.  So the SAME line divides ontology
    (Element / role-limit), logic (constructive / classical), and spectra (discrete /
    continuous).  This file stays 0-axiom precisely BECAUSE it bundles only the
    Element-side arenas — its own axiom status is a witness to the principle.

    ============ E/R/R разбор ============
      Rules (L5): в каждой арене свой критерий завершаемости, но форма ОДНА —
                  дихотомия без промежутка.
      Roles (L4): «арена» = роль границы; «принцип» = объединяющая роль; конструктивно/
                  классически = логическая тень Element/role-limit.
      Elements  : 0-аксиомные демаркации арен (конструктивная, Element-сторона).
    ДИАГНОСТИКА (P4): ③ = P4-граница, поднятая в МЕТА-теорему поперёк арен. Её логический
    след — граница КОНСТРУКТИВНОСТИ: 0-аксиомные результаты = Element-сторона; теоремы,
    требующие L3+L4 (PCH: спектр, несчётность) = role-limit/континуум-сторона. Одна линия
    делит онтологию, логику и спектр. Файл 0-аксиом — сам свидетель принципа.

    STATUS: 2 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.NivenGeneral.
From ToS Require Import stdlib.WalshQuantum.
From ToS Require Import analysis.Sqrt2Irrational.
From ToS Require Import stdlib.GaussianMUB.
From ToS Require Import stdlib.CliffordCapstone.
From ToS Require Import stdlib.CrystallographicRestriction.
Open Scope Q_scope.

(* ===================================================================== *)
(*  Operator arena (local 2×2 representative of no_finite_ccr)           *)
(* ===================================================================== *)

(** The canonical commutator is a role-limit: the two diagonal entries of any 2×2
    commutator are negatives of each other (trace 0), so [A,B] = c·I forces c = 0.
    The quantum [q̂,p̂] = iℏ·I (c ≠ 0) has NO finite realisation.  General N:
    `no_finite_ccr` (process/ProcessCanonicalCommutator.v), same trace argument. *)
Lemma operator_role_limit_2x2 :
  forall a12 a21 b12 b21 c : Q,
    a12*b21 - a21*b12 == c -> a21*b12 - a12*b21 == c -> c == 0.
Proof. intros a12 a21 b12 b21 c H1 H2. lra. Qed.

(* ===================================================================== *)
(*  ★ THE GRAND FINITIZATION PRINCIPLE (the 0-axiom arenas, in one)       *)
(* ===================================================================== *)

(** One boundary, four constructive arenas, bundled.  Each clause is a headline
    demarcation from the cluster; together they are the P4 finitization boundary
    made into a single machine-checked statement.  0 axioms — by which this file
    itself witnesses that the Element side is the constructive side. *)
Theorem finitization_principle :
  (* ① kinematic Element: the Z₄ rotations close *)
  (fst (cpow (1, 0) 1) == 1 /\ fst (cpow (-1, 0) 2) == 1 /\
   fst (cpow (0, 1) 4) == 1 /\ fst (cpow (0, -1) 4) == 1)
  /\
  (* ① kinematic role-limit: the 3-4-5 rotation never closes (Niven) *)
  (forall k : nat, ~ (5 | c 6 5 (S k))%Z)
  /\
  (* ② information: amplitude is a role-limit (√2∉ℚ), probability an Element (½) *)
  ((~ exists r : Q, r * r == 2) /\
   (born e0 w0 == 1#2 /\ born e0 w1 == 1#2 /\ born e1 w0 == 1#2 /\ born e1 w1 == 1#2))
  /\
  (* ② information invariant: the 3-MUB collision sum is the rational 2 *)
  (forall u : qst, ~ (nrm u == 0) -> coll_Z u + coll_X u + coll_Y u == 2)
  /\
  (* ④ higher-dim role-limit: order 5 / the icosahedron is excluded (√5) *)
  (~ exists x : Q, tau x 5 == 2 /\ ~ (x == 2))
  /\
  (* ④ higher-dim Element: orders {1,2,3,4,6} are realised *)
  (tau 2 1 == 2 /\ tau (-2) 2 == 2 /\ tau (-1) 3 == 2 /\ tau 0 4 == 2 /\ tau 1 6 == 2)
  /\
  (* operator role-limit: [A,B]=c·I forces c=0 (finite dimension) *)
  (forall a12 a21 b12 b21 c : Q,
     a12*b21 - a21*b12 == c -> a21*b12 - a12*b21 == c -> c == 0).
Proof.
  split; [ exact Z4_terminates |].
  split; [ exact rotation_345_aperiodic |].
  split; [ split; [ exact sqrt2_not_in_Q | exact walsh_complementarity ] |].
  split; [ exact mub_sum_rule_3 |].
  split; [ exact no_rational_order5 |].
  split; [ exact realizable_orders |].
  exact operator_role_limit_2x2.
Qed.
