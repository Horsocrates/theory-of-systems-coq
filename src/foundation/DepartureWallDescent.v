(** * DepartureWallDescent.v — the FIFTH descent (the departure-from-equilibrium factor of the baryon
      asymmetry eta), placing it in the WALL TAXONOMY and testing whether it is a FOURTH wall-type
      (FiniteButUncomputed), distinct from SymmetryChoice (arrow, Born), BareHierarchy (Lambda), and
      HardStructure (the NS bound).

    Scope: this descends into ONE factor of eta = J * sphaleron * departure (three factors).  eta as a whole
    stays open -- the sphaleron factor is role-limit (SphaleronRateDescent.v), the J factor is the
    rational/irrational boundary (CPMagnitudeDescent.v).  Here we classify the DEPARTURE factor only.

    Result: YES -- a fourth type, and it is DEFLATIONARY.  The earlier DepartureDescent.v established that
    the departure is NOT role-limit (unlike the sphaleron's exp): it is a FINITE process that TERMINATES.
    Placed in the taxonomy, that makes it a distinct fourth type whose honest verdict is "NOT a fundamental
    wall -- just uncomputed".  This is honest in BOTH directions: it adds a type AND it removes the departure
    from the count of genuine walls.

    -- Rung 1: not one of the three known types.  Not BareHierarchy (there IS a process/structure), not
       HardStructure (the estimate is not open), not SymmetryChoice (no symmetry selection).

    -- Rung 2: what distinguishes it?  It STABILIZES: a finite process reaches a determined value in finitely
       many steps (dep_terminates, dep_value_determined).  Contrast the sphaleron exp-process, which NEVER
       stabilizes (exp_never_stabilizes) -- role-limit.  Terminating vs non-terminating is the boundary.

    -- Rung 3 (floor): so the "wall" is NOT fundamental.  The value is determined and a terminating process
       reaches it; the gap is effort/arena, not principle.  The deflationary type: FiniteButUncomputed.

    -- Floor / verdict: DepartureSize is a fourth type, distinct from the other three, AND it is not a
       fundamental wall (is_fundamental_wall = false).  The taxonomy now has FOUR types -- one of which is
       not even a genuine wall.  Strongly heterogeneous; definitely not "one wall".

    -- Honest caveat: "not fundamental" = relative to current ToS (termination is established vs the exp; if
       the termination claim failed for the real magnitude it would reclassify).  The model captures the
       structure "a terminating process reaches a determined value".  eta as a whole remains open.

    Elements: dep_process n = min n K (stabilizes); exp_process n = n (never stabilizes); Wall / WallType (4 types)
    Roles:    the departure = a terminating finite process (determined value); the exp = a role-limit process
    Rules:    terminating (departure) vs non-terminating (sphaleron) is the boundary; FiniteButUncomputed =/= wall

    ============ E/R/R разбор ============
      Rules (L5): departure ТЕРМИНИРУЕТ (конечный процесс достигает значения), контраст -- сфалеронный exp
                  не терминирует (role-limit); граница = терминирует vs нет.
      Roles (L4): departure = терминирующий конечный процесс (определённое значение) = FiniteButUncomputed
                  (дефляционный, не фунд. стена); exp = role-limit.
      Elements  : dep_process = min n K (стабилизируется на K); exp_process = n (никогда не стабилизируется).
    ДИАГНОСТИКА (P4): 4-й тип -- FiniteButUncomputed, и он ДЕФЛЯЦИОННЫЙ. Не BareHierarchy/HardStructure/
    SymmetryChoice. Значение определено, процесс терминирует -- «стена» = недоделка (арена/усилие), не принцип:
    is_fundamental_wall = false. Честно в обе стороны: добавляет тип И убирает departure из счёта настоящих
    стен. CAVEAT: "не фунд." относительно ToS; eta-в-целом открыт (sphaleron-фактор = role-limit).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia.

(* ===================================================================== *)
(*  Rung 2 — the departure process TERMINATES (a determined value)         *)
(* ===================================================================== *)

(** The determined departure value (a finite, definite magnitude). *)
Definition K_dep : nat := 5.

(** The departure process: it grows, then STABILIZES at K_dep (a finite, terminating computation). *)
Definition dep_process (n : nat) : nat := Nat.min n K_dep.

(** ★ It TERMINATES: for all n past K_dep, the process has reached its determined value and stays. *)
Lemma dep_terminates : forall n, K_dep <= n -> dep_process n = K_dep.
Proof. intros n H. unfold dep_process, K_dep in *. lia. Qed.

(** The value is DETERMINED (reached at the finite step n = K_dep). *)
Lemma dep_value_determined : dep_process K_dep = K_dep.
Proof. unfold dep_process, K_dep. lia. Qed.

(* ===================================================================== *)
(*  Contrast — the sphaleron exp-process NEVER stabilizes (role-limit)     *)
(* ===================================================================== *)

(** A stand-in for the non-terminating sphaleron rate (strictly increasing, never reaching a value). *)
Definition exp_process (n : nat) : nat := n.

(** ★ It NEVER stabilizes -- always changing: this is the role-limit (SphaleronRateDescent), the OPPOSITE
    of the departure.  Terminating (departure) vs non-terminating (sphaleron) is the boundary. *)
Lemma exp_never_stabilizes : forall n, exp_process n <> exp_process (S n).
Proof. intro n. unfold exp_process. lia. Qed.

(* ===================================================================== *)
(*  Floor — the verdict: a FOURTH, DEFLATIONARY wall-type                  *)
(* ===================================================================== *)

Inductive Wall := ArrowSign | BornNorm | LambdaSmallness | NSBound | DepartureSize.
Inductive WallType := SymmetryChoice | BareHierarchy | HardStructure | FiniteButUncomputed.

Definition wall_type (w : Wall) : WallType :=
  match w with
  | ArrowSign      => SymmetryChoice
  | BornNorm       => SymmetryChoice
  | LambdaSmallness => BareHierarchy
  | NSBound        => HardStructure
  | DepartureSize  => FiniteButUncomputed
  end.

(** Is the wall a FUNDAMENTAL obstruction, or just uncomputed?  FiniteButUncomputed is NOT fundamental. *)
Definition is_fundamental_wall (w : Wall) : bool :=
  match wall_type w with FiniteButUncomputed => false | _ => true end.

(** ★ The deflationary verdict: the departure is NOT a genuine wall -- a terminating process reaches its
    value; the gap is effort/arena, not principle. *)
Lemma departure_not_fundamental : is_fundamental_wall DepartureSize = false.
Proof. reflexivity. Qed.

(** ★ DepartureSize is a FOURTH type: distinct from all three of the others. *)
Lemma departure_is_fourth_type :
  wall_type DepartureSize <> wall_type BornNorm
  /\ wall_type DepartureSize <> wall_type LambdaSmallness
  /\ wall_type DepartureSize <> wall_type NSBound.
Proof. repeat split; discriminate. Qed.

(** The genuine walls (the other three types) ARE fundamental; only the departure is not. *)
Lemma genuine_walls_are_fundamental :
  is_fundamental_wall LambdaSmallness = true
  /\ is_fundamental_wall NSBound = true
  /\ is_fundamental_wall BornNorm = true.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the departure-wall descent                                   *)
(* ===================================================================== *)

(** Fifth descent (the departure factor of eta):
      (terminates)  a finite process reaches the determined value (dep_terminates) -- NOT role-limit;
      (contrast)    the sphaleron exp-process NEVER stabilizes (role-limit) -- the boundary is termination;
      (fourth type) DepartureSize = FiniteButUncomputed, distinct from the other three;
      (deflationary) is_fundamental_wall DepartureSize = false -- NOT a genuine wall, just uncomputed.
    The taxonomy now has FOUR wall-types, one of which is not even a real wall.  The role-limit / wall side
    is strongly heterogeneous -- honest in both directions (adds a type, removes the departure from the
    genuine-wall count).  eta as a whole remains open (its sphaleron factor is role-limit). *)
Theorem departure_descent :
  (forall n, K_dep <= n -> dep_process n = K_dep)
  /\ (forall n, exp_process n <> exp_process (S n))
  /\ wall_type DepartureSize = FiniteButUncomputed
  /\ is_fundamental_wall DepartureSize = false
  /\ wall_type DepartureSize <> wall_type NSBound.
Proof.
  split; [ exact dep_terminates | ].
  split; [ exact exp_never_stabilizes | ].
  split; [ reflexivity | ].
  split; [ reflexivity | discriminate ].
Qed.
