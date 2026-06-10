(** * ShellCapacityCounting.v — 2n² PROVED as counting, with the imported structure NAMED
       (closes the audit flag "периодическая таблица 2n² = ЗАЯВЛЕНО, не доказано")

      WHAT THIS FILE PROVES (0 axioms, pure combinatorics):
        subshell l holds 2·(2l+1) states (2l+1 orientations m ∈ {−l..l}, × 2 spins);
        shell n = subshells l < n;  Σ_{l<n} 2(2l+1) = 2n²  (shell_capacity_2n2);
        and the LITERAL state space — the list of triples (l, m, s) — has length 2n²
        (shell_states_count).  Instances: 2, 8, 18, 32.

      WHAT IS IMPORTED (named, NOT derived from distinction):
        the quantum-number STRUCTURE — l ranges over l < n, m over |m| ≤ l, s binary.
        That tower is the hydrogen/Coulomb degeneracy structure (physics input; a different
        potential gives a different tower).  ToS touches the count at exactly ONE point:
        the ×2 spin factor is L2-binarity (spin_binary).  Everything else is arithmetic.

      WHAT THIS DOES NOT CLAIM (honesty, per ApplicationsAudit.v):
        2n² is the shell CAPACITY, not the period length: actual periods run
        2,8,8,18,18,32,32 (aufbau doubling) — flagged in
        ApplicationsAudit.periods_carry_aufbau_doubling; "row length = 2n²" stays an
        over-claim there.  shell_capacity in ApplicationsAudit.v is DEFINED as 2n²;
        here that number is COUNTED (shell_capacity_counted) and proved equal to 2n².
        Sibling: experimental/CoulombFull3D.degeneracy_sum_general (Σ(2l+1) over l ≤ n);
        here the foundation-level, spin-included, list-literal version.

    Elements: the literal states (l, m, s) — concrete lists; the numbers 2, 8, 18, 32
    Roles:    n — the shell role; l — subshell; m — orientation; s — spin (L2-binary);
              capacity = how many Elements the shell ROLE can host
    Rules:    the (n,l,m,s) tower (IMPORTED structure) + counting (forced arithmetic):
              Σ_{l<n} 2(2l+1) = 2n²

    ============ E/R/R разбор ============
      Rules (L5): структура квантовых чисел (l<n, |m|≤l, s бинарен) задаёт пространство
                  состояний; Σ_{l<n} 2(2l+1) = 2n² — вынужденная арифметика поверх неё.
                  Правило честности: ВХОД = структура (водородная вырожденность, КМ),
                  НЕ различение; ВЫХОД = счёт.
      Roles (L4): оболочка n / подоболочка l / ориентация m / спин s; ёмкость — «сколько
                  Elements вмещает роль-оболочка»; ×2 спина — ЕДИНСТВЕННАЯ точка касания
                  ToS-слоя (L2-бинарность, spin_binary).
      Elements  : литеральные списки состояний (shell_states), числа 2, 8, 18, 32;
                  1s-оболочка = ровно [(0,0,↑); (0,0,↓)] (shell1_is_1s).
    ДИАГНОСТИКА (P4): доказана ЁМКОСТЬ, не длина периода — ауфбау даёт 2,8,8,18,18,32,32
      (честный флаг в ApplicationsAudit).  Невынужденная точка ИМЕНОВАНА: башня l<n —
      вход из физики (другой потенциал — другая башня); могло быть иначе при тех же
      ToS-правилах.  Уровень: methods/честное закрытие аудит-флага — «заявлено» → «доказано
      при названном входе».  НЕ «2n² из различения».

    STATUS: 13 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia List ZArith.
Import ListNotations.

(* ===================================================================== *)
(*  PART A — THE COUNT: Σ_{l<n} 2(2l+1) = 2n²                             *)
(* ===================================================================== *)

(** Σ_{i<k} f i — sum over the first k values. *)
Fixpoint sum_below (f : nat -> nat) (k : nat) : nat :=
  match k with
  | O => O
  | S k' => (sum_below f k' + f k')%nat
  end.

(** m-orientations of subshell l: m ∈ {−l..l}, i.e. 2l+1 values. *)
Definition orientations (l : nat) : nat := (2 * l + 1)%nat.

(** Subshell capacity: orientations × 2 spins. *)
Definition subshell_capacity (l : nat) : nat := (2 * orientations l)%nat.

(** Shell capacity COUNTED: subshells l < n. *)
Definition shell_capacity_counted (n : nat) : nat := sum_below subshell_capacity n.

(** Σ_{l<n} (2l+1) = n² — the square from summed odd numbers. *)
Lemma orientations_sum : forall n, sum_below orientations n = (n * n)%nat.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. unfold orientations. lia.
Qed.

(** ★ THE COUNT: shell capacity = 2n² — proved, not defined. *)
Theorem shell_capacity_2n2 : forall n, shell_capacity_counted n = (2 * n * n)%nat.
Proof.
  unfold shell_capacity_counted.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. unfold subshell_capacity, orientations. lia.
Qed.

(** The audited instances: shells 1..4 hold 2, 8, 18, 32. *)
Lemma capacities_2_8_18_32 :
  map shell_capacity_counted [1; 2; 3; 4]%nat = [2; 8; 18; 32]%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  PART B — THE LITERAL STATE SPACE: lists of (l, m, s)                  *)
(* ===================================================================== *)

(** Orientations as a literal list: m = i − l for i ∈ {0..2l}. *)
Definition m_values (l : nat) : list Z :=
  map (fun i => (Z.of_nat i - Z.of_nat l)%Z) (seq 0 (2 * l + 1)).

Lemma m_values_count : forall l, length (m_values l) = orientations l.
Proof.
  intro l. unfold m_values, orientations.
  rewrite length_map, length_seq. reflexivity.
Qed.

(** Every listed m satisfies |m| ≤ l. *)
Lemma m_values_bounded : forall l m,
  In m (m_values l) -> (- Z.of_nat l <= m <= Z.of_nat l)%Z.
Proof.
  intros l m Hin. unfold m_values in Hin.
  apply in_map_iff in Hin. destruct Hin as [i [Heq Hin]].
  apply in_seq in Hin. lia.
Qed.

(** Spin: the L2-binary factor — the one point where the ToS layer enters the count. *)
Definition spin : list bool := [true; false].

Lemma spin_binary : length spin = 2%nat.
Proof. reflexivity. Qed.

(** The literal subshell state space: (m, s) pairs — the cartesian product. *)
Definition subshell_states (l : nat) : list (Z * bool) :=
  list_prod (m_values l) spin.

Lemma subshell_states_count :
  forall l, length (subshell_states l) = subshell_capacity l.
Proof.
  intro l. unfold subshell_states.
  rewrite length_prod, m_values_count.
  unfold subshell_capacity. cbn [length spin]. lia.
Qed.

(** The literal shell state space: triples (l, m, s) with l < n. *)
Definition shell_states (n : nat) : list (nat * Z * bool) :=
  flat_map
    (fun l => map (fun ms : Z * bool => (l, fst ms, snd ms)) (subshell_states l))
    (seq 0 n).

(** Generic: length of a flat_map over seq 0 k is the sum of the part lengths. *)
Lemma length_flat_map_seq :
  forall (T : Type) (g : nat -> list T) (k : nat),
    length (flat_map g (seq 0 k)) = sum_below (fun l => length (g l)) k.
Proof.
  intros T g k. induction k.
  - reflexivity.
  - rewrite seq_S, flat_map_app, length_app, IHk.
    simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Sums respect pointwise-equal summands. *)
Lemma sum_below_ext :
  forall (f g : nat -> nat) (k : nat),
    (forall i, f i = g i) -> sum_below f k = sum_below g k.
Proof.
  intros f g k H. induction k.
  - reflexivity.
  - simpl. rewrite IHk, H. reflexivity.
Qed.

(** ★★ THE LITERAL COUNT: the state LIST of shell n has length 2n² — the 2n² is the
    size of an exhibited state space, not a defined number. *)
Theorem shell_states_count : forall n, length (shell_states n) = (2 * n * n)%nat.
Proof.
  intro n. unfold shell_states.
  rewrite (length_flat_map_seq _ _ n).
  transitivity (shell_capacity_counted n).
  - apply sum_below_ext. intro i.
    rewrite length_map. apply subshell_states_count.
  - apply shell_capacity_2n2.
Qed.

(* ===================================================================== *)
(*  Concrete shells                                                      *)
(* ===================================================================== *)

(** The 1s shell is LITERALLY the two spin states of (l=0, m=0). *)
Lemma shell1_is_1s :
  shell_states 1 = [(0%nat, 0%Z, true); (0%nat, 0%Z, false)].
Proof. reflexivity. Qed.

Lemma shell2_count : length (shell_states 2) = 8%nat.
Proof. reflexivity. Qed.

Lemma shell4_count : length (shell_states 4) = 32%nat.
Proof. reflexivity. Qed.

(** Honesty pointer (no import): the CAPACITY sequence 2,8,18,32 is NOT the period
    sequence 2,8,8,18,18,32,32 — see ApplicationsAudit.periods_carry_aufbau_doubling.
    This file upgrades ApplicationsAudit's shell_capacity from DEFINED to COUNTED. *)

Print Assumptions shell_capacity_2n2.
Print Assumptions shell_states_count.
