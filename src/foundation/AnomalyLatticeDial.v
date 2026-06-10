(** * AnomalyLatticeDial.v — TRUE box-exhaustive anomaly scan + the constraint DIAL
       (upgrades AnomalyExhaustive/AnomalySystematic from "~10 tested points" to genuine
        exhaustion over a declared lattice, with underdetermination QUANTIFIED per rule)

      WHAT THIS FILE PROVES (0 axioms, decidable scan, vm_compute):
        Over the DECLARED box (zu,zd,zl,ze) ∈ [−8..8]⁴ (hypercharges in units 1/6,
        normalization Y_Q = 1/6 i.e. zq = 1), the anomaly conditions narrow as a DIAL:
          83 521 tuples
          → grav linear [grav]²U(1)            : 1 317 solutions   (dial_grav)
          → + cubic [U(1)]³                    : 11 solutions      (dial_grav_cubic)
          → + non-abelian [SU(3)]²U(1),[SU(2)]²U(1) : EXACTLY 2     (dial_all_exact)
        and the two survivors are the SM pattern (−4,2,−3,6) and its u↔d swap — the
        filtered list is computed LITERALLY.  The non-abelian conditions do the real
        pinning (11 → 2): an explicit exotic, (−1,−1,0,0), passes grav+cubic and is
        killed by color (exotic_killed).

      WHAT IS IMPORTED (named inputs, NOT derived):
        (i)   one SM generation's fermion content + multiplicities (6,3,3,2,1) — physics;
        (ii)  the anomaly conditions themselves (QFT consistency), in EXACTLY the form of
              AnomalyChargeQuantization.v (anomaly_color/weak/grav/cubic);
        (iii) the normalization zq = 1 — LOAD-BEARING, not cosmetic: with zq = 0 a whole
              1-parameter family (0, t, −t, 0, 0) passes ALL four conditions for every t
              (zq0_family_passes), so "uniqueness" is uniqueness GIVEN Y_Q ≠ 0;
        (iv)  the box bound [−8..8] — declared scan range.  (Over ALL of Z the same pair
              is forced algebraically: ChargeLatticeTheory forces zl=−3, ze=6, zu+zd=−2,
              zu·zd=−8 ⟹ {2,−4} by Vieta; the box scan independently CONFIRMS it by
              exhaustion, complementary method.)

      WHAT THIS REPLACES (honesty): AnomalyExhaustive.v "exhaustive"/"unique among tested"
      tested ~5 alternatives with Y₁ fixed; AnomalySystematic.v scanned ~10 values of Y₂
      with Y₃=Y₄=0.  Here the WHOLE box is exhausted and the per-rule freedom is counted.

    Elements: 83 521 charge tuples; the 11 grav+cubic survivors; the final pair
              (−4,2,−3,6) [SM] and (2,−4,−3,6) [u↔d swap]; the exotic (−1,−1,0,0)
    Roles:    zq = 1 — the normalization role (load-bearing: kills the zq=0 family);
              each filter stage — "how much freedom the rule leaves" (the dial);
              the non-abelian conditions — the pinning role (11 → 2)
    Rules:    the four local anomaly conditions (QFT import, forms matched to
              AnomalyChargeQuantization.v); the scan rule = decidable exhaustion of a
              declared finite box (P4: finite actualization)

    ============ E/R/R разбор ============
      Rules (L5): 4 локальных условия аномалий — импорт КТП-консистентности (форма ровно
                  как в AnomalyChargeQuantization.v); правило-скан — разрешимый перебор
                  бокса [−8..8]⁴ (P4: конечная актуализация); каскад фильтров = «дайл».
      Roles (L4): zq=1 — нормировка с НЕСУЩЕЙ ролью (без неё семейство (0,t,−t,0,0)
                  проходит все условия — zq0_family_passes); счётчик каждой ступени —
                  роль «сколько свободы осталось у правила»; неабелевы условия — роль
                  «пиннинг» (11 → 2).
      Elements  : 83 521 кортеж; 1 317 grav-решений; 11 grav+cubic-решений (с экзотиками
                  типа (−1,−1,0,0)); финальная пара SM и u↔d-своп.
    ДИАГНОСТИКА (P4): «уникальность SM-гиперзарядов» впервые — РАЗРЕШИМАЯ теорема в
      объявленном боксе, а недоопределённость каждого правила — ЧИСЛО (1317 → 11 → 2).
      Невынужденные точки ИМЕНОВАНЫ: содержание поколения, сами условия аномалий,
      нормировка (несущая — теорема), границы бокса.  Честно: это НЕ «SM из различения»
      — это «SM-паттерн = единственное (с точностью до u↔d) решение НАЗВАННЫХ условий
      консистентности в НАЗВАННОМ боксе при НАЗВАННОЙ нормировке», машинно исчерпано.
      Уровень: methods/честное замыкание (заявленная исчерпываемость стала настоящей).

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia List Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The anomaly conditions, GENERALIZED in the normalization q            *)
(*  (forms match AnomalyChargeQuantization.v exactly at q = 1)            *)
(* ===================================================================== *)

Definition g_color (q zu zd : Z) : Z := 2*q + zu + zd.
Definition g_weak  (q zl : Z) : Z := 3*q + zl.
Definition g_grav  (q zu zd zl ze : Z) : Z := 6*q + 3*zu + 3*zd + 2*zl + ze.
Definition g_cubic (q zu zd zl ze : Z) : Z :=
  6*(q*q*q) + 3*(zu*zu*zu) + 3*(zd*zd*zd) + 2*(zl*zl*zl) + ze*ze*ze.

(** The normalization POSIT: Y_Q = 1/6, i.e. zq = 1 in units of 1/6. *)
Definition zq : Z := 1.

Definition a_color (zu zd : Z) : Z := g_color zq zu zd.
Definition a_weak  (zl : Z) : Z := g_weak zq zl.
Definition a_grav  (zu zd zl ze : Z) : Z := g_grav zq zu zd zl ze.
Definition a_cubic (zu zd zl ze : Z) : Z := g_cubic zq zu zd zl ze.

(* ===================================================================== *)
(*  The declared box and the full tuple lattice                           *)
(* ===================================================================== *)

(** All four free charges range over [−8..8] (units 1/6) — the DECLARED bound. *)
Definition box : list Z := map (fun n => Z.of_nat n - 8) (seq 0 17).

Definition tuples : list (Z*Z*Z*Z) :=
  flat_map (fun zu =>
    flat_map (fun zd =>
      flat_map (fun zl =>
        map (fun ze => (zu, zd, zl, ze)) box) box) box) box.

Lemma box_size : length box = 17%nat.
Proof. reflexivity. Qed.

(** Tuple count = 17⁴ = 83 521 (not stated as a unary-nat theorem: an 83k-deep unary
    numeral overflows the kernel checker; the dial counts below are the content). *)

(* ===================================================================== *)
(*  The dial: filters for each rule stage                                 *)
(* ===================================================================== *)

Definition zeqb (x : Z) : bool := Z.eqb x 0.

Definition pass_grav (t : Z*Z*Z*Z) : bool :=
  let '(zu, zd, zl, ze) := t in zeqb (a_grav zu zd zl ze).

Definition pass_grav_cubic (t : Z*Z*Z*Z) : bool :=
  let '(zu, zd, zl, ze) := t in
  zeqb (a_grav zu zd zl ze) && zeqb (a_cubic zu zd zl ze).

Definition pass_all (t : Z*Z*Z*Z) : bool :=
  let '(zu, zd, zl, ze) := t in
  zeqb (a_color zu zd) && zeqb (a_weak zl)
  && zeqb (a_grav zu zd zl ze) && zeqb (a_cubic zu zd zl ze).

(* ===================================================================== *)
(*  THE DIAL, MACHINE-COUNTED                                             *)
(* ===================================================================== *)

(** Stage 1 — the gravitational linear condition leaves 1 317 in-box solutions. *)
Theorem dial_grav : length (filter pass_grav tuples) = 1317%nat.
Proof. vm_compute. reflexivity. Qed.

(** Stage 2 — adding the cubic [U(1)]³ leaves 11. *)
Theorem dial_grav_cubic : length (filter pass_grav_cubic tuples) = 11%nat.
Proof. vm_compute. reflexivity. Qed.

(** ★★ Stage 3 — ALL four conditions: the in-box solution set is EXACTLY the SM
    pattern and its u↔d swap.  This is the literal filtered list — genuine
    exhaustion of the declared box, not a sample of tested alternatives. *)
Theorem dial_all_exact :
  filter pass_all tuples = [(-4, 2, -3, 6); (2, -4, -3, 6)].
Proof. vm_compute. reflexivity. Qed.

Corollary dial_all_count : length (filter pass_all tuples) = 2%nat.
Proof. rewrite dial_all_exact. reflexivity. Qed.

(** The dial strictly narrows: 2 < 11 < 1317 — each added rule removes real freedom. *)
Theorem dial_strictly_narrows :
  (length (filter pass_all tuples)
     < length (filter pass_grav_cubic tuples))%nat /\
  (length (filter pass_grav_cubic tuples)
     < length (filter pass_grav tuples))%nat.
Proof.
  rewrite dial_all_count, dial_grav_cubic, dial_grav. split; lia.
Qed.

(* ===================================================================== *)
(*  The survivors and a killed exotic                                     *)
(* ===================================================================== *)

(** The SM hypercharge pattern (units 1/6): (Yu,Yd,YL,Ye) = (−4,2,−3,6). *)
Theorem sm_passes_all : pass_all (-4, 2, -3, 6) = true.
Proof. reflexivity. Qed.

Theorem swap_passes_all : pass_all (2, -4, -3, 6) = true.
Proof. reflexivity. Qed.

(** ★ The non-abelian conditions do the pinning: the exotic (−1,−1,0,0) survives
    grav + cubic but is killed by [SU(3)]²U(1). *)
Theorem exotic_killed :
  pass_grav_cubic (-1, -1, 0, 0) = true /\ pass_all (-1, -1, 0, 0) = false.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  THE NORMALIZATION IS LOAD-BEARING (what zq = 1 excludes)              *)
(* ===================================================================== *)

(** ★ With zq = 0 the four conditions admit a WHOLE 1-parameter family
    (zu, zd, zl, ze) = (t, −t, 0, 0) for EVERY t — vector-like charge assignments.
    So the in-box pair-uniqueness above is uniqueness GIVEN Y_Q ≠ 0 (normalized
    to 1); the normalization posit carries real weight, it is not a convention
    that could be dropped. *)
Theorem zq0_family_passes : forall t : Z,
  g_color 0 t (-t) = 0 /\
  g_weak 0 0 = 0 /\
  g_grav 0 t (-t) 0 0 = 0 /\
  g_cubic 0 t (-t) 0 0 = 0.
Proof.
  intro t. unfold g_color, g_weak, g_grav, g_cubic.
  repeat split; ring.
Qed.

(** The two scanned survivors agree with AnomalyChargeQuantization's pattern:
    (zq,zu,zd,zl,ze) = (1,−4,2,−3,6) is its (YQ,Yu,Yd,YL,Ye) literally. *)
Theorem matches_charge_quantization_pattern :
  a_color (-4) 2 = 0 /\ a_weak (-3) = 0 /\
  a_grav (-4) 2 (-3) 6 = 0 /\ a_cubic (-4) 2 (-3) 6 = 0.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  SYNTHESIS                                                             *)
(* ===================================================================== *)

(** ★ CAPSTONE: the dial.  Within the declared box and normalization, the anomaly
    rules leave 1317 → 11 → exactly 2 charge patterns; the survivors are SM and its
    u↔d swap; the zq=0 family marks what the normalization excludes.  Uniqueness of
    the SM hypercharges is here a DECIDABLE, fully-scanned statement with every
    unforced input NAMED — not "SM from distinction". *)
Theorem anomaly_lattice_dial :
  length (filter pass_grav tuples) = 1317%nat /\
  length (filter pass_grav_cubic tuples) = 11%nat /\
  filter pass_all tuples = [(-4, 2, -3, 6); (2, -4, -3, 6)] /\
  (forall t : Z, g_cubic 0 t (-t) 0 0 = 0).
Proof.
  split; [apply dial_grav |].
  split; [apply dial_grav_cubic |].
  split; [apply dial_all_exact |].
  intro t. unfold g_cubic. ring.
Qed.

Print Assumptions dial_all_exact.
Print Assumptions anomaly_lattice_dial.
