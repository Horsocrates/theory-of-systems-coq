(** * CausalOrderGeometry.v — the POSITIVE half of the path FrameFreeFinitization.v pointed to: build the
      causal ORDER as a frame-free, relabel-invariant structure and check Sorkin's slogan
      "order + number = geometry".  FrameFreeFinitization showed the NEGATIVE (the regular lattice fails,
      the count is frame-free); this file builds the surviving structure — the causal-set realization of
      finitization — and shows the two frame-free data (order + number) carry geometric content with NO
      preferred frame.

    -- The two frame-free data --
      ORDER : the causal (lightcone) relation — who can influence whom.  In Minkowski this is the
              Lorentz-invariant lightcone order (Bombelli-Henson-Sorkin); it recovers the CONFORMAL class
              of the metric (Malament's theorem: the causal order determines the metric up to a conformal
              factor).  Here, concretely, a strict partial order (irreflexive + transitive).
      NUMBER: the cardinality of an order interval (x,y) = { z : x < z < y } — the "number = volume"
              content (Sorkin): it supplies the SCALE / proper time that the order alone omits.

    -- "order + number = geometry", frame-free --
      The genuinely Element-side, Lorentz-invariant data are exactly these two, and BOTH are invariant
      under relabeling (an order-embedding) — the discrete analog of general covariance / no preferred
      frame.  The physics is the order-isomorphism class, not the labels.  Concretely, on the CHAIN causal
      set (a discrete timelike geodesic, cprec x y := x < y):
        - order says 0 < 4 and 0 < 2 are both causal links (qualitatively "connected");
        - number distinguishes their SCALE: the interval (0,4) has 3 elements, (0,2) has 1 — the proper
          time the order omits;
        - a translation 0,4 -> 10,14 leaves the interval count = 3 (relabel-invariant).

    -- HONEST scope --
      A 1D-chain ILLUSTRATION of the slogan.  Known: causal sets (Sorkin); causal order determines the
      conformal metric (Malament/Hawking-King-McCarthy); a Poisson sprinkling is statistically Lorentz
      invariant (BHS).  This file does NOT derive causal-set DYNAMICS (the sum-over-orders), does NOT prove
      the conformal-recovery theorem, and does NOT claim nature IS a causal set.  It formalizes that order
      + number are frame-free and jointly carry causal-structure + scale — the positive half of the path.

    Elements: the chain causal set; interval (0,4) = {1,2,3} (card 3 = proper time)
    Roles:    order = conformal/causal structure (invariant); number = scale; relabeling = covariance
    Rules:    geometry = order + number, both frame-free (relabel-invariant) — the causal-set realization

    ============ E/R/R разбор ============
      Rules (L5): геометрия восстанавливается из ДВУХ frame-free данных: ПОРЯДКА (каузальная/конформная
                  структура) + ЧИСЛА (мощность интервала = объём/масштаб).  Оба Lorentz-инвариантны.
      Roles (L4): порядок = конформная структура (инвариант); число = масштаб (добавляет опущенное
                  порядком); перемаркировка (order-embedding) = смена координат (дискретная ковариантность);
                  P4 = локальная конечность.  Физика = класс изоморфизма, не метки.
      Elements  : цепь cprec x y := x<y; интервал (0,4)={1,2,3}, card=3; 0<4 и 0<2 связаны; card 3 != 1
                  (масштаб); сдвиг 0,4->10,14 сохраняет card=3 (frame-free).
    ДИАГНОСТИКА (P4): позитивная половина пути.  Порядок даёт каузальную структуру (chain_irrefl/_trans),
    инвариантную под перемаркировку (relabel_preserves_order); число даёт масштаб, которого порядку не
    хватает (number_adds_scale); оба не зависят от меток (translate_preserves_count) = дискретная общая
    ковариантность.  ЧЕСТНО: 1D-иллюстрация слогана; конформное восстановление = теорема Маламента (цитата);
    НЕ динамика causal-set, НЕ доказательство, что природа есть causal set.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith List Lia.
Import ListNotations.

(* ===================================================================== *)
(*  The chain causal set: a discrete timelike geodesic                     *)
(* ===================================================================== *)

(** The causal (lightcone) relation of the chain: x precedes y iff x < y. *)
Definition cprec (x y : nat) : bool := Nat.ltb x y.
Definition causally_before (x y : nat) : Prop := cprec x y = true.

(* ---- ORDER: a strict partial order (the causal / conformal structure) ---- *)

Lemma chain_irrefl : forall x, ~ causally_before x x.
Proof. intros x H. unfold causally_before, cprec in H. rewrite Nat.ltb_irrefl in H. discriminate. Qed.

Lemma chain_trans : forall x y z, causally_before x y -> causally_before y z -> causally_before x z.
Proof.
  unfold causally_before, cprec. intros x y z Hxy Hyz.
  apply Nat.ltb_lt in Hxy. apply Nat.ltb_lt in Hyz.
  apply (proj2 (Nat.ltb_lt x z)). lia.
Qed.

(** Antisymmetry is automatic from irreflexive + transitive. *)
Lemma chain_antisym : forall x y, causally_before x y -> ~ causally_before y x.
Proof. intros x y Hxy Hyx. apply (chain_irrefl x). apply (chain_trans x y x); assumption. Qed.

(* ---- NUMBER: the order interval and its cardinality ("number = volume") ---- *)

(** The order interval (x,y) = { z : x < z < y }. *)
Definition interval (x y : nat) : list nat :=
  filter (fun z => andb (cprec x z) (cprec z y)) (seq 0 (S y)).
Definition interval_card (x y : nat) : nat := length (interval x y).

Lemma interval_0_4 : interval_card 0 4 = 3.   (* {1,2,3} = proper time *)
Proof. reflexivity. Qed.

Lemma interval_0_2 : interval_card 0 2 = 1.   (* {1} *)
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  order + number = geometry, and both are frame-free                     *)
(* ===================================================================== *)

(** ORDER alone: both (0,4) and (0,2) are causal links — qualitatively "connected". *)
Lemma order_says_connected : causally_before 0 4 /\ causally_before 0 2.
Proof. split; reflexivity. Qed.

(** NUMBER supplies the SCALE the order omits: the two links have DIFFERENT volumes. *)
Lemma number_adds_scale : interval_card 0 4 <> interval_card 0 2.
Proof. rewrite interval_0_4, interval_0_2. discriminate. Qed.

(** FRAME-FREE (order): a strictly monotone relabeling (an order-embedding) preserves the causal order —
    the physics is the order-type, not the labels (the discrete analog of general covariance). *)
Lemma relabel_preserves_order :
  forall (g : nat -> nat), (forall a b, a < b -> g a < g b) ->
  forall x y, causally_before x y -> causally_before (g x) (g y).
Proof.
  intros g Hg x y H. unfold causally_before, cprec in *.
  apply Nat.ltb_lt in H. apply (proj2 (Nat.ltb_lt (g x) (g y))). apply Hg. exact H.
Qed.

(** FRAME-FREE (number): a translation 0,4 -> 10,14 leaves the interval count = 3. *)
Lemma translate_preserves_count : interval_card 0 4 = interval_card 10 14.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: order + number is frame-free geometry                        *)
(* ===================================================================== *)

(** The positive half of the path:
      (order)   the causal relation is a strict partial order (irreflexive + transitive) — the conformal /
                causal structure — and it is invariant under relabeling (an order-embedding);
      (number)  the interval cardinality supplies the scale the order omits, and is translation-invariant.
    So the two genuinely Element-side, Lorentz-invariant data — order + number — jointly carry geometric
    content with NO preferred frame: the causal-set realization of finitization, the path nature
    (Fermi-LAT) leaves open. *)
Theorem order_plus_number_is_frame_free_geometry :
  (forall x, ~ causally_before x x)
  /\ (forall x y z, causally_before x y -> causally_before y z -> causally_before x z)
  /\ (forall g, (forall a b, a < b -> g a < g b) ->
        forall x y, causally_before x y -> causally_before (g x) (g y))
  /\ (causally_before 0 4 /\ causally_before 0 2)
  /\ interval_card 0 4 <> interval_card 0 2
  /\ interval_card 0 4 = interval_card 10 14.
Proof.
  split; [ exact chain_irrefl | ].
  split; [ exact chain_trans | ].
  split; [ exact relabel_preserves_order | ].
  split; [ exact order_says_connected | ].
  split; [ exact number_adds_scale | exact translate_preserves_count ].
Qed.
