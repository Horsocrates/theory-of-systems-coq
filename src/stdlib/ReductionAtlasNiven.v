(** * ReductionAtlasNiven.v — the reduction atlas, page IV: the integer TRACE (Niven), the
      sibling invariant to page II's determinant.  The cluster's finite-order / periodicity facts —
      a rational rotation's order (①/Clifford), the crystallographic restriction (④/SO(3)), the
      3-4-5 aperiodicity (the Niven seed) — are NOT separate facts.  They are ONE engine: the
      integer trace m = 2cosθ of a unimodular element, run through the Cayley–Hamilton trace
      recurrence a_{k+2} = m·a_{k+1} − a_k.  Where page II read the DETERMINANT (held at ±1 =
      adjacency), this page reads the TRACE (at 2cosθ = periodicity): det and trace are the two
      invariants of a 2×2, and together they ARE the classification of finite-order SL₂ elements
      (det = 1 ∧ trace ∈ {−2..2} ⟺ finite order = the crystallographic orders {1,2,3,4,6}).

    Elements: the integer trace sequence tr m k; the five elliptic closing orbits (orders
              1,2,3,4,6); the cleared 3-4-5 trace dseq and its non-divisibility by 5 (L1 + P4)
    Roles:    the integer trace m — the single integer deciding periodicity: |m|≤2 (elliptic) ⟺
              the rotation closes (finite order, Element); |m|≥3 (hyperbolic) ⟺ it never returns
              (infinite order, role-limit); a non-integer rational trace s/t (t≥2) is killed by a
              cleared-trace congruence (the 3-4-5 case)
    Rules:    one generating rule — the Cayley–Hamilton trace recurrence a_{k+2}=m·a_{k+1}−a_k with
              det 1 (the companion matrix [[m,−1],[1,0]] is unimodular = page II's invariant)

    THE DEEP POINT — the trace is the sibling of the determinant.  Page II held the determinant
    ad−bc at ±1 (adjacency); page IV reads the trace 2cosθ.  They are the two coefficients of the
    characteristic polynomial x²−m·x+1: trace = m, det = 1.  The trace recurrence's companion
    matrix [[m,−1],[1,0]] has determinant 1 (`companion_unimodular`), so the trace engine runs ON
    a det-1 (SL₂) iteration.  The engine: a_{k+2}=m·a_{k+1}−a_k (`tr_SS`).  Two faces of the SAME
    integer m: (role-limit) |m|≥3 ⟹ the trace strictly grows and never returns to a₀=2
    (`tr_role_limit`, the hyperbolic / infinite-order side; m≤−3 symmetric); (Element) m∈{2,−2,1,
    −1,0} ⟹ the orbit closes at orders 1,2,3,4,6 (`tr_closes_all`, the elliptic / crystallographic
    side).  The non-integer rational case is the 3-4-5 rotation (2cosθ=8/5): the cleared trace
    dseq=5ᵏ·2cos(kθ) is never divisible by 5 (`trace_345_never_div5`), so 2cos(kθ) is never the
    integer 2 — the rotation never returns (role-limit), recovering `infinite_order_345` in trace
    form.  Together with page II: det = 1 (unimodular, page II) ∧ trace ∈ {−2..2} (Niven, page IV)
    ⟺ finite order — the crystallographic restriction is literally "trace ∈ {−2,−1,0,1,2}".
    Element = elliptic (closes); role-limit = hyperbolic / irrational-angle (never closes).

    ============ E/R/R разбор ============
      Rules (L5): одно правило — рекуррентность следа Кэли–Гамильтона a_{k+2}=m·a_{k+1}−a_k, det=1
                  (сопутствующая [[m,−1],[1,0]] унимодулярна = инвариант стр.II); след крутится на SL₂.
      Roles (L4): целый след m решает периодичность: |m|≤2 (эллиптич.) ⟺ замыкается (конечный порядок,
                  Element, порядки {1,2,3,4,6}); |m|≥3 (гиперболич.) ⟺ не возвращается (role-limit);
                  рациональный s/t, t≥2 (3-4-5: 8/5) убит сравнением очищенного следа.
      Elements  : последовательность tr m k; пять эллиптич. орбит; очищенная dseq и её неделимость на 5.
    ДИАГНОСТИКА (P4): движок 4 = СЛЕД, родной брат движка 2 = ОПРЕДЕЛИТЕЛЬ. det и tr — два инварианта 2×2,
    коэффициенты x²−mx+1; вместе ОНИ ЕСТЬ классификация конечного порядка SL₂: det=1 (стр.II) ∧ tr∈{−2..2}
    (Нивен, стр.IV) ⟺ конечный порядок. Кристалл. ограничение = буквально «след∈{−2,−1,0,1,2}». «Имеет ли
    рациональный поворот период?» (①④+3-4-5) = ОДИН вопрос про ОДНО целое (след) через ОДНУ рекуррентность.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Znumtheory.

Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ENGINE: the integer trace recurrence a_{k+2} = m·a_{k+1} − a_k     *)
(* ===================================================================== *)

(** The trace sequence of a unimodular element of trace m: aₖ = tr(Mᵏ), with a₀ = tr(I) = 2,
    a₁ = tr(M) = m, and the Cayley–Hamilton recurrence a_{k+2} = m·a_{k+1} − a_k (det M = 1). *)
Fixpoint tr (m : Z) (k : nat) : Z :=
  match k with
  | O => 2
  | S k' => match k' with
            | O => m
            | S k'' => m * tr m k' - tr m k''
            end
  end.

(** ★ The single rule: the Cayley–Hamilton trace recurrence. *)
Lemma tr_SS : forall m k, tr m (S (S k)) = m * tr m (S k) - tr m k.
Proof. reflexivity. Qed.

(** Cross-link to page II (the determinant engine): the recurrence's companion matrix
    [[m,−1],[1,0]] has determinant 1 — it is unimodular (page II's invariant).  So the trace
    engine runs on a det-1 (SL₂) iteration: trace = m (page IV), det = 1 (page II) are the two
    coefficients of the characteristic polynomial x²−m·x+1. *)
Lemma companion_unimodular : forall m : Z, m * 0 - (-1) * 1 = 1.
Proof. intros. ring. Qed.

(* ===================================================================== *)
(*  ROLE-LIMIT FACE — |m| ≥ 3 (hyperbolic): the trace grows, never returns *)
(* ===================================================================== *)

(** For trace m ≥ 3 the trace sequence is strictly increasing and positive: the hyperbolic case,
    where the unimodular element has infinite order (m ≤ −3 is symmetric, |trace| grows). *)
Lemma tr_increasing : forall m, 3 <= m ->
  forall k, tr m k < tr m (S k) /\ 0 < tr m k.
Proof.
  intros m Hm. induction k as [|k IH].
  - simpl. split; lia.
  - destruct IH as [Hlt Hpos]. rewrite tr_SS. split; [ nia | lia ].
Qed.

(** Hence for m ≥ 3 every trace past the start exceeds 2. *)
Lemma tr_gt2 : forall m, 3 <= m -> forall k, 2 < tr m (S k).
Proof.
  intros m Hm. induction k as [|k IH].
  - simpl. lia.
  - destruct (tr_increasing m Hm (S k)) as [Hlt _]. lia.
Qed.

(** ★ The role-limit side: for trace m ≥ 3 the orbit NEVER returns to a₀ = 2 — the unimodular
    element has infinite order (hyperbolic / no period). *)
Lemma tr_role_limit : forall m, 3 <= m -> forall k, (1 <= k)%nat -> tr m k <> 2.
Proof.
  intros m Hm k Hk. destruct k as [|k']; [ lia | ].
  pose proof (tr_gt2 m Hm k'). lia.
Qed.

(* ===================================================================== *)
(*  ELEMENT FACE — m ∈ {2,−2,1,−1,0} (elliptic): the orbit closes          *)
(* ===================================================================== *)

(** ★ The Element side: the five elliptic traces close at the crystallographic orders.
      m =  2 (θ=0,   order 1):  returns at k=1;
      m = −2 (θ=π,   order 2):  returns at k=2;
      m = −1 (θ=2π/3,order 3):  returns at k=3;
      m =  0 (θ=π/2, order 4):  returns at k=4;
      m =  1 (θ=π/3, order 6):  returns at k=6.
    These are exactly the crystallographic orders {1,2,3,4,6} = the finite-order traces. *)
Lemma tr_closes_all :
  tr 2 1 = 2 /\ tr (-2) 2 = 2 /\ tr (-1) 3 = 2 /\ tr 0 4 = 2 /\ tr 1 6 = 2.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  RATIONAL FLAGSHIP — the 3-4-5 rotation (2cosθ = 8/5), t ≥ 2            *)
(* ===================================================================== *)

(** The cleared integer trace of the 3-4-5 rotation: dseq k = 5ᵏ · 2cos(kθ) with 2cosθ = 8/5.
    Clearing the denominator turns a_{k+1} = (8/5)·a_k − a_{k-1} into the integer recurrence
    dseq_{k+2} = 8·dseq_{k+1} − 25·dseq_k, with dseq 0 = 2, dseq 1 = 8. *)
Fixpoint dseq (k : nat) : Z :=
  match k with
  | O => 2
  | S k' => match k' with
            | O => 8
            | S k'' => 8 * dseq k' - 25 * dseq k''
            end
  end.

Lemma dseq_SS : forall k, dseq (S (S k)) = 8 * dseq (S k) - 25 * dseq k.
Proof. reflexivity. Qed.

(** The mod-5 invariant: the cleared trace is never divisible by 5.  Since dseq_{k+2} ≡ 8·dseq_{k+1}
    ≡ 3·dseq_{k+1} (mod 5) and 3 is invertible mod 5, non-divisibility propagates — no Gauss/prime
    needed, only elementary divisibility algebra (8x = (x²-clear) + 5·…, and 2·3x − 5x = x). *)
Lemma dseq_5_pair : forall k, ~ (5 | dseq k) /\ ~ (5 | dseq (S k)).
Proof.
  induction k as [|k IH].
  - split; intros [c Hc]; cbn in Hc; lia.
  - destruct IH as [IH0 IH1]. split.
    + exact IH1.
    + intros Hassumed. apply IH1.
      assert (H8 : (5 | 8 * dseq (S k))).
      { replace (8 * dseq (S k)) with (dseq (S (S k)) + 25 * dseq k)
          by (rewrite dseq_SS; ring).
        apply Z.divide_add_r; [ exact Hassumed | exists (5 * dseq k); ring ]. }
      assert (H3 : (5 | 3 * dseq (S k))).
      { replace (3 * dseq (S k)) with (8 * dseq (S k) - 5 * dseq (S k)) by ring.
        apply Z.divide_sub_r; [ exact H8 | exists (dseq (S k)); ring ]. }
      replace (dseq (S k)) with (2 * (3 * dseq (S k)) - 5 * dseq (S k)) by ring.
      apply Z.divide_sub_r;
        [ apply Z.divide_mul_r; exact H3 | exists (dseq (S k)); ring ].
Qed.

(** ★ The 3-4-5 rotation never returns: the cleared trace is never divisible by 5, so
    2cos(kθ) = dseq k / 5ᵏ is never the integer 2 (a return would force 5ᵏ | dseq k).  Hence the
    3-4-5 rotation is aperiodic (role-limit) — `infinite_order_345` re-derived through the trace
    engine, the rational (t ≥ 2) case of Niven. *)
Lemma trace_345_never_div5 : forall k, ~ (5 | dseq k).
Proof. intros k. destruct (dseq_5_pair k) as [H _]. exact H. Qed.

(* ===================================================================== *)
(*  The atlas page: one integer trace, periodicity decided                 *)
(* ===================================================================== *)

(** The trace (Niven) atlas page:
      (engine link) the companion matrix is unimodular, det = 1 (`companion_unimodular`) — the
        trace runs on page II's determinant-1 iteration;
      (role-limit) trace m ≥ 3 ⟹ the orbit never returns to 2 (`tr_role_limit`) — hyperbolic /
        infinite order;
      (Element) the five elliptic traces close at orders {1,2,3,4,6} (`tr_closes_all`) — the
        crystallographic finite-order traces;
      (rational flagship) the 3-4-5 cleared trace is never divisible by 5 (`trace_345_never_div5`)
        — the rotation never returns.
    One integer trace decides periodicity; det (page II) and trace (page IV) together classify
    finite order in SL₂. *)
Theorem niven_trace_atlas :
  (forall m : Z, m * 0 - (-1) * 1 = 1)
  /\ (forall m : Z, 3 <= m -> forall k, (1 <= k)%nat -> tr m k <> 2)
  /\ (tr 2 1 = 2 /\ tr (-2) 2 = 2 /\ tr (-1) 3 = 2 /\ tr 0 4 = 2 /\ tr 1 6 = 2)
  /\ (forall k, ~ (5 | dseq k)).
Proof.
  split; [ exact companion_unimodular | ].
  split; [ exact tr_role_limit | ].
  split; [ exact tr_closes_all | exact trace_345_never_div5 ].
Qed.
