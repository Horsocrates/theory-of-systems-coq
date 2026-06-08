(** * ChebyshevLLN.v — Markov & Chebyshev concentration on a FINITE probability space (Element, 0 axioms),
       and the weak law of large numbers ACROSS the finitization boundary: the finite-n concentration
       bound is a decided rational inequality (Element), while convergence-in-probability / almost-sure
       convergence over the infinite product space is the ROLE-LIMIT.  The repo had `variance` as a
       definition (stdlib/Statistics.v) but NO concentration inequality; this adds Markov & Chebyshev.

    -- The finite side (Element, 0 axioms, over Q) --
      A finite probability space is `list (Q*Q)` of (value, weight).  `expect` = Σ vᵢwᵢ, `tail_w a` =
      Σ_{vᵢ≥a} wᵢ = P(X≥a).  Then:
        markov    : values≥0, weights≥0, 0<a  ⟹  a · P(X≥a) ≤ E[X].
        chebyshev : weights≥0, 0<ε            ⟹  ε² · P((X−μ)² ≥ ε²) ≤ E[(X−μ)²]  (= Var when ΣW=1).
      Chebyshev IS Markov applied to the squared-deviation variable; the event (X−μ)²≥ε² is exactly
      |X−μ|≥ε for ε>0.  Both are CLOSED rational inequalities — decided, the signature of an Element.

    -- The weak LLN as a process; the boundary --
      For n i.i.d. copies, Var(S_n/n) = σ²/n (the standard reduction), so Chebyshev gives
      P(|S_n/n − μ| ≥ ε) ≤ σ²/(n ε²) =: `cheb_bound σ² ε n` — a PROCESS (each finite n a concrete Q, an
      Element) whose limit is 0.  The ROLE-LIMIT is the infinite product probability space itself: to even
      STATE "P(…)→0 for all outcomes" / almost-sure convergence one needs the completed totality of
      infinite trial-sequences (the σ-algebra on Πℕ) — choice / classic.  Finite concentration = Element;
      the infinite product / a.s. convergence = the price.  (settheory/ChoicePriceMap.v;
      analysis/BolzanoWeierstrass.v pays classic for an analogous undecidable infinitary criterion.)

    ============ E/R/R разбор ============
      Elements : конечное вероятностное пространство (список (значение,вес), рациональные веса); частичные суммы — актуальны (P4).
      Roles    : хвост P(X≥a) = роль-событие; среднее/дисперсия = роли центр/разброс; сходимость п.н. = role-limit.
      Rules    : Марков (Σ по событию ≤ E[X]/a) и Чебышёв (Марков на (X−μ)²) — разрешимые конечные Q-неравенства;
                 ЗБЧ-граница σ²/(nε²) — процесс (каждое n — Element).
      ДИАГНОСТИКА (P4): конечное пространство + Чебышёв = Element (замкнутое Q-неравенство, 0 акс) — НОВОЕ; бесконечное
        произведение / сходимость п.н. = role-limit (завершённая тотальность бесконечных испытаний = выбор/classic), цитируется.
        Та же граница finite=Element / infinite=role-limit. Уровень: `новая теорема` (Марков/Чебышёв) + `граница` (ЗБЧ).

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa List PeanoNat Lia ZArith.
Import ListNotations.
Open Scope Q_scope.

(* ===================================================================== *)
(*  A finite probability space and its functionals                         *)
(* ===================================================================== *)

Definition dist := list (Q * Q).      (* (value, weight) pairs *)

Definition sq (x : Q) : Q := x * x.

Lemma sq_nonneg : forall x, 0 <= sq x.
Proof. intro x. unfold sq. nra. Qed.

Fixpoint total_w (l : dist) : Q :=
  match l with [] => 0 | (_, w) :: r => w + total_w r end.

(** E[X] = Σ vᵢ wᵢ. *)
Fixpoint expect (l : dist) : Q :=
  match l with [] => 0 | (v, w) :: r => v * w + expect r end.

(** P(X ≥ a) = Σ over the event {vᵢ ≥ a} of the weights. *)
Fixpoint tail_w (a : Q) (l : dist) : Q :=
  match l with
  | [] => 0
  | (v, w) :: r => if Qle_bool a v then w + tail_w a r else tail_w a r
  end.

(** The squared-deviation space: each value vᵢ ↦ (vᵢ − μ)², weights unchanged. *)
Definition sqdev (mu : Q) (l : dist) : dist := map (fun p => (sq (fst p - mu), snd p)) l.

Definition mean (l : dist) : Q := expect l / total_w l.

(* ===================================================================== *)
(*  Positivity                                                             *)
(* ===================================================================== *)

Lemma tail_w_nonneg : forall a l, Forall (fun p => 0 <= snd p) l -> 0 <= tail_w a l.
Proof.
  intros a l. induction l as [| [v w] r IH]; intro Hw.
  - simpl. apply Qle_refl.
  - simpl. pose proof (Forall_inv Hw) as Hw0. simpl in Hw0.
    pose proof (Forall_inv_tail Hw) as Hwr.
    destruct (Qle_bool a v).
    + assert (0 <= tail_w a r) by (apply IH; exact Hwr). nra.
    + apply IH; exact Hwr.
Qed.

Lemma expect_nonneg : forall l,
  Forall (fun p => 0 <= fst p) l -> Forall (fun p => 0 <= snd p) l -> 0 <= expect l.
Proof.
  induction l as [| [v w] r IH]; intros Hv Hw.
  - simpl. apply Qle_refl.
  - simpl. pose proof (Forall_inv Hv) as Hv0. pose proof (Forall_inv Hw) as Hw0.
    simpl in Hv0, Hw0.
    assert (0 <= expect r) by
      (apply IH; [ apply (Forall_inv_tail Hv) | apply (Forall_inv_tail Hw) ]).
    nra.
Qed.

(* ===================================================================== *)
(*  Markov's inequality (finite, Element, 0 axioms)                         *)
(* ===================================================================== *)

(** ★★ MARKOV: for a non-negative variable on a finite weighted space, a · P(X≥a) ≤ E[X]. *)
Lemma markov : forall (l : dist) (a : Q),
  Forall (fun p => 0 <= fst p) l ->
  Forall (fun p => 0 <= snd p) l ->
  0 < a ->
  a * tail_w a l <= expect l.
Proof.
  induction l as [| [v w] r IH]; intros a Hv Hw Ha.
  - simpl. nra.
  - pose proof (Forall_inv Hv) as Hv0. pose proof (Forall_inv_tail Hv) as Hvr.
    pose proof (Forall_inv Hw) as Hw0. pose proof (Forall_inv_tail Hw) as Hwr.
    simpl in Hv0, Hw0.
    assert (Hrec : a * tail_w a r <= expect r) by (apply IH; assumption).
    simpl.
    destruct (Qle_bool a v) eqn:E.
    + apply Qle_bool_iff in E. nra.
    + nra.
Qed.

(* ===================================================================== *)
(*  Chebyshev's inequality (finite, Element, 0 axioms)                      *)
(* ===================================================================== *)

(** ★★ CHEBYSHEV: ε² · P((X−μ)² ≥ ε²) ≤ E[(X−μ)²]  (= Var·ΣW; the variance when ΣW=1).
    This is Markov applied to the squared-deviation variable; the event (X−μ)²≥ε² is |X−μ|≥ε. *)
Lemma chebyshev : forall (l : dist) (mu eps : Q),
  Forall (fun p => 0 <= snd p) l -> 0 < eps ->
  sq eps * tail_w (sq eps) (sqdev mu l) <= expect (sqdev mu l).
Proof.
  intros l mu eps Hw Heps. apply markov.
  - apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [q [Hq _]]. rewrite <- Hq. simpl. apply sq_nonneg.
  - apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [q [Hq Hin]]. rewrite <- Hq. simpl.
    rewrite Forall_forall in Hw. apply (Hw q Hin).
  - unfold sq. nra.
Qed.

(** ★ Chebyshev about the mean — the standard concentration inequality. *)
Corollary chebyshev_mean : forall (l : dist) (eps : Q),
  Forall (fun p => 0 <= snd p) l -> 0 < eps ->
  sq eps * tail_w (sq eps) (sqdev (mean l) l) <= expect (sqdev (mean l) l).
Proof. intros l eps Hw Heps. apply chebyshev; assumption. Qed.

(* ===================================================================== *)
(*  The weak LLN bound as a process (Element each n; limit = role-limit)    *)
(* ===================================================================== *)

(** The Chebyshev tail bound for the sample mean of n i.i.d. copies of variance var:
      P(|S_n/n − μ| ≥ ε) ≤ var / (n · ε²).
    A PROCESS nat→Q: each finite n is a concrete rational (an Element); its limit 0 — and the
    convergence-in-probability statement over the infinite product space — is the role-limit. *)
Definition cheb_bound (var eps : Q) (n : nat) : Q :=
  var / (inject_Z (Z.of_nat n) * sq eps).

(* ===================================================================== *)
(*  CAPSTONE — the boundary                                                *)
(* ===================================================================== *)

(** Markov & Chebyshev across the finitization boundary:
      (markov)    a non-negative variable on a finite weighted Q space obeys a·P(X≥a) ≤ E[X] — a decided
                  rational inequality, 0 axioms (Element);
      (chebyshev) ε²·P((X−μ)²≥ε²) ≤ E[(X−μ)²] — Markov on the squared deviation, 0 axioms (Element);
      (tail≥0)    every tail probability is non-negative (a genuine probability).
    The weak LLN follows: with Var(S_n/n)=σ²/n, Chebyshev gives P(|S_n/n−μ|≥ε) ≤ σ²/(n ε²) = cheb_bound,
    a process vanishing as n grows.  The ROLE-LIMIT is the infinite product probability space — the
    completed totality of infinite trial-sequences needed to state convergence in probability / almost
    surely — choice / classic, honestly cited (settheory/ChoicePriceMap.v).  Finite concentration =
    Element; the infinite product = the price.  Level: Markov & Chebyshev are new in the repo (only
    `variance` existed) + the finite/infinite boundary framing of the LLN. *)
Theorem chebyshev_lln_boundary :
  (forall (l : dist) (a : Q),
     Forall (fun p => 0 <= fst p) l -> Forall (fun p => 0 <= snd p) l -> 0 < a ->
     a * tail_w a l <= expect l)
  /\ (forall (l : dist) (mu eps : Q),
        Forall (fun p => 0 <= snd p) l -> 0 < eps ->
        sq eps * tail_w (sq eps) (sqdev mu l) <= expect (sqdev mu l))
  /\ (forall (a : Q) (l : dist),
        Forall (fun p => 0 <= snd p) l -> 0 <= tail_w a l).
Proof.
  split; [ exact markov | ].
  split; [ exact chebyshev | exact tail_w_nonneg ].
Qed.
