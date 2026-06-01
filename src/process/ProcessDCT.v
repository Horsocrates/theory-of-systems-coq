(** * ProcessDCT.v — Dominated Convergence Theorem, reduction core (F-28, Part VI)

    Elements: rational integral values ∫fₙ, ∫f, dominator g, residuals ∫|fₙ−f|
    Roles:    ∫f as role-limit; g as the "envelope" forcing the limit/integral swap
    Rules:    |∫fₙ−∫f| ≤ ∫|fₙ−f| (engine);  |fₙ−f|≤2g ⇒ ∫|fₙ−f|≤∫2g (domination)

    Dominated Convergence: fₙ → f pointwise, |fₙ| ≤ g (g integrable) ⇒ ∫fₙ → ∫f.
    The textbook proof factors as:
        |∫fₙ − ∫f|  ≤  ∫|fₙ − f|        (linearity + triangle: the ENGINE)
        ∫|fₙ − f|   ≤  ∫(2g)            (domination: the ENVELOPE)
        ∫|fₙ − f|   → 0                 (Fatou / a.e.→L¹: the SUBSTANTIVE LIMIT)
    whence ∫fₙ → ∫f by squeezing.  We prove the ENGINE and the ENVELOPE constructively
    on the self-contained Riemann-sum integral (ProcessMCT.riemann_sum), and obtain the
    conclusion by squeezing GIVEN the residual L¹-convergence ∫|fₙ−f| → 0.

    ============ E/R/R разбор (СНАЧАЛА) ============
      Elements (L1): значения ∫fₙ, ∫f, мажоранта g, невязки ∫|fₙ−f|.
      Roles (L4):    ∫f — роль-предел; g — «конверт», вынуждающий обмен предела и
                     интеграла (без него обмен незаконен).
      Rules (L5):    |∫fₙ−∫f| ≤ ∫|fₙ−f| (движок: линейность + неравенство треугольника
                     для сумм); |fₙ−f| ≤ 2g ⇒ ∫|fₙ−f| ≤ ∫2g (домінування); сжатие.
      ЧЕСТНОСТЬ:
        • ДОКАЗАНО (0 аксиом): движок dct_diff_bound и конверт dct_dom_bound; сжатие
          process_dct даёт ∫fₙ → ∫f ПРИ ∫|fₙ−f| → 0.
        • СОДЕРЖАТЕЛЬНАЯ ИНТЕРПРЕТАЦИЯ: ∫f есть роль-предел; невязки контролируются ∫2g.
        • ПРОГРАММА: вывод ∫|fₙ−f| → 0 из поточечной сходимости (шаг Фату, a.e.→L¹)
          требует завершённой меры/предельной функции — P4-граница. Берём его как
          честную гипотезу-вход L¹ (Hres), явно помечая границу.
      НАШ ПУТЬ: формализуем РЕДУКЦИЮ DCT (движок + конверт) самодостаточно на
        riemann_sum, а не «DCT над завершённым L¹». Зеркалит дисциплину F-27/F-30/F-32.
      ДИАГНОСТИКА: классическое «∫lim = lim∫ под мажорантой» предполагает завершённую
        lim fₙ и Fatou над завершённой мерой; у нас fₙ, f и невязки — ПРОЦЕССЫ, а
        доказуемое ядро — конструктивная редукция к L¹-сходимости невязок.

    STATUS: 7 Qed, 0 Admitted, 0 axioms (engine+envelope constructive; Fatou step = hyp)
    Author: Horsocrates | Date: May 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessMCT.

Open Scope Q_scope.

(* ===================================================================== *)
(*  Extra finite-sum algebra (linearity + triangle) used by the engine.   *)
(* ===================================================================== *)

(** Σ a − Σ b = Σ (a − b). *)
Lemma q_sum_minus : forall (a b : nat -> Q) (N : nat),
  q_sum a N - q_sum b N == q_sum (fun i => a i - b i) N.
Proof.
  intros a b N. induction N as [|k IH]; cbn [q_sum].
  - ring.
  - rewrite <- IH. ring.
Qed.

(** Triangle inequality for sums: |Σ g| ≤ Σ |g|. *)
Lemma q_sum_abs_le : forall (g : nat -> Q) (N : nat),
  Qabs (q_sum g N) <= q_sum (fun i => Qabs (g i)) N.
Proof.
  intros g N. induction N as [|k IH]; cbn [q_sum].
  - assert (H0 : Qabs (0:Q) == 0) by (apply Qabs_pos; apply Qle_refl).
    rewrite H0. apply Qle_refl.
  - eapply Qle_trans; [ apply Qabs_triangle | ].
    apply Qplus_le_compat; [ exact IH | apply Qle_refl ].
Qed.

(* ===================================================================== *)
(*  ENGINE:  |∫f₁ − ∫f₂| ≤ ∫|f₁ − f₂|.                                    *)
(* ===================================================================== *)

Lemma dct_diff_bound : forall (f1 f2 : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  Qabs (riemann_sum f1 pts w N - riemann_sum f2 pts w N)
    <= riemann_sum (fun x => Qabs (f1 x - f2 x)) pts w N.
Proof.
  intros f1 f2 pts w N Hw. unfold riemann_sum.
  (* w·Σf₁ − w·Σf₂ = w·Σ(f₁−f₂) *)
  assert (Estep :
    w * q_sum (fun i => f1 (pts i)) N - w * q_sum (fun i => f2 (pts i)) N
    == w * q_sum (fun i => f1 (pts i) - f2 (pts i)) N).
  { assert (Hqs : q_sum (fun i => f1 (pts i)) N - q_sum (fun i => f2 (pts i)) N
                  == q_sum (fun i => f1 (pts i) - f2 (pts i)) N) by apply q_sum_minus.
    rewrite <- Hqs. ring. }
  rewrite Estep.
  rewrite Qabs_Qmult.
  assert (Hwabs : Qabs w == w) by (apply Qabs_pos; exact Hw).
  rewrite Hwabs.
  rewrite (Qmult_comm w (Qabs (q_sum (fun i => f1 (pts i) - f2 (pts i)) N))).
  rewrite (Qmult_comm w (q_sum (fun i => Qabs (f1 (pts i) - f2 (pts i))) N)).
  apply Qmult_le_compat_r; [ apply q_sum_abs_le | exact Hw ].
Qed.

(* ===================================================================== *)
(*  ENVELOPE:  |f₁ − f₂| ≤ 2g  ⇒  ∫|f₁ − f₂| ≤ ∫(2g).                     *)
(* ===================================================================== *)

Lemma dct_dom_bound : forall (f1 f2 g : Q -> Q) (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (forall x, Qabs (f1 x - f2 x) <= 2 * g x) ->
  riemann_sum (fun x => Qabs (f1 x - f2 x)) pts w N
    <= riemann_sum (fun x => 2 * g x) pts w N.
Proof.
  intros f1 f2 g pts w N Hw Hdom.
  apply riemann_sum_monotone; [ exact Hw | exact Hdom ].
Qed.

(** Residual integrals are nonnegative. *)
Lemma dct_residual_nonneg : forall (fs : nat -> Q -> Q) (f : Q -> Q)
                                   (pts : nat -> Q) (w : Q) (N n : nat),
  0 <= w ->
  0 <= riemann_sum (fun x => Qabs (fs n x - f x)) pts w N.
Proof.
  intros fs f pts w N n Hw.
  apply riemann_sum_nonneg; [ exact Hw | intro i; apply Qabs_nonneg ].
Qed.

(* ===================================================================== *)
(*  CONCLUSION (squeeze):  ∫|fₙ−f| → 0  ⇒  ∫fₙ → ∫f.                      *)
(* ===================================================================== *)

Theorem process_dct : forall (fs : nat -> Q -> Q) (f : Q -> Q)
                             (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (fun n => riemann_sum (fun x => Qabs (fs n x - f x)) pts w N) ~~ const_process 0 ->
  (fun n => riemann_sum (fs n) pts w N) ~~ const_process (riemann_sum f pts w N).
Proof.
  intros fs f pts w N Hw Hres eps Heps.
  destruct (Hres eps Heps) as [N0 HN0].
  exists N0. intros n Hn.
  unfold const_process in *.
  specialize (HN0 n Hn).
  set (res := riemann_sum (fun x => Qabs (fs n x - f x)) pts w N) in *.
  assert (Hr0 : 0 <= res) by (unfold res; apply dct_residual_nonneg; exact Hw).
  assert (Hres_eps : res < eps).
  { assert (E : res - 0 == res) by ring.
    rewrite E in HN0. rewrite Qabs_pos in HN0 by exact Hr0. exact HN0. }
  apply Qle_lt_trans with res.
  - unfold res. apply dct_diff_bound. exact Hw.
  - exact Hres_eps.
Qed.

(* ===================================================================== *)
(*  Packaged DCT: domination envelope + convergence.                      *)
(* ===================================================================== *)

Theorem process_dct_dominated : forall (fs : nat -> Q -> Q) (f g : Q -> Q)
                                       (pts : nat -> Q) (w : Q) (N : nat),
  0 <= w ->
  (forall n x, Qabs (fs n x - f x) <= 2 * g x) ->            (* domination envelope *)
  (fun n => riemann_sum (fun x => Qabs (fs n x - f x)) pts w N) ~~ const_process 0 ->
  (* (a) residuals are uniformly dominated by ∫2g; (b) integrals converge to ∫f *)
  (forall n, riemann_sum (fun x => Qabs (fs n x - f x)) pts w N
             <= riemann_sum (fun x => 2 * g x) pts w N)
  /\ (fun n => riemann_sum (fs n) pts w N) ~~ const_process (riemann_sum f pts w N).
Proof.
  intros fs f g pts w N Hw Hdom Hres. split.
  - intro n. apply dct_dom_bound; [ exact Hw | intro x; apply Hdom ].
  - apply process_dct; [ exact Hw | exact Hres ].
Qed.

Print Assumptions process_dct.
Print Assumptions process_dct_dominated.
