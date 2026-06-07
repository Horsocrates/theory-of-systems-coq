(** * DynamicBoundaryLPO.v — НАПРАВЛЕНИЕ N1++ (deepening N1+, по запросу автора 2026-06-07): the край of
      the dynamic finitization boundary is PROVED to be EXACTLY LPO (not merely cited).

   N1+ (DynamicBoundaryFrontier) established, over nat-flows, that
       Element (bounded)  <->  eventually-constant,
   with the Element direction (eventually-const -> bounded) CONSTRUCTIVE and the converse
   (bounded -> eventually-const) CITED as the non-constructive "край" (= LPO = halting,
   cs/ScaleFlowUndecidable).  This file DISCHARGES that citation: it proves, fully and 0-axiom,
   that the principle "every nondecreasing bounded nat-flow is eventually constant" (MCT_nat) is
   logically EQUIVALENT to LPO (the limited principle of omniscience).

   ★ THE THEOREM (the genuine new content):   MCT_nat  <->  LPO.
     -- MCT_nat -> LPO  (CONSTRUCTIVE reduction).  Encode a boolean sequence g as the indicator
        flow  f_lpo g n = (1 if some g k, k<=n, is true; else 0) -- nondecreasing, bounded by 1.
        MCT_nat stabilises it at some N; the stable value DECIDES (exists n, g n) \/ (forall n, ~ g n).
     -- LPO -> MCT_nat  (induction on the bound B).  At bound S B' ask LPO "does f reach S B'?":
        reached -> f stabilises at the witness; never -> f is bounded by B', recurse.
   Together: the Element-completing "край" of the dynamic boundary IS LPO -- now a theorem, not a
   citation.  This is strictly deeper than N1 (linear class decidable) and N1+ (край named): it
   PINS the non-constructive content of the dynamic boundary to a named, classical principle.

   HONEST SCOPE.  Fully machine-closed, 0 axioms.  Both MCT_nat and LPO are stated as Props and we
   prove their INTER-DERIVABILITY -- we never ASSERT either (no axiom).  By the spirit of reverse
   mathematics this equivalence (monotone-convergence over nat ~ LPO) is known; the GENUINE ToS
   content is (a) the 0-axiom machine proof and (b) the identification of this equivalence as the
   EXACT край of the *dynamic finitization boundary* that N1+ pointed at.  No new theorem of
   constructive mathematics is claimed.  The halting face (the running counter nh_count, whose
   eventual-constancy = the machine halting) stays CITED (cs/ScaleFlowUndecidable), not re-proved.
   The flow predicates are replicated from DynamicBoundaryFrontier (N1+, cited, self-contained).

   Elements: the nat-flow; the bound B; the stabilisation index N; the boolean sequence g; the
             indicator flow f_lpo.
   Roles:    LPO = the omniscience oracle = the role-limit край; MCT_nat = dynamic Element-completion;
             the equivalence = these are the SAME non-constructive content.
   Rules:    MCT_nat -> LPO (constructive, via the indicator flow); LPO -> MCT_nat (induction on the
             bound); together MCT_nat <-> LPO.

   ============ E/R/R разбор (осн. + образующие + вложенные) ============
     ОСН.: край динамич. финитизац. границы доказан как РОВНО LPO (не цитата).
     Rules (L5): MCT->LPO конструктивно (индикатор f_lpo решает (ex g)\/(all ~g)); LPO->MCT индукцией
                 по боду B (запрос "достигает верхушки?"); вместе MCT_nat <-> LPO.
     Roles (L4): LPO = оракул всеведения = role-limit-край; MCT_nat = дин. Element-завершение; экв-сть
                 = одно и то же неконструктивное содержание.
     Elements  : ℕ-поток; бод B; индекс стабилизации N; булева g; индикатор f_lpo.
     ОБРАЗУЮЩИЕ: DynamicBoundaryFrontier (N1+, цитировал край — здесь ПОГАШАЕМ); LPO (Bishop);
                 ScaleFlowUndecidable (halting-лицо: nh_count стабилизируется <-> машина встаёт).
     ВЛОЖЕННЫЕ : f_lpo g (индикатор — носитель MCT->LPO); поток-уровень при боде S B' (носитель индукции
                 LPO->MCT); каждый = вложенный свидетель внутри эквивалентности.
   ДИАГНОСТИКА (P4): ★ genuine-глубже N1/N1+: ЦИТИРОВАННЫЙ край -> ДОКАЗАННАЯ эквивалентность
   MCT_nat <-> LPO. 0 аксиом — оба суть Prop, доказываю взаимовыводимость БЕЗ постулирования (констр.
   мета-теорема). ЧЕСТНО: по духу reverse-math это известно (MCT над ℕ ~ LPO); genuine ToS-вклад =
   (a) 0-axiom машинное доказательство, (b) идентификация как ТОЧНОГО края динамич. границы (на что
   N1+ указывал). Halting-лицо (nh_count) — цитата (ScaleFlowUndecidable), не передоказываю.

   STATUS: 9 Qed, 0 Admitted, 0 axioms
   Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Arith Lia Bool.

(* ===================================================================== *)
(*  Nat-flows and the structural predicates (replicated from N1+)           *)
(* ===================================================================== *)

Definition NatFlow := nat -> nat.
Definition nf_nondecreasing (f : NatFlow) : Prop := forall n, f n <= f (S n).
Definition nf_bounded (f : NatFlow) : Prop := exists B, forall n, f n <= B.
Definition nf_eventually_const (f : NatFlow) : Prop :=
  exists N, forall n, N <= n -> f n = f N.

Lemma nf_mono : forall f, nf_nondecreasing f -> forall a b, a <= b -> f a <= f b.
Proof.
  intros f Hnd a b Hab. induction Hab.
  - apply Nat.le_refl.
  - apply Nat.le_trans with (f m). exact IHHab. apply Hnd.
Qed.

(* ===================================================================== *)
(*  The two principles, stated as Props (NOT asserted as axioms)            *)
(* ===================================================================== *)

(** LPO: the limited principle of omniscience (Bishop). *)
Definition LPO : Prop :=
  forall g : nat -> bool, (exists n, g n = true) \/ (forall n, g n = false).

(** MCT_nat: every nondecreasing bounded nat-flow is eventually constant -- the dynamic
    Element-completion "край". *)
Definition MCT_nat : Prop :=
  forall f, nf_nondecreasing f -> nf_bounded f -> nf_eventually_const f.

(* ===================================================================== *)
(*  The indicator flow: vehicle of MCT_nat -> LPO                           *)
(* ===================================================================== *)

(** any_true g n = "some g k with k <= n is true". *)
Fixpoint any_true (g : nat -> bool) (n : nat) : bool :=
  match n with
  | O => g O
  | S m => orb (any_true g m) (g (S m))
  end.

Lemma any_true_mono : forall g m n, m <= n -> any_true g m = true -> any_true g n = true.
Proof.
  intros g m n Hmn Hm. induction Hmn.
  - exact Hm.
  - simpl. rewrite IHHmn. reflexivity.
Qed.

Lemma any_true_last : forall g n, any_true g n = false -> g n = false.
Proof.
  intros g n H. destruct n.
  - exact H.
  - simpl in H. apply orb_false_iff in H. destruct H as [_ H2]. exact H2.
Qed.

Lemma any_true_spec : forall g n, any_true g n = true -> exists k, g k = true.
Proof.
  intros g n. induction n; intro H.
  - exists 0. exact H.
  - simpl in H. apply orb_true_iff in H. destruct H as [H | H].
    + apply IHn. exact H.
    + exists (S n). exact H.
Qed.

(** The indicator flow of g. *)
Definition f_lpo (g : nat -> bool) : NatFlow := fun n => if any_true g n then 1 else 0.

Lemma f_lpo_nondecreasing : forall g, nf_nondecreasing (f_lpo g).
Proof.
  intros g n. unfold f_lpo. destruct (any_true g n) eqn:E.
  - assert (HS : any_true g (S n) = true).
    { apply (any_true_mono g n (S n)). apply Nat.le_succ_diag_r. exact E. }
    rewrite HS. apply Nat.le_refl.
  - destruct (any_true g (S n)); apply Nat.le_0_l.
Qed.

Lemma f_lpo_bounded : forall g, nf_bounded (f_lpo g).
Proof.
  intro g. exists 1. intro n. unfold f_lpo.
  destruct (any_true g n); [ apply Nat.le_refl | apply Nat.le_0_l ].
Qed.

(* ===================================================================== *)
(*  ★ Direction 1 (CONSTRUCTIVE): MCT_nat -> LPO                            *)
(* ===================================================================== *)

Lemma mct_implies_lpo : MCT_nat -> LPO.
Proof.
  intros mct g.
  destruct (mct (f_lpo g) (f_lpo_nondecreasing g) (f_lpo_bounded g)) as [N HN].
  destruct (any_true g N) eqn:E.
  - left. apply (any_true_spec g N). exact E.
  - right. intro n.
    assert (Hn : any_true g n = false).
    { destruct (Nat.le_gt_cases n N) as [Hle | Hgt].
      - destruct (any_true g n) eqn:En; [ | reflexivity ].
        assert (Hc : any_true g N = true)
          by (apply (any_true_mono g n N); [ exact Hle | exact En ]).
        rewrite E in Hc. discriminate.
      - assert (Hge : N <= n) by lia.
        specialize (HN n Hge). unfold f_lpo in HN. rewrite E in HN.
        destruct (any_true g n) eqn:En; [ simpl in HN; discriminate | reflexivity ]. }
    apply any_true_last. exact Hn.
Qed.

(* ===================================================================== *)
(*  ★ Direction 2 (induction on the bound): LPO -> MCT_nat                  *)
(* ===================================================================== *)

Lemma lpo_implies_mct : LPO -> MCT_nat.
Proof.
  intros lpo. unfold MCT_nat. intros f Hnd Hbd. destruct Hbd as [B Hb].
  revert f Hnd Hb. induction B as [|B IHB]; intros f Hnd Hb.
  - exists 0. intros n _.
    assert (f n = 0) by (specialize (Hb n); lia).
    assert (f 0 = 0) by (specialize (Hb 0); lia). lia.
  - destruct (lpo (fun n => S B <=? f n)) as [Hex | Hall].
    + destruct Hex as [n0 Hn0]. apply Nat.leb_le in Hn0.
      exists n0. intros n Hn.
      assert (Hfn0 : f n0 = S B) by (specialize (Hb n0); lia).
      assert (Hfn : f n = S B).
      { specialize (Hb n).
        assert (f n0 <= f n) by (apply nf_mono; [ exact Hnd | exact Hn ]). lia. }
      rewrite Hfn, Hfn0. reflexivity.
    + apply IHB. exact Hnd. intro n. specialize (Hall n).
      apply Nat.leb_gt in Hall. lia.
Qed.

(* ===================================================================== *)
(*  Capstone: the dynamic boundary's край IS exactly LPO                    *)
(* ===================================================================== *)

(** ★ The край of the dynamic finitization boundary -- "every nondecreasing bounded nat-flow is
    eventually constant" -- is logically EQUIVALENT to LPO.  N1+ cited this; it is now a theorem.
    The Element-completing direction of the dynamic boundary carries EXACTLY the omniscience content
    of LPO; for the running counter nh_count this край is HALTING (cs/ScaleFlowUndecidable). *)
Theorem boundary_frontier_is_lpo : MCT_nat <-> LPO.
Proof. split; [ exact mct_implies_lpo | exact lpo_implies_mct ]. Qed.
