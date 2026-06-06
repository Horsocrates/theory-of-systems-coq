(** * ScaleFlowUndecidable.v — the bridge: deciding a scale-flow's Element/role-limit side IS halting
      Connects the "Иерархии и Каскады" direction (foundation/InterLevelCalculus.v) to the
      Computer-Science branch: InterLevelCalculus gives the SEMANTIC dichotomy (a monotone scale-flow
      is Element=bounded XOR role-limit=unbounded); here we prove that DECIDING which side a flow is
      on is undecidable — flow-unboundedness is a RoleLimitDrawn boundary — by REDUCING halting to it.
      So InterLevelCalculus's honest "край: located, not crossed" becomes a THEOREM about WHY it
      cannot be crossed computationally.

      The reduction flow: g c n = (number of steps k < n at which machine c has NOT yet halted),
      a nondecreasing counter that STABILISES iff c halts.  Hence:
        halts c     -> g c is bounded   (Element)      — fully constructive (0 axioms);
        diverges c <-> g c is unbounded (role-limit)   — fully constructive (0 axioms).
      We work on the divergence (role-limit) side so the whole bridge is axiom-free: the OTHER
      direction (bounded -> halts) is exactly InterLevelCalculus's classic-needing край (Σ1 not
      ~~-stable), and we avoid it.

    Reuses cs/HaltingRoleLimit.v (run, halts_in, halts, diverges, halts_in_mono) and
    cs/BoundaryDecidability.v (ElementDrawn, RoleLimitDrawn).  Replicates the InterLevelCalculus.v
    flow predicates locally (self-contained; cites that file, does not touch it).

    Elements: configurations; the counter-flow g c : nat->Q; the not-yet-halted step indicator
    Roles:    "bounded / unbounded" = the STATUS of the flow (Element / role-limit, as in
              InterLevelCalculus); a decider of that status = a role-oracle (Status != Role)
    Rules:    the reduction — g c is nondecreasing; bounded <-> halts; a boundedness-decider would
              decide divergence

    ============ E/R/R разбор ============
      Rules (L5): сведение — g c монотонно нарастает; ограничен <-> останавливается; решатель
                  ограниченности ⟹ решатель divergence.
      Roles (L4): «ограничен/неограничен» = СТАТУС потока (Element/role-limit, как у InterLevel);
                  решатель статуса = роль-оракул.
      Elements  : конфигурации; счётчик-поток g c (nat->Q); индикатор не-остановленности.
    ДИАГНОСТИКА (P4): InterLevel даёт СЕМАНТИЧЕСКУЮ дихотомию (element_excludes_role_limit); мы
      доказываем, что РЕШИТЬ её = halting (RoleLimitDrawn), движком CS-ветки.  Element-направление
      (halts->bounded) конструктивно 0 ax; role-limit-направление (bounded->halts) нужен classic =
      честный «край» InterLevel — поэтому работаем со стороны divergence (flow_role_limit <-> diverges
      конструктивно), сохраняя 0 ax.  «Локализуем, не пересекаем» становится теоремой о вычислительной
      непересекаемости.

    STATUS: 17 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.
From Stdlib Require Import Lqa.
From ToS Require Import cs.HaltingRoleLimit.
From ToS Require Import cs.BoundaryDecidability.

(* QArith auto-opens Q_scope; close it so nat arithmetic (nh_count) stays nat.
   The flow predicates below use named Qle/Qlt, which are scope-independent. *)
Close Scope Q_scope.

(* ===================================================================== *)
(*  Replicated from foundation/InterLevelCalculus.v (cited, not imported) *)
(* ===================================================================== *)

Definition ScaleFlow := nat -> Q.
Definition nondecreasing (f : ScaleFlow) : Prop := forall n, Qle (f n) (f (S n)).
Definition bounded_above (f : ScaleFlow) (B : Q) : Prop := forall n, Qle (f n) B.
Definition unbounded (f : ScaleFlow) : Prop := forall B, exists n, Qlt B (f n).
Definition flow_element (f : ScaleFlow) : Prop := nondecreasing f /\ exists B, bounded_above f B.
Definition flow_role_limit (f : ScaleFlow) : Prop := nondecreasing f /\ unbounded f.

(** Naturals are cofinal in Q (from GravityH1Decision.v / InterLevel arena). *)
Lemma arch_nat : forall B : Q, exists n : nat, Qlt B (inject_Z (Z.of_nat n)).
Proof.
  intro B. destruct (Qarchimedean B) as [p Hp]. exists (Pos.to_nat p).
  unfold inject_Z. rewrite positive_nat_Z. exact Hp.
Qed.

(** Bridge nat-≤ to Q-≤ on injected nats (Zle_Qle is a Prop EQUALITY, not an iff). *)
Lemma Qle_of_nat_le : forall a b : nat,
  a <= b -> Qle (inject_Z (Z.of_nat a)) (inject_Z (Z.of_nat b)).
Proof. intros a b H. rewrite <- Zle_Qle. apply (proj1 (Nat2Z.inj_le _ _)). exact H. Qed.

(* ===================================================================== *)
(*  RoleLimitDrawn transfers across logical equivalence                    *)
(* ===================================================================== *)

Lemma RoleLimitDrawn_iff : forall (D : Type) (P Q : D -> Prop),
  (forall d, P d <-> Q d) -> RoleLimitDrawn P -> RoleLimitDrawn Q.
Proof.
  intros D P Q Hiff HP HE. apply HP. destruct HE as [dec Hdec]. exists dec.
  intro d. split.
  - intro H. apply (proj2 (Hiff d)). apply (proj1 (Hdec d)). exact H.
  - intro H. apply (proj2 (Hdec d)). apply (proj1 (Hiff d)). exact H.
Qed.

(* ===================================================================== *)
(*  The halting->flow-boundedness reduction                               *)
(* ===================================================================== *)

Section FlowReduction.

  Variable Config : Type.
  Variable step   : Config -> Config.
  Variable halted : Config -> bool.

  (** 0 if step k has halted, 1 if still running. *)
  Definition not_halted (c : Config) (k : nat) : nat :=
    if halted (run Config step halted k c) then 0 else 1.

  (** Running counter: how many steps < n the machine was still running. *)
  Fixpoint nh_count (c : Config) (n : nat) : nat :=
    match n with O => 0 | S k => nh_count c k + not_halted c k end.

  (** The reduction flow over Q. *)
  Definition g (c : Config) : ScaleFlow := fun n => inject_Z (Z.of_nat (nh_count c n)).

  Lemma nh_count_step : forall c n, nh_count c n <= nh_count c (S n).
  Proof.
    intros c n. simpl. unfold not_halted.
    destruct (halted (run Config step halted n c)); lia.
  Qed.

  Lemma nh_count_mono : forall c a b, a <= b -> nh_count c a <= nh_count c b.
  Proof.
    intros c a b Hab. induction Hab.
    - apply Nat.le_refl.
    - apply Nat.le_trans with (nh_count c m). exact IHHab. apply nh_count_step.
  Qed.

  Lemma g_nondecreasing : forall c, nondecreasing (g c).
  Proof.
    intros c n. unfold g. apply Qle_of_nat_le. apply nh_count_step.
  Qed.

  (* ---- the role-limit (divergence) side, fully constructive ---- *)

  Lemma nh_count_diverges : forall c,
    diverges Config step halted c -> forall n, nh_count c n = n.
  Proof.
    intros c Hdiv n. induction n.
    - reflexivity.
    - simpl. unfold not_halted. rewrite (Hdiv n). simpl. rewrite IHn. lia.
  Qed.

  Lemma g_diverges_unbounded : forall c,
    diverges Config step halted c -> unbounded (g c).
  Proof.
    intros c Hdiv B. destruct (arch_nat B) as [n Hn]. exists n.
    unfold g. rewrite (nh_count_diverges c Hdiv n). exact Hn.
  Qed.

  Lemma not_halts_diverges : forall c,
    ~ halts Config step halted c -> diverges Config step halted c.
  Proof.
    intros c Hnh n. destruct (halted (run Config step halted n c)) eqn:E.
    - exfalso. apply Hnh. exists n. exact E.
    - reflexivity.
  Qed.

  Lemma diverges_iff_not_halts : forall c,
    diverges Config step halted c <-> ~ halts Config step halted c.
  Proof.
    intro c. split.
    - intros Hdiv [n Hn]. unfold halts_in in Hn. specialize (Hdiv n).
      rewrite Hdiv in Hn. discriminate.
    - apply not_halts_diverges.
  Qed.

  (* ---- the Element (halting) side, fully constructive ---- *)

  Lemma not_halted_zero : forall c k,
    halted (run Config step halted k c) = true -> not_halted c k = 0.
  Proof. intros c k H. unfold not_halted. rewrite H. reflexivity. Qed.

  Lemma nh_count_const_after : forall c N,
    (forall k, N <= k -> halted (run Config step halted k c) = true) ->
    forall m, nh_count c (N + m) = nh_count c N.
  Proof.
    intros c N Htail m. induction m.
    - rewrite Nat.add_0_r. reflexivity.
    - replace (N + S m) with (S (N + m)) by lia.
      simpl. rewrite (not_halted_zero c (N + m) (Htail (N + m) (Nat.le_add_r N m))).
      rewrite IHm. lia.
  Qed.

  Lemma nh_count_le_N : forall c N,
    (forall k, N <= k -> halted (run Config step halted k c) = true) ->
    forall n, nh_count c n <= nh_count c N.
  Proof.
    intros c N Htail n. destruct (Nat.le_gt_cases n N) as [Hle | Hgt].
    - apply nh_count_mono. exact Hle.
    - replace n with (N + (n - N)) by lia.
      rewrite (nh_count_const_after c N Htail (n - N)). apply Nat.le_refl.
  Qed.

  Lemma g_halts_bounded : forall c,
    halts Config step halted c -> exists B, bounded_above (g c) B.
  Proof.
    intros c [N HN].
    assert (Htail : forall k, N <= k -> halted (run Config step halted k c) = true).
    { intros k Hk. exact (halts_in_mono Config step halted c N k Hk HN). }
    exists (inject_Z (Z.of_nat (nh_count c N))). intro n. unfold g.
    apply Qle_of_nat_le. apply nh_count_le_N. exact Htail.
  Qed.

  (** Element side (constructive, 0 axioms): a halting machine gives an Element flow. *)
  Lemma flow_element_of_halts : forall c,
    halts Config step halted c -> flow_element (g c).
  Proof.
    intros c Hh. unfold flow_element. split.
    - apply g_nondecreasing.
    - apply g_halts_bounded. exact Hh.
  Qed.

  (* ---- the reduction, on the constructive (divergence) side ---- *)

  Lemma flow_role_limit_iff_diverges : forall c,
    flow_role_limit (g c) <-> diverges Config step halted c.
  Proof.
    intro c. split.
    - intros [_ Hub]. apply not_halts_diverges. intro Hh.
      destruct (g_halts_bounded c Hh) as [B HB]. destruct (Hub B) as [n Hn].
      pose proof (HB n) as HBn. lra.
    - intro Hdiv. unfold flow_role_limit. split.
      + apply g_nondecreasing.
      + apply g_diverges_unbounded. exact Hdiv.
  Qed.

  (** ★ THE BRIDGE: if divergence is undecidable (RoleLimitDrawn — as for a universal machine,
      cf. no_halting_decider), then so is a scale-flow's role-limit (unbounded) side.  Deciding
      InterLevelCalculus's Element/role-limit dichotomy is halting. *)
  Theorem scale_flow_role_limit_undecidable :
    RoleLimitDrawn (fun c => diverges Config step halted c) ->
    RoleLimitDrawn (fun c => flow_role_limit (g c)).
  Proof.
    intro Hrl.
    apply (RoleLimitDrawn_iff Config
             (fun c => diverges Config step halted c)
             (fun c => flow_role_limit (g c))).
    - intro c. split.
      + intro Hd. apply (proj2 (flow_role_limit_iff_diverges c)). exact Hd.
      + intro Hf. apply (proj1 (flow_role_limit_iff_diverges c)). exact Hf.
    - exact Hrl.
  Qed.

End FlowReduction.

(** Synthesis: InterLevelCalculus.v's monotone Element(bounded)/role-limit(unbounded) dichotomy and
    the CS branch are ONE boundary along two hierarchies (scale vs computation).  The CS branch
    supplies the missing computability layer: the bounded/unbounded side is RoleLimitDrawn (deciding
    it is halting).  Element direction (halts -> bounded) is constructive (our Element floor);
    role-limit direction (bounded -> halts) is InterLevel's classic-needing край — avoided here by
    working through divergence, keeping the bridge 0-axiom. *)

Print Assumptions flow_role_limit_iff_diverges.
Print Assumptions scale_flow_role_limit_undecidable.
