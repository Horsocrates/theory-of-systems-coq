(** * CliffordCapstone.v — ① CAPSTONE: a rational rotation TERMINATES iff it is
      Z₄.  The cmul-orbit ↔ Niven-trace bridge, fully machine-checked.

    Elements: the rational circle points (a,b) ∈ S¹(ℚ) and their cmul-orbit
              cpow (a,b) k = (cos kθ, sin kθ) — a ℚ-sequence (a PROCESS)
    Roles:    a single-qubit rational rotation as a PROCESS — TERMINATING
              (closes → an Element; cos(nθ)=1 for some n≥1) or NON-TERMINATING
              (never closes → a role-limit)
    Rules:    the first coordinate obeys the Chebyshev recurrence
              A_{k+1} = 2a·A_k − A_{k-1} (uses a²+b²=1); the bridge
              2·tᵏ·A_k = c s t k (Niven's integer trace, 2a=s/t); Niven's
              obstruction t∤c s t (S k) for t≥2; and √3 ∉ ℚ for the 60°/120° gap

    THE CAPSTONE OF DIRECTION ①.  Earlier bricks (CliffordBoundary,
    CliffordPhaseGate, CliffordSynthesis) showed *instances* of the
    terminating/non-terminating dichotomy.  Here it is the FULL classification:

        capstone_only_Z₄_terminates :
          a rational point (a,b) of FINITE ORDER (∃ n≥1, fst(cpow (a,b) n) = 1)
          is one of the four points (±1,0), (0,±1) — i.e. exactly Z₄.

    The proof is the long-promised cmul-orbit ↔ Niven bridge:
      (1) the orbit's first coordinate A_k = fst(cpow (a,b) k) satisfies the
          Chebyshev trace recurrence A_{k+1} = 2a·A_k − A_{k-1} (needs a²+b²=1);
      (2) hence 2·tᵏ·A_k = c s t k, Niven's integer trace, where 2a = s/t;
      (3) finite order n forces A_n = 1, so c s t n = 2·tⁿ, so t | c s t n;
      (4) but Niven (niven_general) says t ∤ c s t (S m) when t ≥ 2 — so t = 1,
          i.e. 2a ∈ ℤ; with |a| ≤ 1 this gives 2a ∈ {−2,−1,0,1,2};
      (5) the cases 2a = ±1 (a = ±1/2, the 60°/120° points) have b² = 3/4, but
          √3 ∉ ℚ (`no_rational_sqrt3`) — those are NOT rational points; so only
          2a ∈ {−2,0,2} survive, giving exactly Z₄.

    This closes the HONEST FRONTIER flagged in CliffordSynthesis.v: the capstone
    is now stated on the cmul-orbit directly and proved — the "Gaussian/algebraic
    integer machinery" is replaced by the elementary Niven integer trace c s t k,
    bridged to the orbit by a two-step induction.  The converse is trivial
    (`Z4_terminates`): the four Z₄ points do close.

    ============ E/R/R разбор ============
      Rules (L5): A_{k+1}=2a·A_k−A_{k-1} (Чебышёв, нужно a²+b²=1); мост 2tᵏA_k=c s t k;
                  обструкция Нивена t∤c(S m) при t≥2; √3∉ℚ.
      Roles (L4): поворот = ПРОЦЕСС; ЗАВЕРШАЮЩИЙСЯ (cos nθ=1 ⟹ Element ⟹ Z₄) или
                  НЕЗАВЕРШАЮЩИЙСЯ (role-limit, вне Z₄).
      Elements  : точки (a,b)∈S¹(ℚ), орбита cpow (a,b) k = (cos kθ, sin kθ) (L1+P4).
    ДИАГНОСТИКА (P4): ① ПОЛНОСТЬЮ классифицировано — ЗАВЕРШАЮЩИЙСЯ рациональный поворот
    ⟺ Z₄. Точки 60°/120° (cos=±½ рационален) — НЕ рациональные точки окружности
    (sin=±√3/2 = незавершающийся процесс), поэтому в Z₄ не входят: «иррационально ли
    √3» — не-вопрос, √3 ЕСТЬ незавершающийся процесс (`no_rational_sqrt3`).

    ГЛУБОКИЙ РАЗБОР (P4) — три точки, в которых процессная онтология делает работу,
    недоступную классическому «завершённому» взгляду:
      (1) ОНТОЛОГИЧЕСКАЯ ИНВЕРСИЯ. Классика спрашивает «какие рациональные точки — корни из
          единицы?» (вопрос о ЗАВЕРШЁННОЙ группе SO(2,ℚ) и её подгруппе кручения). Мы спрашиваем
          «какие орбиты-ПРОЦЕССЫ завершаются?». Z₄ — НЕ примитивная подгруппа, которую «находят»;
          Z₄ есть МНОЖЕСТВО ТЕРМИНУСОВ завершающихся процессов. Поэтому теорема — не «выделение
          подгруппы», а КРИТЕРИЙ КОНСТИТУИРОВАНИЯ (L5): сортирует каждый поворот-процесс на
          завершающийся (→ терминус = Element) и незавершающийся (→ role-limit), между ними пусто.
          Element производен; процесс первичен.
      (2) ФАНТОМ 60°/120° РАСТВОРЁН (не декретом). Рациональная ТОЧКА требует завершаемости ОБОИХ
          координатных процессов. У (½, √3/2): косинус-процесс завершается (½ — Element, cos 60°
          рационален), а синус-процесс (√3/2) — нет. Значит «рациональный поворот порядка 6» —
          ФАНТОМ: есть завершающаяся косинус-роль, но НЕТ Элемента-точки, ибо синус-процесс
          незавершающийся. Исключён не стипуляцией, а потому что √3 доказуемо не замыкается
          (`no_rational_sqrt3`). Фантом растворяется в «пару процессов, один из которых не закрылся».
      (3) МОСТ = ОДНА РОЛЬ В ДВУХ ПРЕДСТАВЛЕНИЯХ ЭЛЕМЕНТОВ. Геометрический процесс (cmul-орбита над
          ℚ²) и арифметический (целочисленный след Нивена `c s t k` над ℤ) — ОДНА Роль (одно
          разворачивание) под ДВУМЯ представлениями Элементов; потому завершаемость геометрии
          доказуема арифметической обструкцией (`bridge`). И то, что ГАУССОВЫ ЦЕЛЫЕ ℤ[i] ОКАЗАЛИСЬ
          НЕ НУЖНЫ, — та же истина в другой форме: я принял более богатую ОБЛАСТЬ Элементов за
          необходимость, тогда как Роль (процесс / его завершаемость) ИНВАРИАНТНА К ПРЕДСТАВЛЕНИЮ —
          хватает минимального верного (целочисленный след). Эхо урока F-8/F-9: «два имени = артефакт
          представления, не онтологическое различие».

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa.
From ToS Require Import stdlib.NivenGeneral.
From ToS Require Import stdlib.PythagoreanTriples.
From ToS Require Import analysis.Sqrt3Irrational.
Open Scope Q_scope.

(* ===================================================================== *)
(*  The cmul-orbit: cpow (a,b) k = (a,b)^k = (cos kθ, sin kθ)             *)
(* ===================================================================== *)

Fixpoint cpow (p : Q * Q) (k : nat) : Q * Q :=
  match k with
  | O => (1, 0)
  | S j => cmul p (cpow p j)
  end.

Lemma cpow_S : forall p k, cpow p (S k) = cmul p (cpow p k).
Proof. reflexivity. Qed.

Lemma fst_cpow_S : forall a b k,
  fst (cpow (a, b) (S k)) == a * fst (cpow (a, b) k) - b * snd (cpow (a, b) k).
Proof. intros a b k. rewrite cpow_S. cbn [cmul fst snd]. reflexivity. Qed.

Lemma snd_cpow_S : forall a b k,
  snd (cpow (a, b) (S k)) == a * snd (cpow (a, b) k) + b * fst (cpow (a, b) k).
Proof. intros a b k. rewrite cpow_S. cbn [cmul fst snd]. reflexivity. Qed.

(* ===================================================================== *)
(*  (1) Chebyshev recurrence on the first coordinate (needs a²+b²=1)     *)
(* ===================================================================== *)

Lemma chebyshev_fst : forall a b : Q, a*a + b*b == 1 -> forall k,
  fst (cpow (a, b) (S (S k)))
  == 2 * a * fst (cpow (a, b) (S k)) - fst (cpow (a, b) k).
Proof.
  intros a b H k.
  rewrite (fst_cpow_S a b (S k)).
  rewrite (fst_cpow_S a b k).
  rewrite (snd_cpow_S a b k).
  set (A := fst (cpow (a, b) k)).
  set (B := snd (cpow (a, b) k)).
  assert (Hkey : a * (a * A - b * B) - b * (a * B + b * A)
               == (2 * a * (a * A - b * B) - A) + A * (1 - (a*a + b*b))) by ring.
  rewrite Hkey, H. ring.
Qed.

(* ===================================================================== *)
(*  inject_Z is a ring homomorphism Z → Q (the facts we need)            *)
(* ===================================================================== *)

Lemma injZ_mult : forall a b : Z, inject_Z (a * b) == inject_Z a * inject_Z b.
Proof. intros a b. unfold inject_Z, Qmult, Qeq. simpl. ring. Qed.

Lemma injZ_sub : forall a b : Z, inject_Z (a - b) == inject_Z a - inject_Z b.
Proof. intros a b. unfold inject_Z, Qminus, Qplus, Qopp, Qeq. simpl. ring. Qed.

Lemma injZ_1 : inject_Z 1 == 1.
Proof. reflexivity. Qed.

Lemma injZ_2 : inject_Z 2 == 2.
Proof. reflexivity. Qed.

Lemma injZ_inj : forall a b : Z, inject_Z a == inject_Z b -> a = b.
Proof. intros a b H. unfold inject_Z, Qeq in H. simpl in H. lia. Qed.

(* ===================================================================== *)
(*  (2) THE BRIDGE: 2·tᵏ·fst(cpow (a,b) k) = c s t k   (2a = s/t)         *)
(* ===================================================================== *)

Lemma bridge : forall (a b : Q) (s t : Z),
  a*a + b*b == 1 -> inject_Z s == 2 * a * inject_Z t ->
  forall k, 2 * inject_Z (tpow t k) * fst (cpow (a, b) k) == inject_Z (c s t k).
Proof.
  intros a b s t Hcirc Hst.
  assert (Hpair : forall k,
    (2 * inject_Z (tpow t k) * fst (cpow (a, b) k) == inject_Z (c s t k)) /\
    (2 * inject_Z (tpow t (S k)) * fst (cpow (a, b) (S k)) == inject_Z (c s t (S k)))).
  { induction k as [|k [IHk IHSk]].
    - split.
      + (* k = 0 *) vm_compute. reflexivity.
      + (* k = 1 *)
        change (tpow t 1) with (t * 1)%Z.
        change (c s t 1) with s.
        change (fst (cpow (a, b) 1)) with (a * 1 - b * 0).
        rewrite (injZ_mult t 1), injZ_1, Hst. ring.
    - split.
      + exact IHSk.
      + (* k → S (S k) *)
        rewrite (chebyshev_fst a b Hcirc k).
        rewrite (c_rec s t k).
        rewrite injZ_sub.
        rewrite (injZ_mult s (c s t (S k))).
        rewrite (injZ_mult (t * t) (c s t k)).
        rewrite <- IHSk, <- IHk.
        rewrite Hst.
        change (tpow t (S (S k))) with (t * (t * tpow t k))%Z.
        change (tpow t (S k)) with (t * tpow t k)%Z.
        rewrite !injZ_mult.
        ring. }
  intro k. exact (proj1 (Hpair k)).
Qed.

(* ===================================================================== *)
(*  (3)–(5) THE CAPSTONE: finite order ⟹ exactly Z₄                      *)
(* ===================================================================== *)

Theorem capstone_only_Z4_terminates : forall (a b : Q) (s t : Z),
  on_circle a b ->
  inject_Z s == 2 * a * inject_Z t ->
  (Z.gcd s t = 1)%Z -> (0 < t)%Z ->
  (exists n, (1 <= n)%nat /\ fst (cpow (a, b) n) == 1) ->
  (a == 1 /\ b == 0) \/ (a == -1 /\ b == 0) \/
  (a == 0 /\ b == 1) \/ (a == 0 /\ b == -1).
Proof.
  intros a b s t Hcirc Hst Hgcd Hpos [n [Hn Hfst]].
  unfold on_circle in Hcirc.
  (* (3) the bridge at n, with fst(cpow n) = 1 *)
  pose proof (bridge a b s t Hcirc Hst n) as Hbr.
  rewrite Hfst in Hbr.
  assert (Hceq : (c s t n = 2 * tpow t n)%Z).
  { apply injZ_inj. rewrite injZ_mult, injZ_2, <- Hbr. ring. }
  assert (Htdiv : (t | c s t n)%Z).
  { rewrite Hceq. apply Z.divide_mul_r. apply tpow_div. exact Hn. }
  (* (4) Niven: t ≥ 2 is impossible, so t = 1 *)
  assert (Ht1 : t = 1%Z).
  { destruct (Z.le_gt_cases 2 t) as [Ht2 | Ht2]; [ | lia ].
    exfalso. destruct n as [|m]; [ lia | ].
    exact (niven_general s t Hgcd Ht2 m Htdiv). }
  subst t.
  rewrite injZ_1 in Hst.
  assert (Hsa : inject_Z s == 2 * a) by (rewrite Hst; ring).
  (* |a| ≤ 1, so s² ≤ 4, so −2 ≤ s ≤ 2 *)
  assert (Hb2 : 0 <= b * b) by apply Qsqr_nonneg'.
  assert (Ha2 : a * a <= 1) by lra.
  assert (Hss4 : inject_Z (s * s) <= inject_Z 4).
  { assert (H4 : inject_Z 4 == 4) by (vm_compute; reflexivity).
    rewrite injZ_mult, H4, Hsa.
    assert (Hsq : (2 * a) * (2 * a) == 4 * (a * a)) by ring.
    rewrite Hsq. lra. }
  assert (Hsbound : (-2 <= s <= 2)%Z).
  { rewrite <- Zle_Qle in Hss4. nia. }
  (* (5) enumerate s ∈ {−2,−1,0,1,2}; √3 kills ±1 *)
  assert (Hs5 : (s = -2 \/ s = -1 \/ s = 0 \/ s = 1 \/ s = 2)%Z) by lia.
  destruct Hs5 as [E | [E | [E | [E | E]]]]; subst s.
  - (* s = -2: a = -1, b = 0 *)
    assert (Hi : inject_Z (-2) == -2) by (vm_compute; reflexivity).
    rewrite Hi in Hsa.
    assert (Ha : a == -1) by lra.
    right; left. split; [ exact Ha | ].
    assert (Haa : a * a == 1) by (rewrite Ha; ring).
    assert (Hbb : b * b == 0) by lra.
    apply Qmult_integral in Hbb. destruct Hbb; assumption.
  - (* s = -1: a = -1/2, b² = 3/4 — impossible *)
    exfalso.
    assert (Hi : inject_Z (-1) == -1) by (vm_compute; reflexivity).
    rewrite Hi in Hsa.
    assert (Ha : a == -(1#2)) by lra.
    assert (Haa : a * a == 1#4) by (rewrite Ha; vm_compute; reflexivity).
    assert (Hbb : b * b == 3#4) by lra.
    apply (no_rational_sqrt3 (2 * b)).
    assert (Hexp : (2 * b) * (2 * b) == 4 * (b * b)) by ring.
    rewrite Hexp, Hbb. vm_compute. reflexivity.
  - (* s = 0: a = 0, b = ±1 *)
    assert (Hi : inject_Z 0 == 0) by (vm_compute; reflexivity).
    rewrite Hi in Hsa.
    assert (Ha : a == 0) by lra.
    assert (Haa : a * a == 0) by (rewrite Ha; ring).
    assert (Hbb : b * b == 1) by lra.
    assert (Hfac : (b - 1) * (b + 1) == 0).
    { assert (Hr : (b - 1) * (b + 1) == b * b - 1) by ring.
      rewrite Hr, Hbb. ring. }
    apply Qmult_integral in Hfac. destruct Hfac as [Hb1 | Hb2'].
    + right; right; left.  split; [ exact Ha | lra ].
    + right; right; right. split; [ exact Ha | lra ].
  - (* s = 1: a = 1/2, b² = 3/4 — impossible *)
    exfalso.
    assert (Hi : inject_Z 1 == 1) by (vm_compute; reflexivity).
    rewrite Hi in Hsa.
    assert (Ha : a == 1#2) by lra.
    assert (Haa : a * a == 1#4) by (rewrite Ha; vm_compute; reflexivity).
    assert (Hbb : b * b == 3#4) by lra.
    apply (no_rational_sqrt3 (2 * b)).
    assert (Hexp : (2 * b) * (2 * b) == 4 * (b * b)) by ring.
    rewrite Hexp, Hbb. vm_compute. reflexivity.
  - (* s = 2: a = 1, b = 0 *)
    assert (Hi : inject_Z 2 == 2) by (vm_compute; reflexivity).
    rewrite Hi in Hsa.
    assert (Ha : a == 1) by lra.
    left. split; [ exact Ha | ].
    assert (Haa : a * a == 1) by (rewrite Ha; ring).
    assert (Hbb : b * b == 0) by lra.
    apply Qmult_integral in Hbb. destruct Hbb; assumption.
Qed.

(* ===================================================================== *)
(*  The converse: the four Z₄ points DO terminate (close to (1,0))       *)
(* ===================================================================== *)

Theorem Z4_terminates :
  fst (cpow (1, 0) 1) == 1 /\
  fst (cpow (-1, 0) 2) == 1 /\
  fst (cpow (0, 1) 4) == 1 /\
  fst (cpow (0, -1) 4) == 1.
Proof. repeat split; vm_compute; reflexivity. Qed.
