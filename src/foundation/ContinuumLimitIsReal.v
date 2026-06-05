(** * ContinuumLimitIsReal.v — the BOTTOM of Q1: the convergent process IS the real (the P4 thesis
      "a real = a process"), not an approximation to an external object.  ContinuumLimitRoleLimit.v showed
      the Pell convergents APPROACH sqrt2 (error -> 0).  Here the move is internal: the convergents form a
      CAUCHY process whose Cauchy rate is the UNIMODULAR determinant +-1 of consecutive convergents, and
      they BRACKET sqrt2 in nested intervals (alternating sides) — so sqrt2 is uniquely PINNED by the
      process, never reached.  sqrt2 does not exist as a completed object the process chases; sqrt2 IS
      (the class of) this Cauchy process.

    -- The unimodular Cauchy rate --
      The determinant of consecutive convergents is x_{n+1} y_n - x_n y_{n+1} = - pell_val n = +-1 (the
      same unimodular +-1 as ReductionAtlasUnimodular / continued fractions).  Hence the gap between
      consecutive convergents is EXACTLY +-1/(y_n y_{n+1}):
          (r_{n+1} - r_n) * (y_n y_{n+1}) = - pell_val n = +-1.
      With y_n >= n+1 -> infinity, the gaps -> 0: the process is Cauchy with an explicit unimodular rate.

    -- The bracketing --
      The sign of r_n^2 - 2 equals the sign of pell_val n (from (r_n^2 - 2) y_n^2 = pell_val n); pell_val
      alternates +1/-1, so consecutive convergents lie on OPPOSITE sides of sqrt2 — they bracket it in
      nested shrinking intervals.  sqrt2 is the unique point pinned by the brackets, never an endpoint.

    -- Two atlas engines meet --
      sqrt2's non-reachability is the Pell invariant x^2 - 2 y^2 = +-1 (H22); the Cauchy rate is the
      unimodular determinant +-1 (atlas page II).  The SAME +-1 is both the wall and the rate.  The
      continuum limit, as a constituted process, sits on two engines of the reduction atlas at once.

    -- HONEST scope --
      The full epsilon-N Cauchy (telescoping the tail) is not derived; what is proved is the EXACT
      consecutive gap (+-1/(y_n y_{n+1})), the denominator growth (-> infinity), and the nested bracketing
      — which together ARE the constructive-real content (Cauchy rate + unique pin).  One instance (sqrt2).

    Elements: pell_det = - pell_val = +-1; gap*(y_n y_{n+1}) = +-1; sign(r_n^2-2)=sign(pell_val n); brackets
    Roles:    convergents = Element points; sqrt2 = role-limit CONSTITUTED (not chased); +-1 = Cauchy rate
    Rules:    a real = a process; the Cauchy rate is the unimodular +-1; brackets pin the unique limit

    ============ E/R/R разбор ============
      Rules (L5): онтологическое завершение: реал СОСТАВЛЯЕТСЯ Cauchy-процессом, не приближается извне.
                  Скорость Cauchy = определитель соседних конвергентов = -pell_val = +-1 (унимодуляр);
                  знак инварианта чередуется => конвергенты ЗАЖИМАЮТ sqrt2 (вложенные интервалы).
      Roles (L4): конвергенты r_n = Element-точки; sqrt2 = role-limit СОСТАВЛЯЕМЫЙ; det +-1 = скорость Cauchy
                  (атлас II); знак pell_val = сторона скобки; y_n y_{n+1} -> infinity = знаменатель шага.
      Elements  : pell_det = -pell_val = +-1; (r_{n+1}-r_n) y_n y_{n+1} = +-1; знак r^2-2 = знак pell_val.
    ДИАГНОСТИКА (P4): дно Q1 -- тезис "реал = процесс".  Машинно: процесс Cauchy (шаг = +-1/(y_n y_{n+1})
    -> 0) и зажимает sqrt2 во вложенных скобках => sqrt2 уникально пойман = СОСТАВЛЕН процессом, не достигнут.
    Две смычки с атласом: Pell (H22, x^2-2y^2=+-1 = недостижимость) + унимодуляр (атлас II, det=+-1 =
    скорость).  Тот же +-1 -- и стена, и скорость.  ЧЕСТНО: полную eps-N Cauchy не вывожу; точный шаг +
    знаменатель->infinity + зажим = конструктивно-реальное содержание; один инстанс sqrt2.

    STATUS: 9 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import foundation.ContinuumLimitRoleLimit.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The unimodular determinant of consecutive convergents                  *)
(* ===================================================================== *)

(** The determinant of consecutive convergents is - pell_val n (hence +-1). *)
Lemma pell_det_eq : forall n, px (S n) * py n - px n * py (S n) = - pell_val n.
Proof. intro n. unfold pell_val. rewrite px_succ, py_succ. ring. Qed.

(** ...so the consecutive-convergent determinant is the unimodular +-1. *)
Lemma pell_det_pm : forall n,
  px (S n) * py n - px n * py (S n) = 1 \/ px (S n) * py n - px n * py (S n) = -1.
Proof.
  intro n. rewrite pell_det_eq.
  destruct (pell_val_pm n) as [H | H]; rewrite H; [ right | left ]; reflexivity.
Qed.

(* ===================================================================== *)
(*  Sign helper                                                            *)
(* ===================================================================== *)

Lemma sign_from_product : forall A P, (0 < P)%Q -> (A * P == 1)%Q -> (0 < A)%Q.
Proof.
  intros A P HP H.
  destruct (Qlt_le_dec 0 A) as [HA | HA]; [ exact HA | exfalso ].
  assert (Hle : (A * P <= 0)%Q).
  { setoid_replace 0%Q with (0 * P)%Q by ring.
    apply Qmult_le_compat_r; [ exact HA | apply Qlt_le_weak; exact HP ]. }
  rewrite H in Hle. lra.
Qed.

(* ===================================================================== *)
(*  The Cauchy rate: consecutive gap = +-1/(y_n y_{n+1})                   *)
(* ===================================================================== *)

(** ★ The exact consecutive gap: (r_{n+1} - r_n) * (y_n y_{n+1}) = - pell_val n = +-1. *)
Lemma consecutive_gap : forall n,
  ((r (S n) - r n) * (inject_Z (py n) * inject_Z (py (S n))) == inject_Z (- pell_val n))%Q.
Proof.
  intro n.
  assert (Hn := py_inject_ne n). assert (Hsn := py_inject_ne (S n)).
  assert (Hh : (inject_Z (px (S n)) * inject_Z (py n) - inject_Z (px n) * inject_Z (py (S n))
            == inject_Z (- pell_val n))%Q).
  { rewrite <- pell_det_eq.
    replace (px (S n) * py n - px n * py (S n))%Z
       with (px (S n) * py n + - (px n * py (S n)))%Z by ring.
    rewrite inject_Z_plus, inject_Z_opp, !inject_Z_mult. ring. }
  unfold r. rewrite <- Hh. field. split; [ exact Hn | exact Hsn ].
Qed.

(* ===================================================================== *)
(*  The bracketing: consecutive convergents straddle sqrt2                 *)
(* ===================================================================== *)

(** When the Pell form is +1 the convergent is above sqrt2 (r_n^2 > 2). *)
Lemma r_above : forall n, pell_val n = 1 -> (2 < r n * r n)%Q.
Proof.
  intros n H. destruct (pxy_pos n) as [_ Hy].
  assert (Hpy : (0 < inject_Z (py n))%Q) by (unfold Qlt; simpl; lia).
  assert (HP : (0 < inject_Z (py n) * inject_Z (py n))%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hc := r_sq_close n). rewrite H in Hc.
  assert (Hc1 : ((r n * r n - 2) * (inject_Z (py n) * inject_Z (py n)) == 1)%Q)
    by (rewrite Hc; reflexivity).
  assert (HA := sign_from_product (r n * r n - 2) (inject_Z (py n) * inject_Z (py n)) HP Hc1).
  lra.
Qed.

(** When the Pell form is -1 the convergent is below sqrt2 (r_n^2 < 2). *)
Lemma r_below : forall n, pell_val n = -1 -> (r n * r n < 2)%Q.
Proof.
  intros n H. destruct (pxy_pos n) as [_ Hy].
  assert (Hpy : (0 < inject_Z (py n))%Q) by (unfold Qlt; simpl; lia).
  assert (HP : (0 < inject_Z (py n) * inject_Z (py n))%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hc := r_sq_close n). rewrite H in Hc.
  assert (Hc1 : ((2 - r n * r n) * (inject_Z (py n) * inject_Z (py n)) == 1)%Q).
  { setoid_replace ((2 - r n * r n) * (inject_Z (py n) * inject_Z (py n)))%Q
       with (- ((r n * r n - 2) * (inject_Z (py n) * inject_Z (py n))))%Q by ring.
    rewrite Hc. reflexivity. }
  assert (HA := sign_from_product (2 - r n * r n) (inject_Z (py n) * inject_Z (py n)) HP Hc1).
  lra.
Qed.

(** ★ Consecutive convergents lie on OPPOSITE sides of sqrt2 — they bracket it. *)
Lemma brackets_root : forall n,
  (2 < r n * r n /\ r (S n) * r (S n) < 2)%Q \/ (r n * r n < 2 /\ 2 < r (S n) * r (S n))%Q.
Proof.
  intro n. destruct (pell_val_pm n) as [H | H].
  - left. split.
    + apply r_above; exact H.
    + apply r_below. rewrite pell_val_neg, H. reflexivity.
  - right. split.
    + apply r_below; exact H.
    + apply r_above. rewrite pell_val_neg, H. reflexivity.
Qed.

(** Concrete gap: r_1 - r_0 = 3/2 - 1 = 1/2 = 1/(y_0 y_1) = 1/(1*2). *)
Lemma ex_gap : (r 1 - r 0 == 1 # 2)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: the continuum limit IS a real (Cauchy process, pinned)       *)
(* ===================================================================== *)

(** sqrt2 is CONSTITUTED by the convergent process, not chased:
      (gap)      consecutive convergents differ by the unimodular +-1 over y_n y_{n+1};
      (unimod)   the determinant is +-1 (atlas page II) — the Cauchy rate;
      (denom)    y_n -> infinity, so the gaps -> 0 (Cauchy);
      (brackets) consecutive convergents straddle sqrt2 — nested shrinking brackets pin it uniquely;
      (never)    no convergent equals sqrt2 (x_n^2 <> 2 y_n^2).
    A real = a process: sqrt2 is the (class of the) Cauchy process, with rate the unimodular +-1, never
    reached.  Two atlas engines — Pell (the wall) and unimodular (the rate) — meet in one limit. *)
Theorem continuum_limit_is_real :
  (forall n, ((r (S n) - r n) * (inject_Z (py n) * inject_Z (py (S n))) == inject_Z (- pell_val n))%Q)
  /\ (forall n, px (S n) * py n - px n * py (S n) = 1 \/ px (S n) * py n - px n * py (S n) = -1)
  /\ (forall n, py n >= Z.of_nat (S n))
  /\ (forall n, (2 < r n * r n /\ r (S n) * r (S n) < 2)%Q
              \/ (r n * r n < 2 /\ 2 < r (S n) * r (S n))%Q)
  /\ (forall n, px n * px n <> 2 * (py n * py n)).
Proof.
  split; [ exact consecutive_gap | ].
  split; [ exact pell_det_pm | ].
  split; [ exact py_ge | ].
  split; [ exact brackets_root | exact sqrt2_never_reached ].
Qed.
