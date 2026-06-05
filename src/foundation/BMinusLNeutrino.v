(** * BMinusLNeutrino.v — the exact/counting side, continued (after AnomalyChargeQuantization.v): gauging
      B-L FORCES the right-handed neutrino.  Exact integer arithmetic; a genuine prediction.

    Two facts:
      (a) the right-handed neutrino nu_R is a Standard-Model gauge SINGLET (Y = 0), hence anomaly-NEUTRAL
          for the SM gauge group -- adding it does not disturb the SM anomaly cancellation;
      (b) if B-L is GAUGED, its gravitational and cubic anomalies do NOT cancel for the SM fermions alone --
          a field with B-L = +1 (the nu_R) is REQUIRED, and the two conditions (grav + cubic) FIX it
          uniquely: charge 3 (units of 1/3), multiplicity 1, i.e. exactly one nu_R per generation.

    -- B-L charges in units of 1/3 (so integers), one generation:
         Q  : +1   mult 6      u^c : -1   mult 3      d^c : -1   mult 3
         L  : -3   mult 2      e^c : +3   mult 1      nu^c: +3   mult 1
       (B-L: quark = +1/3, antiquark = -1/3, lepton = -1, antilepton = +1.)

    -- B-L anomalies WITH nu_R all cancel (over Z):
         [SU(3)]^2(B-L): 2*BLq + BLu + BLd                                  = 0
         [SU(2)]^2(B-L): 3*BLq + BLl                                        = 0
         [grav]^2(B-L):  6*BLq + 3*BLu + 3*BLd + 2*BLl + BLe + BLnu         = 0
         [B-L]^3:        6*BLq^3 + 3*BLu^3 + 3*BLd^3 + 2*BLl^3 + BLe^3+BLnu^3 = 0

    -- WITHOUT nu_R, the grav and cubic anomalies have nonzero DEFICITS:
         [grav]^2(B-L) deficit = -3      [B-L]^3 deficit = -27
       so nu_R must supply +3 (grav) and +27 (cubic).

    -- The forcing (the gem): a field of B-L charge q (units 1/3) and multiplicity m cancels BOTH iff
       m*q = 3 AND m*q^3 = 27.  These overdetermine, yet are solved UNIQUELY by q = 3, m = 1 (q^2 = 9):
       exactly one nu_R with B-L = +1.  The grav (linear) and cubic conditions agree on the same field.

    -- Consequence: gauging B-L predicts the right-handed neutrino -> Dirac/seesaw neutrino mass becomes
       possible.  And nu_R is SM-anomaly-neutral, so the SM is undisturbed.

    -- HONEST scope: one generation; a KNOWN result (B-L anomaly freedom requires nu_R), here machine-verified
       EXACTLY over Z, with the overdetermination (grav AND cubic fix the same field) made explicit.

    Elements: B-L charges (units 1/3) = (1,-1,-1,-3,3,3); deficits (-3,-27); the canceller (q=3,m=1)
    Roles:    nu_R = the B-L anomaly canceller, SM-neutral; its charge & multiplicity fixed by grav + cubic
    Rules:    gauging B-L => its anomalies must vanish => a B-L=+1 field (nu_R) is forced, uniquely

    ============ E/R/R разбор ============
      Rules (L5): калибровка B-L => его аномалии обязаны обнулиться; грав/куб ненулевы для СМ => поле вынуждено.
      Roles (L4): nu_R = сократитель B-L-аномалии, СМ-нейтрален (Y=0); заряд(+1)/мульт(1) фиксированы грав+куб.
      Elements  : B-L-заряды (ед.1/3) (1,-1,-1,-3,3,3); дефициты (-3,-27); сократитель q=3,m=1.
    ДИАГНОСТИКА (P4): счётная сторона. Гем переопределения: m*q=3 И m*q^3=27 => q^2=9 => q=3,m=1 = ровно один
    nu_R (B-L=+1) на поколение; грав и куб решаются ОДНИМ полем. Предсказание: калибровка B-L => правый нейтрино
    => масса нейтрино возможна. nu_R СМ-анома-нейтрален => СМ не возмущена. Машинно, 0 аксиом. ЧЕСТНО: известный
    результат, здесь точно + гем переопределения.

    STATUS: 10 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  nu_R is a SM gauge singlet (Y = 0): anomaly-neutral for the SM         *)
(* ===================================================================== *)

Definition YnuR : Z := 0.

(** ★ nu_R contributes 0 to the linear [grav]U(1)_Y and cubic [U(1)_Y]^3 anomalies (Y = 0); it is also
    color- and isospin-singlet, so it leaves ALL five SM anomalies unchanged.  The SM is undisturbed. *)
Lemma nuR_sm_neutral : YnuR = 0 /\ YnuR*YnuR*YnuR = 0.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  B-L charges (units of 1/3) and their anomalies WITH nu_R               *)
(* ===================================================================== *)

Definition BLq  : Z := 1.    (* quark doublet *)
Definition BLu  : Z := -1.   (* u^c *)
Definition BLd  : Z := -1.   (* d^c *)
Definition BLl  : Z := -3.   (* lepton doublet *)
Definition BLe  : Z := 3.    (* e^c *)
Definition BLnu : Z := 3.    (* nu^c (right-handed neutrino) *)

Lemma bl_color : 2*BLq + BLu + BLd = 0.
Proof. reflexivity. Qed.

Lemma bl_weak : 3*BLq + BLl = 0.
Proof. reflexivity. Qed.

Lemma bl_grav : 6*BLq + 3*BLu + 3*BLd + 2*BLl + BLe + BLnu = 0.
Proof. reflexivity. Qed.

Lemma bl_cubic :
  6*(BLq*BLq*BLq) + 3*(BLu*BLu*BLu) + 3*(BLd*BLd*BLd)
  + 2*(BLl*BLl*BLl) + BLe*BLe*BLe + BLnu*BLnu*BLnu = 0.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  WITHOUT nu_R: nonzero grav and cubic deficits => nu_R required          *)
(* ===================================================================== *)

(** ★ Without nu_R the gravitational B-L anomaly does NOT cancel: deficit -3. *)
Lemma bl_grav_deficit : 6*BLq + 3*BLu + 3*BLd + 2*BLl + BLe = -3.
Proof. reflexivity. Qed.

(** ★ Without nu_R the cubic B-L anomaly does NOT cancel: deficit -27. *)
Lemma bl_cubic_deficit :
  6*(BLq*BLq*BLq) + 3*(BLu*BLu*BLu) + 3*(BLd*BLd*BLd)
  + 2*(BLl*BLl*BLl) + BLe*BLe*BLe = -27.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  The forcing: the canceller is uniquely nu_R (charge 3, mult 1)         *)
(* ===================================================================== *)

(** The nu_R (B-L charge 3, multiplicity 1) cancels BOTH deficits at once: +3 (grav) and +27 (cubic). *)
Lemma nuR_cancels_both : 1 * BLnu = 3 /\ 1 * (BLnu*BLnu*BLnu) = 27.
Proof. split; reflexivity. Qed.

(** ★ THE GEM: a field of B-L charge q and multiplicity m (m > 0) that cancels BOTH the grav deficit
    (m*q = 3) AND the cubic deficit (m*q^3 = 27) is FORCED to be q = 3, m = 1 -- exactly one nu_R with
    B-L = +1.  The two conditions overdetermine and agree (q^2 = 9). *)
Lemma nuR_forced : forall q m : Z,
  m > 0 -> m * q = 3 -> m * (q*q*q) = 27 -> q = 3 /\ m = 1.
Proof.
  intros q m Hm H1 H2.
  assert (Hq2 : q*q = 9).
  { assert (Haux : (m*q) * (q*q) = 27) by (rewrite <- H2; ring).
    rewrite H1 in Haux. lia. }
  assert (Hpos : 0 < q) by nia.
  assert (Hq3 : q = 3).
  { assert (Hfac : (q - 3) * (q + 3) = 0).
    { replace ((q - 3) * (q + 3)) with (q*q - 9) by ring. lia. }
    apply Z.mul_eq_0 in Hfac. destruct Hfac as [H | H]; lia. }
  subst q. split; [ reflexivity | lia ].
Qed.

(* ===================================================================== *)
(*  Capstone: gauging B-L forces exactly one nu_R per generation           *)
(* ===================================================================== *)

(** The exact result:
      (SM-neutral)  nu_R is a SM gauge singlet (Y = 0), anomaly-neutral -- the SM is undisturbed;
      (B-L cancels) with nu_R, all B-L anomalies (color, weak, grav, cubic) vanish over Z;
      (forced)      without nu_R the grav and cubic B-L anomalies have deficits -3 and -27; a field that
                    cancels BOTH is uniquely q = 3, m = 1 (nuR_forced) -- exactly one nu_R, B-L = +1.
    Gauging B-L predicts the right-handed neutrino (hence Dirac/seesaw neutrino mass).  A counting-side
    derivation, machine-verified exactly over Z. *)
Theorem b_minus_l_forces_neutrino :
  (YnuR = 0)
  /\ (6*BLq + 3*BLu + 3*BLd + 2*BLl + BLe + BLnu = 0
      /\ 6*(BLq*BLq*BLq) + 3*(BLu*BLu*BLu) + 3*(BLd*BLd*BLd)
         + 2*(BLl*BLl*BLl) + BLe*BLe*BLe + BLnu*BLnu*BLnu = 0)
  /\ (6*BLq + 3*BLu + 3*BLd + 2*BLl + BLe = -3
      /\ 6*(BLq*BLq*BLq) + 3*(BLu*BLu*BLu) + 3*(BLd*BLd*BLd)
         + 2*(BLl*BLl*BLl) + BLe*BLe*BLe = -27)
  /\ (forall q m : Z, m > 0 -> m * q = 3 -> m * (q*q*q) = 27 -> q = 3 /\ m = 1).
Proof.
  split; [ reflexivity | ].
  split; [ split; reflexivity | ].
  split; [ split; reflexivity | exact nuR_forced ].
Qed.
