(** * AnomalyChargeQuantization.v — the EXACT/COUNTING side (the dual of the walls): Standard-Model gauge
      ANOMALY CANCELLATION as pure integer arithmetic, and the DERIVATION it yields -- the hypercharge
      pattern is FORCED up to normalization, hence ELECTRIC CHARGE is QUANTIZED (proton +1, neutron 0).

    This is where ToS has a genuine edge: anomaly freedom is exact integer/rational counting, not real
    analysis.  The result is a DERIVATION (consistency forces the charges), not a re-description.

    -- One generation, all-left-handed Weyl, hypercharges in units of 1/6 (so everything is an integer):
         Q (quark doublet)  Y = 1     mult 6 = color 3 x isospin 2
         u^c                Y = -4    mult 3
         d^c                Y = 2     mult 3
         L (lepton doublet) Y = -3    mult 2 = isospin 2
         e^c                Y = 6     mult 1

    -- The five anomaly conditions, all = 0 exactly over Z:
         A1 [SU(3)]^2 U(1) (colored, isospin-weighted):  2*YQ + Yu + Yd                       = 0
         A2 [SU(2)]^2 U(1) (doublets, color-weighted):   3*YQ + YL                            = 0
         A4 [grav]^2 U(1)  (all, full mult):             6*YQ + 3*Yu + 3*Yd + 2*YL + Ye       = 0
         A3 [U(1)]^3       (all, full mult, cubed):      6*YQ^3 + 3*Yu^3 + 3*Yd^3 + 2*YL^3+Ye^3 = 0
         A5 Witten SU(2)   (number of doublets even):    3 (from Q) + 1 (from L) = 4           even

    -- The derivation (consistency forces the pattern):
         (linear, Yukawa route)  the anomaly + Yukawa gauge-invariance constraints are a LINEAR system that
              forces (YL,Yu,Yd,Ye) = (-3,-4,2,6)*YQ up to the normalization YQ (hypercharges_forced).
         (cubic route)           A1 gives Yu+Yd = -2*YQ and A3 gives Yu*Yd = -8*YQ^2; by Vieta these two
              force {Yu,Yd} = {2*YQ, -4*YQ} (split_forced) -- so the cubic anomaly fixes the up/down split.

    -- Charge quantization: with Q_em = Y + T3 (units of 1/6, T3 = +-3 on a doublet), the electric charges
       are INTEGERS (in units of 1/6): u = 4, d = -2, e = -6, nu = 0; hence proton (uud) = +1 and neutron
       (udd) = 0 (proton_neutron).  Charge is quantized, and p/n charges are DERIVED.

    -- HONEST scope: one generation; a KNOWN result (anomaly freedom constrains hypercharges), here given the
       right (counting) ontology and machine-verified EXACTLY over Z, with the full chain to p/n charges.
       Not new physics; a new exact, verified derivation.  (Higgs Y_H sign is convention-dependent.)

    Elements: hypercharges (units 1/6) = (1,-4,2,-3,6); multiplicities (6,3,3,2,1); the 5 anomaly sums; charges
    Roles:    hypercharges = conserved charges; multiplicities = counts; anomaly = a count that must vanish
    Rules:    consistency = anomaly freedom (exact Z conditions) forces the pattern => charge quantization

    ============ E/R/R разбор ============
      Rules (L5): консистентность = свобода от аномалий = точные ℤ-условия на гиперзаряды; вынуждают паттерн.
      Roles (L4): гиперзаряды = сохраняемые заряды; мультиплетности = счёты; аномалия = обнуляемый счёт.
      Elements  : паттерн (1,-4,2,-3,6) units 1/6; мульт (6,3,3,2,1); 5 сумм; электрозаряды целые.
    ДИАГНОСТИКА (P4): точная/счётная сторона (дуал стен). Аномалии = чистая ℤ-арифметика. Условия ВЫНУЖДАЮТ
    паттерн (линейно/Юкава; либо A3 через Виета yu*yd=-8yq^2) => квантование заряда => протон +1, нейтрон 0,
    машинно. ЧЕСТНО: одно поколение; известный результат, редко машинно-проверенный точно, здесь в счётной
    онтологии + полная цепь до p/n. Не новая физика -- новая верифицированная точная деривация.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import ZArith Lia Arith.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The SM hypercharge pattern (one generation, units of 1/6)              *)
(* ===================================================================== *)

Definition YQ : Z := 1.    (* quark doublet *)
Definition Yu : Z := -4.   (* u^c *)
Definition Yd : Z := 2.    (* d^c *)
Definition YL : Z := -3.   (* lepton doublet *)
Definition Ye : Z := 6.    (* e^c *)

(* ===================================================================== *)
(*  The five anomaly conditions cancel exactly (over Z)                    *)
(* ===================================================================== *)

(** A1: [SU(3)]^2 U(1) -- colored fermions, isospin-weighted. *)
Lemma anomaly_color : 2*YQ + Yu + Yd = 0.
Proof. reflexivity. Qed.

(** A2: [SU(2)]^2 U(1) -- SU(2) doublets, color-weighted. *)
Lemma anomaly_weak : 3*YQ + YL = 0.
Proof. reflexivity. Qed.

(** A4: [grav]^2 U(1) -- all fermions, full multiplicity. *)
Lemma anomaly_grav : 6*YQ + 3*Yu + 3*Yd + 2*YL + Ye = 0.
Proof. reflexivity. Qed.

(** A3: [U(1)]^3 -- all fermions, full multiplicity, cubed. *)
Lemma anomaly_cubic :
  6*(YQ*YQ*YQ) + 3*(Yu*Yu*Yu) + 3*(Yd*Yd*Yd) + 2*(YL*YL*YL) + Ye*Ye*Ye = 0.
Proof. reflexivity. Qed.

(** A5: Witten SU(2) global anomaly -- number of doublets must be even (Q: 3 colors, L: 1). *)
Definition n_doublets : nat := 3 + 1.
Lemma anomaly_witten : Nat.even n_doublets = true.
Proof. reflexivity. Qed.

(** ★ All five gauge anomalies cancel exactly. *)
Lemma all_anomalies_cancel :
  2*YQ + Yu + Yd = 0
  /\ 3*YQ + YL = 0
  /\ 6*YQ + 3*Yu + 3*Yd + 2*YL + Ye = 0
  /\ 6*(YQ*YQ*YQ) + 3*(Yu*Yu*Yu) + 3*(Yd*Yd*Yd) + 2*(YL*YL*YL) + Ye*Ye*Ye = 0
  /\ Nat.even n_doublets = true.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================== *)
(*  Derivation 1 (linear / Yukawa): the pattern is FORCED up to scale      *)
(* ===================================================================== *)

(** ★ The anomaly + Yukawa gauge-invariance constraints form a LINEAR system that forces all hypercharges
    in terms of the single normalization yq.  (yh = Higgs hypercharge; its sign is convention.) *)
Lemma hypercharges_forced :
  forall yq yu yd yl ye yh : Z,
    3*yq + yl = 0 ->                       (* A2 weak anomaly *)
    yq + yd + yh = 0 ->                     (* d-Yukawa:  Q d^c H *)
    yq + yu - yh = 0 ->                     (* u-Yukawa:  Q u^c H~ *)
    yl + ye + yh = 0 ->                     (* e-Yukawa:  L e^c H *)
    6*yq + 3*yu + 3*yd + 2*yl + ye = 0 ->   (* A4 grav *)
    yl = -3*yq /\ yu = -4*yq /\ yd = 2*yq /\ ye = 6*yq /\ yh = -3*yq.
Proof.
  intros yq yu yd yl ye yh HA2 Hd Hu He HA4. repeat split; lia.
Qed.

(* ===================================================================== *)
(*  Derivation 2 (cubic / Vieta): A1 + A3 fix the up/down split            *)
(* ===================================================================== *)

(** ★ Given Yu+Yd = -2*yq (A1) and Yu*Yd = -8*yq^2 (the content of the cubic A3), Vieta forces the split
    {Yu,Yd} = {2*yq, -4*yq}: the cubic anomaly fixes the up/down assignment. *)
Lemma split_forced : forall yu yd yq : Z,
  yu + yd = -2*yq -> yu*yd = -8*yq*yq ->
  (yu = 2*yq /\ yd = -4*yq) \/ (yu = -4*yq /\ yd = 2*yq).
Proof.
  intros yu yd yq Hsum Hprod.
  assert (Hfact : (yu - 2*yq) * (yu + 4*yq) = 0).
  { replace ((yu - 2*yq) * (yu + 4*yq))
      with (yu*(yu + yd + 2*yq) - (yu*yd + 8*yq*yq)) by ring.
    assert (Ha : yu + yd + 2*yq = 0) by lia.
    assert (Hb : yu*yd + 8*yq*yq = 0) by lia.
    rewrite Ha, Hb. ring. }
  apply Z.mul_eq_0 in Hfact. destruct Hfact as [H | H].
  - left.  split; lia.
  - right. split; lia.
Qed.

(** The SM pattern supplies exactly the Vieta data (sum and product) the cubic route needs. *)
Lemma sm_vieta : Yu + Yd = -2*YQ /\ Yu*Yd = -8*YQ*YQ.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Charge quantization: proton +1, neutron 0 (derived)                    *)
(* ===================================================================== *)

(** Electric charge Q_em = Y + T3 (units of 1/6; T3 = +-3 on a doublet component). *)
Definition Qem_up   : Z := YQ + 3.    (* u: 1+3 = 4  -> +2/3 *)
Definition Qem_down : Z := YQ - 3.    (* d: 1-3 = -2 -> -1/3 *)
Definition Qem_elec : Z := YL - 3.    (* e: -3-3 = -6 -> -1  *)
Definition Qem_nu   : Z := YL + 3.    (* nu: -3+3 = 0        *)

(** ★ The electric charges are INTEGERS (in units of 1/6): quantization. *)
Lemma charges_quantized :
  Qem_up = 4 /\ Qem_down = -2 /\ Qem_elec = -6 /\ Qem_nu = 0.
Proof. repeat split; reflexivity. Qed.

(** ★ Proton (uud) = +1 (= 6 units of 1/6); neutron (udd) = 0.  Derived from the forced pattern. *)
Lemma proton_neutron :
  2*Qem_up + Qem_down = 6 /\ Qem_up + 2*Qem_down = 0.
Proof. split; reflexivity. Qed.

(* ===================================================================== *)
(*  Capstone: anomaly freedom => charge quantization                       *)
(* ===================================================================== *)

(** The exact/counting result:
      (anomalies)  all five SM gauge anomalies cancel exactly over Z;
      (forced)     the anomaly (+ Yukawa) constraints force the hypercharge pattern up to normalization
                   (hypercharges_forced); the cubic alone fixes the up/down split by Vieta (split_forced);
      (quantized)  the electric charges are integers (units of 1/6): u=4, d=-2, e=-6, nu=0;
      (p/n)        proton (uud) = +1 and neutron (udd) = 0.
    Consistency (anomaly freedom) forces the charges -- a derivation, machine-verified exactly over Z, in
    the counting ontology where ToS has its edge. *)
Theorem anomaly_charge_quantization :
  (2*YQ + Yu + Yd = 0
   /\ 3*YQ + YL = 0
   /\ 6*YQ + 3*Yu + 3*Yd + 2*YL + Ye = 0
   /\ 6*(YQ*YQ*YQ) + 3*(Yu*Yu*Yu) + 3*(Yd*Yd*Yd) + 2*(YL*YL*YL) + Ye*Ye*Ye = 0)
  /\ (forall yq yu yd yl ye yh : Z,
        3*yq + yl = 0 -> yq + yd + yh = 0 -> yq + yu - yh = 0 -> yl + ye + yh = 0 ->
        6*yq + 3*yu + 3*yd + 2*yl + ye = 0 ->
        yl = -3*yq /\ yu = -4*yq /\ yd = 2*yq /\ ye = 6*yq /\ yh = -3*yq)
  /\ (Qem_up = 4 /\ Qem_down = -2 /\ Qem_elec = -6 /\ Qem_nu = 0)
  /\ (2*Qem_up + Qem_down = 6 /\ Qem_up + 2*Qem_down = 0).
Proof.
  split; [ repeat split; reflexivity | ].
  split; [ exact hypercharges_forced | ].
  split; [ exact charges_quantized | exact proton_neutron ].
Qed.
