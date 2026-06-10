(** * CayleyFourierMassBridge.v — ONE Cayley map (4−λ²)/(4+λ²) is BOTH the Fourier/DFT transfer
       eigenvalue (analysis cluster) AND the lattice mass-gap input (lattice cluster), and it is a
       RATIONAL point of the unit circle (q-kinematics) — so the lattice masses are PYTHAGOREAN.
       Sews three clusters (analysis ↔ lattice ↔ geometry) that share the formula but had NO shared import.

    THE OBSERVATION (the surprising edge from the Cayley-hub audit).
    Two clusters independently define, with NO shared import, the byte-identical rational map
        C(λ) = (4 − λ²) / (4 + λ²) :
      - analysis/FourierCayleyConnection.v:37  as `cayley_eigenvalue` — the DFT transfer eigenvalue
        (Cayley image of a cycle-graph Laplacian eigenvalue λ; T^K eigenvalue = C(λ)^K);
      - lattice/MassFromSpectrum.v:34          as `Re_cayley` — the Euclidean transfer eigenvalue
        whose log is the lattice mass gap (mass proxy = 1 − |C(λ)|, mass = −ln|C(λ)|).
    They are LITERALLY the same function. Hence the lattice mass gap IS a function of the Fourier
    transfer eigenvalue, through one Cayley map. No file states this; this one does.

    THE CIRCLE / PYTHAGOREAN READING (link to H62 + q-kinematics).
    With the imaginary part Im(λ) = 4λ/(4+λ²) (= cayley_im, physics/AlphaBareLattice.v:25),
        C(λ)² + Im(λ)² = 1   —   C(λ) is the tangent-half-angle point of the UNIT CIRCLE.
    So every lattice transfer eigenvalue is a RATIONAL circle point (q-kinematics / RationalRotationGroup),
    and the concrete Z³ masses come out Pythagorean:
        C(4) = −3/5   (3-4-5),   C(8) = −15/17  (8-15-17),   C(12) = −35/37  (12-35-37).
    This is WHY the lattice masses are rational Elements (vein A / H62): the gap eigenvalue is a rational
    circle point. The Cayley map is the universal rationalizer (the candidate 6th vein) that ties the
    spectral arm (Fourier↔mass) to the geometry rational-circle arm.

    WHAT IS NEW / HONEST SCALE.
    Each fact is classical: the Cayley transform (1846), the tangent-half-angle / rational-circle
    parametrization, transfer-eigenvalue powers, mass = −ln|transfer eigenvalue|. NEW (synthesis+
    observation, all machine-checked): the cross-cluster UNIFICATION — that ONE Cayley map is the
    Fourier transfer eigenvalue, the lattice mass-gap input, AND a rational circle point, so the
    lattice masses are Pythagorean — a connection that was invisible because the clusters share no
    import. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : единая рациональная функция C(λ)=(4−λ²)/(4+λ²); её Fourier-имя `cayley_eigenvalue`
                 (собств. значение трансфера), её lattice-имя `Re_cayley` (евклид. собств. значение щели),
                 мнимая часть `cayley_im`=4λ/(4+λ²); опорные λ∈{0,4,8,12}.
      Roles    : C(λ) = Кэли-образ собств. значения связи λ (off-diagonal); Fourier-роль = собств. значение
                 трансфера T^K=C(λ)^K; lattice-роль = вход масс-щели m=−ln|C(λ)|; (C,Im) = рациональная
                 точка единичной окружности (q-kinematics).
      Rules    : `cayley_eigenvalue ≡ Re_cayley` (одна функция, два кластера, reflexivity); m_proxy=1−|C(λ)|;
                 C²+Im²=1 (единичная окружность); опорные значения пифагоровы (−3/5↔3-4-5, −15/17↔8-15-17,
                 −35/37↔12-35-37).
      ДИАГНОСТИКА (P4): масс-щель решётки = функция Fourier-собств-значения через ОДНО Кэли; нулевая мода =
      безмассовая (неподвижная точка Кэли C(0)=1); все массы = рациональные точки окружности ⟹ пифагоровы ⟹
      Element (вена A / H62). Кросс-кластерная связь, бывшая невидимой (нет общего импорта), сделана машинной.
      ЧЕСТНО: классическое tangent-half-angle тождество + перенос; новое — унификация трёх кластеров одной
      функцией. Уровень: `синтез+наблюдение`.

    STATUS: 9 Qed, 0 Admitted, 0 axioms  (imports analysis.FourierCayleyConnection + lattice.MassFromSpectrum)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia.
From ToS Require Import analysis.FourierCayleyConnection.
From ToS Require Import lattice.MassFromSpectrum.

Open Scope Q_scope.

(* ===================================================================== *)
(*  1. THE LITERAL IDENTITY: two cluster definitions, ONE function         *)
(* ===================================================================== *)

(** ★★ The Fourier transfer eigenvalue (analysis) and the Euclidean mass-gap eigenvalue (lattice) are
    LITERALLY the same Cayley map — `reflexivity` on the unfolded definitions. Two clusters, no shared
    import, one function. *)
Theorem cayley_fourier_is_mass : forall lambda,
  cayley_eigenvalue lambda == Re_cayley lambda.
Proof. intro lambda. unfold cayley_eigenvalue, Re_cayley. reflexivity. Qed.

(* ===================================================================== *)
(*  2. CONSEQUENCE: the mass gap is a function of the FOURIER eigenvalue   *)
(* ===================================================================== *)

(** The lattice mass proxy expressed through the FOURIER transfer eigenvalue: mass = 1 − |Fourier eig|. *)
Corollary mass_proxy_via_fourier : forall lambda,
  mass_proxy lambda == 1 - Qabs (cayley_eigenvalue lambda).
Proof.
  intro lambda. unfold mass_proxy. rewrite <- cayley_fourier_is_mass. reflexivity.
Qed.

(** The Fourier transfer eigenvalue at K=1 IS the Euclidean transfer eigenvalue feeding the mass. *)
Corollary fourier_transfer_is_euclid : forall lambda,
  transfer_eigenvalue lambda 1 == Re_cayley lambda.
Proof. intro lambda. rewrite transfer_K1. apply cayley_fourier_is_mass. Qed.

(** Concrete: the λ=4 lattice mass proxy 2/5, expressed via the Fourier eigenvalue. *)
Example mass_4_via_fourier : 1 - Qabs (cayley_eigenvalue 4) == 2 # 5.
Proof. rewrite <- mass_proxy_via_fourier. exact mass_proxy_4_value. Qed.

(* ===================================================================== *)
(*  3. THE ZERO MODE: Fourier zero mode = massless mode (one fixed point)  *)
(* ===================================================================== *)

(** The graph zero mode λ=0 is the Cayley fixed point (C(0)=1) AND the massless mode (proxy 0): the
    Fourier zero mode and the massless mode are the SAME mode. *)
Theorem zero_mode_is_massless :
  cayley_eigenvalue 0 == 1 /\ mass_proxy 0 == 0.
Proof. split; [ exact cayley_zero | exact mass_proxy_0 ]. Qed.

(** The number 3/5 surfaces in BOTH clusters from ONE map: Fourier C(1)=3/5 and the magnitude of the
    lattice λ=4 mass eigenvalue Re_cayley(4)=−3/5. *)
Lemma three_fifths_both : cayley_eigenvalue 1 == 3 # 5 /\ Re_cayley 4 == -(3 # 5).
Proof. split; [ exact cayley_at_1 | exact Re_cayley_4 ]. Qed.

(* ===================================================================== *)
(*  4. The Cayley eigenvalue is a RATIONAL point of the UNIT CIRCLE        *)
(* ===================================================================== *)

(** The Cayley imaginary part (= cayley_im, physics/AlphaBareLattice.v:25). *)
Definition cayley_im (lambda : Q) : Q := (4 * lambda) / (4 + lambda * lambda).

(** ★ C(λ)² + Im(λ)² = 1: the Cayley map lands on the UNIT CIRCLE — the rational tangent-half-angle
    point (q-kinematics / RationalRotationGroup). So every lattice transfer eigenvalue is a rational
    circle point. *)
Lemma cayley_on_unit_circle : forall lambda,
  ~ (4 + lambda * lambda == 0) ->
  Re_cayley lambda * Re_cayley lambda + cayley_im lambda * cayley_im lambda == 1.
Proof.
  intros lambda Hnz. unfold Re_cayley, cayley_im. field. exact Hnz.
Qed.

(* ===================================================================== *)
(*  5. The lattice masses are PYTHAGOREAN (rational circle points)         *)
(* ===================================================================== *)

(** The Z³ lattice transfer eigenvalues are rational circle points = Pythagorean numerators:
      C(4) = −3/5   → legs (3,4),  hyp 5;
      C(8) = −15/17 → legs (15,8), hyp 17;
      C(12)= −35/37 → legs (35,12),hyp 37.
    This is WHY the lattice masses are rational Elements (vein A / H62): the gap eigenvalue is a
    rational circle point. *)
Theorem lattice_masses_pythagorean :
  Re_cayley 4 == -(3 # 5) /\ Re_cayley 8 == -(15 # 17) /\ Re_cayley 12 == -(35 # 37)
  /\ (3 * 3 + 4 * 4 = 5 * 5)%Z
  /\ (15 * 15 + 8 * 8 = 17 * 17)%Z
  /\ (35 * 35 + 12 * 12 = 37 * 37)%Z.
Proof.
  split. exact Re_cayley_4.
  split. exact Re_cayley_8.
  split. exact Re_cayley_12.
  split. reflexivity.
  split. reflexivity.
  reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ONE Cayley map (4−λ²)/(4+λ²), read across three clusters:
      (one map)     cayley_eigenvalue ≡ Re_cayley — Fourier transfer eig = lattice mass-gap input;
      (mass)        mass proxy = 1 − |Fourier eigenvalue|;
      (zero mode)   the Fourier zero mode is the massless mode (Cayley fixed point C(0)=1);
      (circle)      C(λ)² + Im(λ)² = 1 — a rational point of the unit circle (q-kinematics);
      (Pythagorean) the Z³ masses C(4),C(8),C(12) = −3/5,−15/17,−35/37 are Pythagorean (vein A / H62).
    The Cayley map is the universal rationalizer joining the spectral arm (Fourier↔mass) to the
    geometry rational-circle arm. Honest: classical pieces, machine-checked cross-cluster unification. *)
Theorem cayley_fourier_mass_bridge :
  (forall lambda, cayley_eigenvalue lambda == Re_cayley lambda)
  /\ (forall lambda, mass_proxy lambda == 1 - Qabs (cayley_eigenvalue lambda))
  /\ (forall lambda, transfer_eigenvalue lambda 1 == Re_cayley lambda)
  /\ (cayley_eigenvalue 0 == 1 /\ mass_proxy 0 == 0)
  /\ (forall lambda, ~ (4 + lambda * lambda == 0) ->
        Re_cayley lambda * Re_cayley lambda + cayley_im lambda * cayley_im lambda == 1)
  /\ (Re_cayley 4 == -(3 # 5) /\ Re_cayley 8 == -(15 # 17) /\ Re_cayley 12 == -(35 # 37)).
Proof.
  split. exact cayley_fourier_is_mass.
  split. exact mass_proxy_via_fourier.
  split. exact fourier_transfer_is_euclid.
  split. exact zero_mode_is_massless.
  split. exact cayley_on_unit_circle.
  split. exact Re_cayley_4. split. exact Re_cayley_8. exact Re_cayley_12.
Qed.
