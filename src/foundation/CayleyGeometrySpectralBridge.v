(** * CayleyGeometrySpectralBridge.v — the GEOMETRY arm of the Cayley (6th) vein: the spectral
       transfer eigenvalue (4−λ²)/(4+λ²) is a rational point of the UNIT CIRCLE = an element of the
       rational rotation group SO(2,ℚ); the lattice mass eigenvalue is the cosine of a rational rotation.
       Closes vein F's geometry arm to its (already-bridged) spectral arm — ONE Cayley map, t=λ/2.

    THE OBSERVATION.
    The spectral Cayley point (Re_cayley λ, cayley_im λ) = ((4−λ²)/(4+λ²), 4λ/(4+λ²)) — the lattice
    transfer eigenvalue (MassFromSpectrum.v:34) plus its imaginary part (AlphaBareLattice.v:25) — is
    EXACTLY the SO(2,ℚ) Cayley / tangent-half-angle rotation chart ((1−s²)/(1+s²), 2s/(1+s²))
    (RationalRotationGroup.v:96 `cayley_on_circle`) at half-angle s = λ/2:
        (1−s²)/(1+s²) = (4−λ²)/(4+λ²) = Re_cayley λ,    2s/(1+s²) = 4λ/(4+λ²) = cayley_im λ   (s=λ/2).
    So the spectral arm (Fourier transfer eigenvalue / lattice mass gap) and the geometry arm (rational
    rotations SO(2,ℚ)) of the Cayley vein are ONE map: the lattice mass eigenvalue IS the cosine of a
    rational rotation, and the spectral Cayley point lies in — and composes/doubles inside — SO(2,ℚ).
    Concretely the λ=4 lattice mass point is the rotation (−3/5, 4/5), which doubles (via the
    two-square identity) to (−7/25, −24/25) — the 7-24-25 rotation (cf. double_345).

    WHAT IS NEW / HONEST SCALE.
    The Cayley transform (1846), the tangent-half-angle parametrization of SO(2,ℚ), and the two-square
    (Brahmagupta) closure are all classical. NEW (synthesis+observation, machine-checked): the
    cross-cluster UNIFICATION — that the SAME Cayley map is the spectral transfer eigenvalue (lattice/
    analysis) AND a rational rotation (geometry), so the two arms of vein F are one map (t=λ/2), and the
    lattice masses are rational rotations. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : спектральная Кэли-точка (Re_cayley λ, cayley_im λ)=((4−λ²)/(4+λ²),4λ/(4+λ²)); геометрическая
                 2D Кэли-карта SO(2,ℚ) ((1−s²)/(1+s²),2s/(1+s²)); связь s=λ/2; инстанс λ=4 (масс-точка решётки).
      Roles    : спектральная роль = собств. значение трансфера/масс-щель; геометрическая роль = элемент
                 группы рациональных вращений SO(2,ℚ); единый объект = рациональная точка окружности.
      Rules    : Re²+Im²=1 (на окружности); rcompose замкнут (rotation_compose_closed) ⟹ спектральная точка
                 ∈ SO(2,ℚ); λ=2s ⟹ спектральная точка = геом. карта при s (tangent-half-angle); λ=4 ⟹
                 (−3/5,4/5) = вращение, удваивается в (−7/25,−24/25).
      ДИАГНОСТИКА (P4): спектральная рука (Fourier/масс) и геометрическая рука (рациональные вращения) вены F —
      ОДНА Кэли-карта (t=λ/2); масс-щель решётки = косинус рационального вращения; обе руки сшиты. ЧЕСТНО:
      tangent-half-angle классична; новое — машинная унификация двух рук вены F одной картой. Уровень: `синтез+наблюдение`.

    STATUS: 6 Qed, 0 Admitted, 0 axioms  (imports lattice.MassFromSpectrum + stdlib.RationalRotationGroup)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia.
From ToS Require Import lattice.MassFromSpectrum.        (* Re_cayley (spectral transfer eigenvalue), Re_cayley_4 *)
From ToS Require Import stdlib.RationalRotationGroup.    (* rcompose, rotation_compose_closed, cayley_on_circle *)

Open Scope Q_scope.

(** The spectral Cayley imaginary part (= cayley_im, physics/AlphaBareLattice.v:25). *)
Definition cayley_im (lambda : Q) : Q := (4 * lambda) / (4 + lambda * lambda).

(* ===================================================================== *)
(*  1. The spectral Cayley point is a rational point of the UNIT CIRCLE   *)
(* ===================================================================== *)

(** ★ Re_cayley² + cayley_im² = 1: the spectral transfer eigenvalue point lies on the unit circle —
    a rational circle point, i.e. an element of SO(2,ℚ). *)
Lemma spectral_point_on_circle : forall lambda,
  ~ (4 + lambda * lambda == 0) ->
  Re_cayley lambda * Re_cayley lambda + cayley_im lambda * cayley_im lambda == 1.
Proof.
  intros lambda Hnz. unfold Re_cayley, cayley_im. field. exact Hnz.
Qed.

(* ===================================================================== *)
(*  2. The spectral point lies in SO(2,ℚ): it composes as a rotation      *)
(* ===================================================================== *)

(** ★ The spectral Cayley point composes (complex multiplication / rcompose) with ANY rational rotation
    to another rational rotation — via the two-square identity (rotation_compose_closed). So the spectral
    transfer eigenvalues are genuine elements of the rational rotation group SO(2,ℚ). *)
Theorem spectral_composes_in_SO2Q : forall lambda x y : Q,
  ~ (4 + lambda * lambda == 0) ->
  x * x + y * y == 1 ->
  (Re_cayley lambda * x - cayley_im lambda * y) * (Re_cayley lambda * x - cayley_im lambda * y)
  + (Re_cayley lambda * y + cayley_im lambda * x) * (Re_cayley lambda * y + cayley_im lambda * x) == 1.
Proof.
  intros lambda x y Hnz Hxy.
  apply rotation_compose_closed.
  - apply spectral_point_on_circle. exact Hnz.
  - exact Hxy.
Qed.

(* ===================================================================== *)
(*  3. Concrete: the λ=4 lattice mass point IS the rational rotation       *)
(*     (−3/5, 4/5) = the geometry Cayley chart at t=2                       *)
(* ===================================================================== *)

Lemma im_4 : cayley_im 4 == 4 # 5.
Proof. unfold cayley_im. vm_compute. reflexivity. Qed.

(** ★★ The λ=4 lattice mass eigenvalue point is the rational rotation (−3/5, 4/5), equal to the geometry
    Cayley / tangent-half-angle chart at t=2, and it lies on the unit circle (a rotation). *)
Theorem mass_4_is_rotation :
  Re_cayley 4 == -(3 # 5)                          (* lattice mass eigenvalue, MassFromSpectrum.v:54 *)
  /\ cayley_im 4 == 4 # 5
  /\ Re_cayley 4 == (1 - 2 * 2) / (1 + 2 * 2)       (* = geometry Cayley chart ((1−s²)/(1+s²)) at s=2 *)
  /\ cayley_im 4 == (2 * 2) / (1 + 2 * 2)           (* = geometry Cayley chart (2s/(1+s²)) at s=2 *)
  /\ Re_cayley 4 * Re_cayley 4 + cayley_im 4 * cayley_im 4 == 1.   (* on the unit circle: a rotation *)
Proof.
  split. exact Re_cayley_4.
  split. exact im_4.
  split. { rewrite Re_cayley_4. vm_compute. reflexivity. }
  split. { rewrite im_4. vm_compute. reflexivity. }
  rewrite Re_cayley_4, im_4. vm_compute. reflexivity.
Qed.

(** Doubling the λ=4 rotation (via rcompose) stays in SO(2,ℚ): (−3/5,4/5)∘(−3/5,4/5) = (−7/25,−24/25)
    — the double-angle, cf. double_345 (the 3-4-5 ↦ 7-24-25 doubling). *)
Lemma mass_4_doubles :
  fst (rcompose (Re_cayley 4, cayley_im 4) (Re_cayley 4, cayley_im 4)) == -(7 # 25)
  /\ snd (rcompose (Re_cayley 4, cayley_im 4) (Re_cayley 4, cayley_im 4)) == -(24 # 25).
Proof.
  unfold rcompose. simpl. rewrite Re_cayley_4, im_4. split; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The geometry arm of the Cayley vein, joined to the spectral arm — ONE map:
      (circle)   the spectral Cayley point (Re_cayley λ, cayley_im λ) is on the unit circle;
      (group)    it composes with rational rotations to rational rotations — it lies in SO(2,ℚ);
      (chart)    the λ=4 lattice mass point = the geometry Cayley chart at t=2 = the rotation (−3/5,4/5);
      (doubling) it doubles to (−7/25,−24/25) inside SO(2,ℚ) (the 7-24-25 rotation).
    So the lattice mass eigenvalue is the cosine of a rational rotation: spectral arm = geometry arm. *)
Theorem cayley_geometry_spectral_bridge :
  (forall lambda, ~ (4 + lambda * lambda == 0) ->
     Re_cayley lambda * Re_cayley lambda + cayley_im lambda * cayley_im lambda == 1)
  /\ (forall lambda x y, ~ (4 + lambda * lambda == 0) -> x * x + y * y == 1 ->
        (Re_cayley lambda * x - cayley_im lambda * y) * (Re_cayley lambda * x - cayley_im lambda * y)
        + (Re_cayley lambda * y + cayley_im lambda * x) * (Re_cayley lambda * y + cayley_im lambda * x) == 1)
  /\ (Re_cayley 4 == (1 - 2 * 2) / (1 + 2 * 2))
  /\ (Re_cayley 4 * Re_cayley 4 + cayley_im 4 * cayley_im 4 == 1).
Proof.
  split. exact spectral_point_on_circle.
  split. exact spectral_composes_in_SO2Q.
  split. { rewrite Re_cayley_4. vm_compute. reflexivity. }
  rewrite Re_cayley_4, im_4. vm_compute. reflexivity.
Qed.
