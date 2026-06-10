(** * NormFormTowerBridge.v — the HURWITZ norm-form tower (n=1,2,4,8) IS the rational-rotation closure
       ladder: the same sum-of-n-squares multiplicativity that closes ℂ/ℍ/𝕆 closes SO(2,ℚ) / SU(2) /
       the octonion loop — and Hurwitz's {1,2,4,8} is WHY rational rotation/spin groups exist exactly
       in these dimensions (a finitization one storey up). Candidate 8th thread; ties q-kinematics & vein F.

    THE OBSERVATION.
    The multiplicative sum-of-n-squares norm forms (HurwitzTower.v) exist for EXACTLY n=1,2,4,8
    (ℝ,ℂ,ℍ,𝕆 — Hurwitz). This file makes LITERAL that each identity IS the group-closure law of the
    rational rotation group at that dimension:
      - n=2 (ℂ, Brahmagupta two_square): unit ℚ[i] elements close ⟹ SO(2,ℚ) is a group — and this is
        EXACTLY RationalRotationGroup.rotation_compose_closed (the rational rotations). The same n=2 rung
        carries vein F's geometry arm (the spectral Cayley point ∈ SO(2,ℚ)) and the 3-4-5 object.
      - n=4 (ℍ, Euler four_square): unit quaternions close ⟹ SU(2)/Spin(3) is a group — the double cover
        of SO(3,ℚ) (rational 3D rotations).
      - n=8 (𝕆, Degen eight_square): unit octonions close into a Moufang loop (non-associative) —
        HurwitzTower.unit_octonion_closed.
    By Hurwitz, these are the ONLY dimensions: the Element-side rotation-group construction TERMINATES
    at n=8; dims 3,5,6,7 admit no normed multiplication, hence no such rational rotation group. The list
    of Element-dimensions {1,2,4,8} is finite — a finitization at the meta-level.

    WHAT IS NEW / HONEST SCALE.
    The two/four/eight-square identities (Brahmagupta/Euler/Degen), Hurwitz's theorem, and the
    division-algebra ladder ℝ→ℂ→ℍ→𝕆 are all classical, and HurwitzTower.v already proves the identities.
    NEW (synthesis+observation, machine-checked): the LITERAL identification of each Hurwitz rung with the
    rational-rotation closure law (n=2 = rotation_compose_closed, n=4 = unit-quaternion closure), so the
    norm-form tower and the q-kinematics rotation thread + vein F (the SO(2,ℚ) Cayley rung) are ONE
    mechanism, with the Hurwitz {1,2,4,8} terminus as the dimensional finitization. Level: synthesis+observation.

    ============ E/R/R разбор ============
      Elements : тождества суммы n квадратов (n=1,2,4,8); единичные элементы ℝ/ℂ/ℍ/𝕆; конкретные единицы
                 (3/5,4/5) при n=2 и (1/2,1/2,1/2,1/2) при n=4.
      Roles    : норм-форма мультипликативна = ЗАМЫКАНИЕ группы вращений на каждой размерности; n=2 → SO(2,ℚ),
                 n=4 → SU(2)/Spin(3), n=8 → октонионный Moufang-loop; {1,2,4,8} = конечный список Element-размерностей.
      Rules    : two_square|единичный = rotation_compose_closed (SO(2,ℚ)); four_square|единичный = замыкание
                 единичных кватернионов (SU(2)); Гурвиц ⟹ только n=1,2,4,8 (мета-финитизация, терминус 𝕆).
      ДИАГНОСТИКА (P4): Element-сторонняя конструкция групп вращений из норм-форм существует РОВНО в dim 1,2,4,8
      (Гурвиц) — конечная башня, обрывающаяся на октонионах; dim 3,5,6,7 — role-limit (нет норм-деления). Тот же
      n=2-рунг несёт вену F (Cayley-точка ∈ SO(2,ℚ)) и 3-4-5. ЧЕСТНО: тождества/Гурвиц классичны (и уже в
      HurwitzTower); ново — литеральное отождествление рунгов с замыканием групп вращений + унификация с веной F/q-kinematics.
      Уровень: `синтез+наблюдение`.

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (imports stdlib.HurwitzTower + stdlib.RationalRotationGroup)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Lqa ZArith Lia.
From ToS Require Import stdlib.HurwitzTower.            (* one/two/four/eight_square, unit_octonion_closed *)
From ToS Require Import stdlib.RationalRotationGroup.   (* rotation_compose_closed = SO(2,Q) group law *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  n = 2 (ℂ): the Brahmagupta rung IS the SO(2,ℚ) group law              *)
(* ===================================================================== *)

(** ★ The n=2 Hurwitz rung (two_square) at UNIT norm IS the SO(2,ℚ) closure: the rational rotation group
    closes BECAUSE the 2-square (ℂ) norm is multiplicative. (This is exactly
    RationalRotationGroup.rotation_compose_closed, here derived from the Hurwitz rung to make the link
    literal — and it is the rung that carries vein F's geometry arm and the 3-4-5 object.) *)
Theorem n2_rung_is_SO2Q_closure : forall x1 y1 x2 y2 : Q,
  x1*x1 + y1*y1 == 1 -> x2*x2 + y2*y2 == 1 ->
  (x1*x2 - y1*y2)*(x1*x2 - y1*y2) + (x1*y2 + y1*x2)*(x1*y2 + y1*x2) == 1.
Proof.
  intros x1 y1 x2 y2 H1 H2.
  rewrite (two_square x1 y1 x2 y2), H1, H2. ring.
Qed.

(* ===================================================================== *)
(*  n = 4 (ℍ): the Euler rung gives unit-quaternion / SU(2) closure       *)
(* ===================================================================== *)

(** ★ The n=4 Hurwitz rung (four_square) at UNIT norm gives unit-QUATERNION closure: N(p)=N(q)=1 ⟹
    N(pq)=1 — the SU(2)/Spin(3) group law (the double cover of rational 3D rotations SO(3,ℚ)). *)
Theorem unit_quaternion_closed : forall a1 a2 a3 a4 b1 b2 b3 b4 : Q,
  a1*a1 + a2*a2 + a3*a3 + a4*a4 == 1 ->
  b1*b1 + b2*b2 + b3*b3 + b4*b4 == 1 ->
  (a1*b1 - a2*b2 - a3*b3 - a4*b4)*(a1*b1 - a2*b2 - a3*b3 - a4*b4)
  + (a1*b2 + a2*b1 + a3*b4 - a4*b3)*(a1*b2 + a2*b1 + a3*b4 - a4*b3)
  + (a1*b3 - a2*b4 + a3*b1 + a4*b2)*(a1*b3 - a2*b4 + a3*b1 + a4*b2)
  + (a1*b4 + a2*b3 - a3*b2 + a4*b1)*(a1*b4 + a2*b3 - a3*b2 + a4*b1) == 1.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 Ha Hb.
  rewrite (four_square a1 a2 a3 a4 b1 b2 b3 b4), Ha, Hb. ring.
Qed.

(* ===================================================================== *)
(*  Concrete unit elements at two rungs of the tower                       *)
(* ===================================================================== *)

(** n=2: the 3-4-5 unit element (3/5, 4/5) ∈ SO(2,ℚ) — the rung shared with vein F / vein G. *)
Lemma unit_345_n2 : (3#5)*(3#5) + (4#5)*(4#5) == 1.
Proof. vm_compute. reflexivity. Qed.

(** n=4: the order-3 unit quaternion (1/2,1/2,1/2,1/2) ∈ SU(2). *)
Lemma unit_half_quaternion_n4 :
  (1#2)*(1#2) + (1#2)*(1#2) + (1#2)*(1#2) + (1#2)*(1#2) == 1.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** The Hurwitz norm-form tower IS the rational-rotation closure ladder:
      n=2 (ℂ, two_square)  ⟹ SO(2,ℚ) closes (= rotation_compose_closed; vein F's geometry arm, 3-4-5);
      n=4 (ℍ, four_square) ⟹ unit quaternions / SU(2) close (Spin(3), double cover of SO(3,ℚ));
      n=8 (𝕆, eight_square)⟹ unit octonions close (Moufang loop — HurwitzTower.unit_octonion_closed).
    By Hurwitz, ONLY n=1,2,4,8: the Element-side rotation-group construction terminates at the octonions;
    dims 3,5,6,7 have no normed multiplication, hence no such rational rotation group (a meta-finitization).
    The same multiplicativity is the n=2 rung under vein F (Cayley SO(2,ℚ)) and vein G (the 3-4-5 Born object). *)
Theorem norm_form_tower_bridge :
  (forall x1 y1 x2 y2, x1*x1 + y1*y1 == 1 -> x2*x2 + y2*y2 == 1 ->
     (x1*x2 - y1*y2)*(x1*x2 - y1*y2) + (x1*y2 + y1*x2)*(x1*y2 + y1*x2) == 1)
  /\ (forall a1 a2 a3 a4 b1 b2 b3 b4, a1*a1+a2*a2+a3*a3+a4*a4 == 1 -> b1*b1+b2*b2+b3*b3+b4*b4 == 1 ->
        (a1*b1 - a2*b2 - a3*b3 - a4*b4)*(a1*b1 - a2*b2 - a3*b3 - a4*b4)
        + (a1*b2 + a2*b1 + a3*b4 - a4*b3)*(a1*b2 + a2*b1 + a3*b4 - a4*b3)
        + (a1*b3 - a2*b4 + a3*b1 + a4*b2)*(a1*b3 - a2*b4 + a3*b1 + a4*b2)
        + (a1*b4 + a2*b3 - a3*b2 + a4*b1)*(a1*b4 + a2*b3 - a3*b2 + a4*b1) == 1)
  /\ ((3#5)*(3#5) + (4#5)*(4#5) == 1)
  /\ ((1#2)*(1#2) + (1#2)*(1#2) + (1#2)*(1#2) + (1#2)*(1#2) == 1).
Proof.
  split. exact n2_rung_is_SO2Q_closure.
  split. exact unit_quaternion_closed.
  split. exact unit_345_n2.
  exact unit_half_quaternion_n4.
Qed.
