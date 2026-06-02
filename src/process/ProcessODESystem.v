(** * ProcessODESystem.v — Systems of ODEs and higher order as a VECTOR process
      over ℚ; reduction of y''=g to first order; harmonic oscillator (Part VIII, batch A)

    Elements: rational state pairs (y_n, v_n) ∈ ℚ×ℚ at each stage
    Roles:    (y, v) = role-state (position, velocity); v = y' = the role that turns a
              2nd-order equation into a 1st-order system; E = y²+v² = role-invariant
    Rules:    vector Euler step (y,v) ↦ (y+h·f₁(t,y,v), v+h·f₂(t,y,v)); order reduction
              y''=g(t,y,y') ⟺ the system y'=v, v'=g(t,y,v); oscillator y''=−y ⟺ (y'=v, v'=−y)

    A system / higher-order equation is a joint VECTOR process on ℚⁿ. Reducing order is the
    introduction of velocity as a ROLE (an extension of the state space), not a trick. The
    oscillator y''=−y: its trajectory (cos, sin) is the role-limit of the vector Euler process;
    sin/cos as completed transcendentals are NOT Elements (like e in batch C), but role-limits.
    (This is ODE-systems-as-solution-process; dynamical systems proper are Part IX.)

    ============ E/R/R разбор ============
      Rules (L5): (y,v)↦(y+h·f₁, v+h·f₂); y''=g ⟺ (y'=v, v'=g); осциллятор y''=−y ⟺ (y'=v,v'=−y);
                  почти-инвариант E=y²+v².
      Roles (L4): (y,v) = роль-состояние; v=y' = роль-расширение (понижение порядка);
                  E = роль-инвариант (дрейфует на сетке); h = роль-разрешение.
      Elements  : пара рациональных (y_n,v_n)∈ℚ×ℚ на каждой стадии (L1+P4).
    ДИАГНОСТИКА: система/высший порядок = совместный векторный процесс на ℚⁿ; редукция порядка =
    введение скорости как РОЛИ; (cos,sin) — роль-предел, не завершённый объект.

    HONEST FRONTIER: proved over ℚ — the vector Euler step laws, the order-reduction position
    law (y'=v), and concrete oscillator stages with the energy drift of explicit Euler. The
    completed (cos, sin) trajectory and exact energy conservation are role-limits / the frontier.

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith ZArith Lia.

Open Scope Q_scope.

Definition tg (h : Q) (n : nat) : Q := inject_Z (Z.of_nat n) * h.   (* grid time t_n = n·h *)

(* vector Euler for the system y' = f1(t,y,v), v' = f2(t,y,v); state pair (y,v) *)
Fixpoint sys_euler (f1 f2 : Q -> Q -> Q -> Q) (h y0 v0 : Q) (n : nat) : Q * Q :=
  match n with
  | O => (y0, v0)
  | S k =>
      (fst (sys_euler f1 f2 h y0 v0 k)
         + h * f1 (tg h k) (fst (sys_euler f1 f2 h y0 v0 k)) (snd (sys_euler f1 f2 h y0 v0 k)),
       snd (sys_euler f1 f2 h y0 v0 k)
         + h * f2 (tg h k) (fst (sys_euler f1 f2 h y0 v0 k)) (snd (sys_euler f1 f2 h y0 v0 k)))
  end.

(* reduction of y'' = g(t,y,y') to the first-order system y'=v, v'=g(t,y,v) *)
Definition order2_euler (g : Q -> Q -> Q -> Q) := sys_euler (fun _ _ v => v) g.

(* harmonic oscillator y'' = -y, i.e. y'=v, v'=-y *)
Definition sho_euler := order2_euler (fun _ y _ => - y).

(* ===================================================================== *)
(*  Vector Euler step laws                                                 *)
(* ===================================================================== *)

Lemma sys_euler_0 : forall f1 f2 h y0 v0,
  sys_euler f1 f2 h y0 v0 0 = (y0, v0).
Proof. intros. reflexivity. Qed.

Lemma sys_euler_fst_S : forall f1 f2 h y0 v0 k,
  fst (sys_euler f1 f2 h y0 v0 (S k))
  == fst (sys_euler f1 f2 h y0 v0 k)
     + h * f1 (tg h k) (fst (sys_euler f1 f2 h y0 v0 k)) (snd (sys_euler f1 f2 h y0 v0 k)).
Proof. intros. cbn [sys_euler fst snd]. reflexivity. Qed.

Lemma sys_euler_snd_S : forall f1 f2 h y0 v0 k,
  snd (sys_euler f1 f2 h y0 v0 (S k))
  == snd (sys_euler f1 f2 h y0 v0 k)
     + h * f2 (tg h k) (fst (sys_euler f1 f2 h y0 v0 k)) (snd (sys_euler f1 f2 h y0 v0 k)).
Proof. intros. cbn [sys_euler fst snd]. reflexivity. Qed.

(** Order reduction is correct: in the reduced system the position advances by h·velocity
    (the equation y' = v), so velocity is the genuine role of the first derivative. *)
Lemma order2_position_step : forall g h y0 v0 k,
  fst (order2_euler g h y0 v0 (S k))
  == fst (order2_euler g h y0 v0 k) + h * snd (order2_euler g h y0 v0 k).
Proof. intros. unfold order2_euler. cbn [sys_euler fst snd]. reflexivity. Qed.

(* ===================================================================== *)
(*  Harmonic oscillator y''=-y: concrete stages (y0=1, v0=0, h=1/10)       *)
(* ===================================================================== *)

Lemma sho_y2 : fst (sho_euler (1 # 10) 1 0 2) == 99 # 100.
Proof. vm_compute. reflexivity. Qed.

Lemma sho_v2 : snd (sho_euler (1 # 10) 1 0 2) == - (1 # 5).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  Energy E = y²+v²: exactly conserved at the role-limit, drifts on grid  *)
(* ===================================================================== *)

Lemma sho_energy2 :
  fst (sho_euler (1 # 10) 1 0 2) * fst (sho_euler (1 # 10) 1 0 2)
  + snd (sho_euler (1 # 10) 1 0 2) * snd (sho_euler (1 # 10) 1 0 2) == 10201 # 10000.
Proof. vm_compute. reflexivity. Qed.

(** Explicit Euler is not symplectic: the role-invariant energy drifts upward on the grid
    (E_2 = 1.0201 > 1 = E_0). Exact conservation is the role-limit. *)
Lemma sho_energy_drifts :
  1 < fst (sho_euler (1 # 10) 1 0 2) * fst (sho_euler (1 # 10) 1 0 2)
      + snd (sho_euler (1 # 10) 1 0 2) * snd (sho_euler (1 # 10) 1 0 2).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions order2_position_step.
Print Assumptions sho_energy2.
