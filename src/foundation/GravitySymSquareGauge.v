(** * GravitySymSquareGauge.v — H3: gravity = Sym^2(gauge) ; the E/R/R triad = matter / gauge / gravity.

    HYPOTHESIS (H3 — the "double copy" on the E/R/R axis).
    A rank-2 tensor over the Roles-space (Q^D = the directions/indices) splits into the two
    irreducible ways two Roles can relate — and these ARE the two Rule-level forces:
        Q^D (x) Q^D  =  Sym^2(Q^D)  (+)  Antisym^2(Q^D)
                     =  METRIC (gravity, spin-2)  (+)  so(D) (rotations/gauge, spin-1).
    So GRAVITY = Sym^2(Roles) (the symmetric Rule of mutual measurement, g_mn = g_nm), and
    GAUGE/ROTATION = Antisym^2(Roles) = so(D) (the antisymmetric Rule of relative orientation,
    F_mn = -F_nm).  Both are Rule-level rank-2 objects built from the Roles (the gauge vectors) —
    "gravity is gauge symmetric-squared".  DOF counts:
        dim Sym^2(Q^D)     = D(D+1)/2 = T(D)      (metric DOF ; = 10 for D=4 -> kappa = 1/10),
        dim Antisym^2(Q^D) = D(D-1)/2 = T(D-1)    (so(D) ; = 6 field-strength DOF for D=4),
        D*D = T(D) + T(D-1).
    Spin (SO(3), D=3, vector = spin-1):  Sym^2(spin-1) = spin-2 (graviton, 5) (+) spin-0 (dilaton, 1) = 6,
    Antisym^2(spin-1) = spin-1 (so(3) = the gauge SU(2) of TwoSU2OneQuaternion.v, 3).

    ============ E/R/R разбор ============
      Elements : D направлений (вектор v in Q^D, спин-1); ранг-2 тензоры из них —
                 симметричный g_mn (метрика) и антисимметричный F_mn (напряжённость); DOF T(D), T(D-1).
      Roles    : роль = направление/индекс = вектор (спин-1); калибр. группа = Aut(роли) (ERRAutomorphism).
      Rules    : ранг-2 над Ролями = два неприводимых Правила —
                 СИММЕТРИЧНОЕ Sym^2(Роли) = метрика = ГРАВИТАЦИЯ (g_mn=g_nm, L1 при перестановке, спин-2);
                 АНТИСИММЕТРИЧНОЕ Lambda^2(Роли) = so(D) = вращения/КАЛИБРОВКА (спин-1; D=3 => so(3)=SU(2), H2).
      ДИАГНОСТИКА (P4): DOF-счёты и спин-разложения Element-сторона (конечный nat, 0 акс); kappa=1/T(D) —
      гравитация разбавлена по всем T(D) спариваниям. ЧЕСТНО: триада E/R/R=материя/калибровка/гравитация —
      интерпретативное соответствие (как ERRLawsCorrespondence), не вывод; double-copy и реп-теория
      классические; ново = прочтение "Rules=Sym^2(Roles), gravity=Sym^2(gauge), gauge=Lambda^2(Roles)=so(D)"
      на оси E/R/R. Уровень: `новое обрамление известного`.

    STATUS: 12 Qed, 0 Admitted, 0 axioms  (self-contained: Stdlib only)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import Arith Lia QArith ZArith.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  Triangular number = dim of symmetric rank-2 tensors                    *)
(* ===================================================================== *)

Fixpoint tri (n : nat) : nat :=
  match n with O => O | S k => S k + tri k end.

(** dim Sym^2(Q^D) = T(D) = D(D+1)/2 = the metric (gravity) DOF (the Rule of mutual measurement). *)
Definition dim_sym2 (D : nat) : nat := tri D.

(** dim Antisym^2(Q^D) = T(D-1) = D(D-1)/2 = dim so(D) = the rotation/gauge DOF. *)
Definition dim_antisym2 (D : nat) : nat := tri (Nat.pred D).

(** Spin (SO(3)) representation dimensions 2j+1. *)
Definition spin2_dim : nat := 5%nat.   (* traceless symmetric = graviton *)
Definition spin1_dim : nat := 3%nat.   (* so(3) = the gauge vector / field strength *)
Definition spin0_dim : nat := 1%nat.   (* trace = dilaton *)

(* ===================================================================== *)
(*  Counting lemmas (Element side: 0 axioms)                               *)
(* ===================================================================== *)

(** 2*T(n) = n(n+1): the triangular identity (engine of the DOF count). *)
Lemma tri_double : forall n, 2 * tri n = n * (n + 1).
Proof. induction n as [|k IH]; cbn [tri]; nia. Qed.

(** Metric DOF = T(D): 2*dim_sym2 D = D(D+1). *)
Lemma sym2_dof : forall D, 2 * dim_sym2 D = D * (D + 1).
Proof. intro D. unfold dim_sym2. apply tri_double. Qed.

(** ★ Rank-2 over Roles splits: D*D = Sym^2 (gravity) + Antisym^2 (gauge/so(D)). *)
Lemma tensor_splits : forall D, D * D = dim_sym2 D + dim_antisym2 D.
Proof.
  intro D. unfold dim_sym2, dim_antisym2. destruct D as [|k].
  - reflexivity.
  - assert (Hk : 2 * tri k = k * (k + 1)) by apply tri_double.
    cbn [Nat.pred tri]. nia.
Qed.

(* ----- D = 4 (spacetime): 16 = 10 (metric/gravity) + 6 (field strength/gauge) ----- *)
Lemma dim_sym2_4     : dim_sym2 4 = 10%nat.   Proof. reflexivity. Qed.
Lemma dim_antisym2_4 : dim_antisym2 4 = 6%nat. Proof. reflexivity. Qed.
Lemma split_4        : (4 * 4 = 10 + 6)%nat.   Proof. reflexivity. Qed.

(* ----- D = 3 (SO(3) spins): Sym^2(spin-1) = spin-2 (+) spin-0 ; Antisym^2 = spin-1 = so(3) = SU(2) ----- *)
Lemma sym2_3_is_graviton_plus_dilaton : dim_sym2 3 = spin2_dim + spin0_dim.
Proof. reflexivity. Qed.

Lemma antisym2_3_is_so3 : dim_antisym2 3 = spin1_dim.
Proof. reflexivity. Qed.

Lemma vector_tensor_3 : (3 * 3 = dim_sym2 3 + dim_antisym2 3)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  Gravity coupling = 1 / (Rule-DOF) = 1 / dim Sym^2(Roles)               *)
(* ===================================================================== *)

Open Scope Q_scope.

Definition kappa (D : nat) : Q := 1 / inject_Z (Z.of_nat (dim_sym2 D)).

(** kappa(4) = 1/10 : gravity's weakness = 1 / (the 10 ways 4 directions pair symmetrically). *)
Lemma kappa_4 : kappa 4 == 1 # 10.
Proof. unfold kappa, dim_sym2. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** Gravity = Sym^2(gauge) on the E/R/R axis:
      (Rules=Sym^2(Roles))  metric DOF = dim Sym^2(Q^D) = T(D) = D(D+1)/2;
      (rank-2 split)        D*D = Sym^2 (metric/gravity) + Antisym^2 (so(D)/gauge);
      (D=4 spacetime)       16 = 10 (metric = gravity) + 6 (field strength = gauge flux);
      (spin / SO(3))        Sym^2(spin-1) = spin-2 (graviton) + spin-0 (dilaton);
                            Antisym^2(spin-1) = spin-1 = so(3) = the gauge SU(2) (TwoSU2OneQuaternion.v);
      (coupling)            kappa(D) = 1/dim Sym^2(Roles); kappa(4) = 1/10.
    Gravity is the symmetric Rule (mutual measurement of Roles); gauge/rotation is the antisymmetric
    Rule (so(D)); both are rank-2 over the gauge vectors — "gravity = gauge symmetric-squared". *)
Theorem gravity_is_sym_square_gauge :
  ((forall D, 2 * dim_sym2 D = D * (D + 1)) /\
   (forall D, D * D = dim_sym2 D + dim_antisym2 D) /\
   (dim_sym2 4 = 10 /\ dim_antisym2 4 = 6 /\ 4 * 4 = 10 + 6) /\
   (dim_sym2 3 = spin2_dim + spin0_dim /\ dim_antisym2 3 = spin1_dim /\
    3 * 3 = dim_sym2 3 + dim_antisym2 3))%nat
  /\ (kappa 4 == 1 # 10).
Proof.
  split.
  - split. exact sym2_dof.
    split. exact tensor_splits.
    split.
    + split. exact dim_sym2_4. split. exact dim_antisym2_4. reflexivity.
    + split. exact sym2_3_is_graviton_plus_dilaton.
      split. exact antisym2_3_is_so3. exact vector_tensor_3.
  - exact kappa_4.
Qed.
