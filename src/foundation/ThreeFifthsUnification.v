(** * ThreeFifthsUnification.v — ONE rational number 3/5 is Cayley(1), the Born-rule entry U₀₀, AND the
       3-4-5 Schrödinger rotation cosine; and ONE Pythagorean identity (3/5)²+(4/5)²=1 is simultaneously
       Cayley-on-the-unit-circle, the Born p=2 normalization, and the Schrödinger norm-preservation.

    THE OBSERVATION (from the Cayley-hub audit).
    The number 3/5 was proved THREE times independently, in three clusters, with no shared statement:
      - analysis : `cayley_at_1 : cayley_eigenvalue 1 == 3#5`  (FourierCayleyConnection.v:54) — Cayley(1);
      - physics  : `U00 := 3#5`, `born_rule_p2 : U00²+U01²==1` (BornRuleFromUnitarity.v:32,39) — the
                   chain-2 Cayley unitary [[3/5,−4/5],[4/5,3/5]] at θ=1, where p=2 is the UNIQUE exponent;
      - process  : the 3-4-5 rotation c=3/5, s=4/5, c²+s²=1 IS the norm-preserving Schrödinger step
                   (ProcessSchrodingerEvolution.v:15-17) — cited, not imported (heavy process chain).
    This file states, once, that these are the SAME number and the SAME Pythagorean identity, read in
    three physical roles.

    WHAT IS NEW / HONEST SCALE.
    Trivial algebra ((3,4,5) is the smallest Pythagorean triple). The value is purely the OBSERVATION
    that one number / one identity carries the Born rule, the Cayley transfer eigenvalue, and the
    Schrödinger isometry across three clusters — previously scattered. Level: observation (the lowest
    novelty tier — a unification of identical facts, recorded for the H63 / 6th-vein thread).

    ============ E/R/R разбор ============
      Elements : число 3/5 (= U₀₀ Борна = cayley_eigenvalue 1 = косинус 3-4-5 поворота); пифагоров партнёр
                 4/5; тождество (3/5)²+(4/5)²=1.
      Roles    : 3/5 в роли Born-амплитуды U₀₀ (вероятность=|U|²); в роли Cayley-образа Cayley(1)
                 (собств. значение трансфера); в роли косинуса 3-4-5 Шрёдингер-поворота (изометрия/
                 сохранение нормы); 4/5 = пифагоров партнёр, замыкающий окружность.
      Rules    : U₀₀ ≡ cayley_eigenvalue 1 (одно число); (3/5)²+(4/5)²=1 = Cayley-на-окружности =
                 Born p=2 нормировка = Шрёдингер-изометрия (одно тождество, три роли).
      ДИАГНОСТИКА (P4): одно рациональное число и одно пифагорово тождество несут три физические роли
      (Борн/Кэли/Шрёдингер) в трёх кластерах (physics/analysis/process); ранее доказано трижды независимо,
      теперь сшито. ЧЕСТНО: тривиальная алгебра 3-4-5; новое — наблюдение тождественности ролей.
      Уровень: `наблюдение`.

    STATUS: 5 Qed, 0 Admitted, 0 axioms  (imports analysis.FourierCayleyConnection + physics.BornRuleFromUnitarity)
    Author: Horsocrates (experiment) | Date: June 2026
*)

From Stdlib Require Import QArith Qabs Lqa ZArith Lia.
From ToS Require Import analysis.FourierCayleyConnection.   (* cayley_eigenvalue, cayley_at_1 *)
From ToS Require Import physics.BornRuleFromUnitarity.      (* U00, U01, born_rule_p2, born_rule_unique_exponent *)

Open Scope Q_scope.

(** ★ The Born-rule matrix entry U₀₀ IS the Cayley value Cayley(1) — one number, two clusters. *)
Theorem born_entry_is_cayley_at_1 : U00 == cayley_eigenvalue 1.
Proof. rewrite cayley_at_1. unfold U00. reflexivity. Qed.

(** The 3-4-5 Schrödinger rotation cosine (c=3/5, ProcessSchrodingerEvolution.v:16) is the same Cayley(1). *)
Theorem schrodinger_cosine_is_cayley_at_1 : (3 # 5) == cayley_eigenvalue 1.
Proof. rewrite cayley_at_1. reflexivity. Qed.

(** ★★ ONE Pythagorean identity (3/5)²+(4/5)²=1, read three ways — Cayley-on-circle, Born p=2
    normalization, Schrödinger isometry — and all three share the number U₀₀ = Cayley(1). *)
Theorem one_identity_three_readings :
  (* Cayley-on-circle: Cayley(1)² + (4/5)² = 1  (the 3-4-5 rational circle point) *)
  cayley_eigenvalue 1 * cayley_eigenvalue 1 + (4 # 5) * (4 # 5) == 1
  (* Born p=2 normalization: U₀₀² + U₀₁² = 1 *)
  /\ U00 * U00 + U01 * U01 == 1
  (* Schrödinger isometry: the 3-4-5 rotation c=3/5, s=4/5 preserves norm, c²+s²=1 *)
  /\ (3 # 5) * (3 # 5) + (4 # 5) * (4 # 5) == 1
  (* ...and the number is shared: U₀₀ = Cayley(1) *)
  /\ U00 == cayley_eigenvalue 1.
Proof.
  split. { vm_compute. reflexivity. }
  split. { exact born_rule_p2. }
  split. { vm_compute. reflexivity. }
  exact born_entry_is_cayley_at_1.
Qed.

(** The Born p=2 normalization IS the integer Pythagorean triple 3²+4²=5². *)
Theorem born_p2_is_pythagorean :
  U00 * U00 + U01 * U01 == 1 /\ (3 * 3 + 4 * 4 = 5 * 5)%Z.
Proof. split; [ exact born_rule_p2 | reflexivity ]. Qed.

(* ===================================================================== *)
(*  CAPSTONE                                                               *)
(* ===================================================================== *)

(** ONE number 3/5 and ONE identity (3/5)²+(4/5)²=1, across three clusters:
      (number)     U₀₀ (Born, physics) = cayley_eigenvalue 1 (Cayley, analysis) = 3/5 (Schrödinger cos);
      (identity)   Cayley-on-circle = Born p=2 normalization = Schrödinger isometry = 3²+4²=5²;
      (uniqueness) p=2 is the unique Born exponent — because (3,4,5) is Pythagorean.
    A unification of three independently-proved facts (observation level), recorded for H63 / the 6th
    (Cayley) vein. *)
Theorem three_fifths_unification :
  U00 == cayley_eigenvalue 1
  /\ (3 # 5) == cayley_eigenvalue 1
  /\ (cayley_eigenvalue 1 * cayley_eigenvalue 1 + (4 # 5) * (4 # 5) == 1)
  /\ (U00 * U00 + U01 * U01 == 1)
  /\ (3 * 3 + 4 * 4 = 5 * 5)%Z
  /\ (U00 * U00 + U01 * U01 == 1 /\ ~ (U00 + U01 == 1)).   (* Born p=2 holds, p=1 fails *)
Proof.
  split. exact born_entry_is_cayley_at_1.
  split. exact schrodinger_cosine_is_cayley_at_1.
  split. { vm_compute. reflexivity. }
  split. exact born_rule_p2.
  split. reflexivity.
  split. exact born_rule_p2.
  exact p1_not_one.
Qed.
