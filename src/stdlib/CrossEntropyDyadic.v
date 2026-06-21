(** * CrossEntropyDyadic.v — кросс-энтропия / KL над ℚ как ПРОЦЕСС: граница Element ↔ role-limit
      (закрывает горизонт KL/CE из отчёта docs/AI-ProcessMath-vs-Infinity.md, блок B).

    Функция потерь ИИ — next-token NLL = −log p(correct) (каталог AI #14); кросс-энтропия;
    KL в VAE/диффузии (#9,12,13) — в стандартной записи живёт в расширенной прямой [0,+∞]:
    log:(0,∞)→ℝ, log0=−∞, KL может быть +∞ (завершённое значение).  ToS даёт ДРУГУЮ запись:
    информация = −log p — над ДИАДИЧЕСКИМИ вероятностями (p=2^{−k}) схлопывается в ЦЕЛОЕ k бит
    (Element, точная ℚ); над НЕ-диадическими (трит) — иррациональна (role-limit); а KL=+∞ —
    НЕОГРАНИЧЕННЫЙ процесс (нет рационального потолка), не завершённое значение.

    ============ E/R/R разбор ============
      Rules (L5): информация = −log₂ p; log₂ рационален ⟺ p диадично (2^a=p^{−b} разрешимо) —
        DyadicBits; расходимость при p→0 = неограниченный процесс.
      Roles (L4): энтропия H, кросс-энтропия CE, дивергенция KL — роль-величины (рациональные
        комбинации суражизалов k_i).  Диадическое распределение → точная ℚ (Element);
        не-диадическое → role-limit (иррационально).
      Elements (L1+P4): суражизалы k (целые биты); диад. вероятности 2^{−k}; конечные ℚ-суммы —
        каждая стадия точна и терминирует.
    ДИАГНОСТИКА (P4): завершённое KL∈[0,+∞] реифицирует role-limit.  Над ℚ: KL диадических ТОЧНА
      (Element; KL(p‖p)=0; примеры = точные ℚ); не-диадических — иррациональна (role-limit);
      KL=+∞ — неограниченный процесс (у суражизала нет рационального потолка), не число.
      Могло ли быть иначе?  Нет: бит-мера рациональна ⟺ диадично (DyadicBits).
    ЧЕСТНАЯ СТЕНА: общая (не-диадическая) кросс-энтропия как АКТУАЛЬНЫЙ Cauchy-процесс — это ln_proc
      (Log2Process.v), сюда НЕ импортируется (тяжёлая цепь); здесь — самодостаточный диадический
      Element + role-limit-граница в стиле DyadicBits.

    STATUS: 12 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qpower List Lia.
From ToS Require Import stdlib.DyadicBits.
Import ListNotations.
Open Scope Q_scope.

(* ================================================================= *)
(*  Диадическая вероятность p = 2^{−k} и суражизал −log₂ p = k         *)
(* ================================================================= *)

(** Вероятность диадического события с суражизалом k бит: p = (1/2)^k. *)
Definition pdyad (k : nat) : Q := Qpower (1 # 2) (Z.of_nat k).

Lemma pdyad_zero : pdyad 0 == 1.
Proof. vm_compute; reflexivity. Qed.

Lemma pdyad_half : pdyad 1 == 1 # 2.
Proof. vm_compute; reflexivity. Qed.

(** Суражизал (информация) диадической p = 2^{−k} есть ЦЕЛОЕ k бит — Element-сторона
    (−log₂(2^{−k}) = k). *)
Definition nll (k : nat) : Q := inject_Z (Z.of_nat k).

Lemma nll_dyadic_integer : nll 3 == 3.
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  Энтропия / кросс-энтропия / KL диадических распределений (Element) *)
(*  Распределение = список суражизалов ks  (p_i = 2^{−k_i}).           *)
(* ================================================================= *)

(** Энтропия H(p) = Σ p_i·(−log p_i) = Σ 2^{−k_i}·k_i — конечная точная ℚ. *)
Fixpoint H_dyad (ks : list nat) : Q :=
  match ks with
  | [] => 0
  | k :: r => pdyad k * inject_Z (Z.of_nat k) + H_dyad r
  end.

(** Кросс-энтропия H(p;q) = Σ p_i·(−log q_i) = Σ 2^{−pᵢ}·qᵢ. *)
Fixpoint CE_dyad (ps qs : list nat) : Q :=
  match ps, qs with
  | p :: pr, q :: qr => pdyad p * inject_Z (Z.of_nat q) + CE_dyad pr qr
  | _, _ => 0
  end.

(** KL(p‖q) = H(p;q) − H(p). *)
Definition KL_dyad (ps qs : list nat) : Q := CE_dyad ps qs - H_dyad ps.

(* --- Element: точные рациональные значения (терминируют) --- *)

(** Честная монета: H(½,½) = 1 бит. *)
Lemma H_fair_coin : H_dyad [1; 1]%nat == 1.
Proof. vm_compute; reflexivity. Qed.

(** H(½,¼,¼) = 3/2 бита — ТОЧНАЯ ℚ (Element). *)
Lemma H_half_quarter_quarter : H_dyad [1; 2; 2]%nat == 3 # 2.
Proof. vm_compute; reflexivity. Qed.

(** Кросс-энтропия диадических — точная ℚ: true=(½,½), model=(½,¼) ⟹ CE = ½·1+½·2 = 3/2. *)
Lemma CE_dyadic_exact : CE_dyad [1; 1]%nat [1; 2]%nat == 3 # 2.
Proof. vm_compute; reflexivity. Qed.

(** Гиббс в точке: KL(p‖p) = 0. *)
Lemma KL_self_zero : KL_dyad [1; 1]%nat [1; 1]%nat == 0.
Proof. vm_compute; reflexivity. Qed.

(** KL диадических — точная ℚ и положительна: KL((½,½)‖(½,¼)) = 3/2 − 1 = 1/2. *)
Lemma KL_dyadic_exact : KL_dyad [1; 1]%nat [1; 2]%nat == 1 # 2.
Proof. vm_compute; reflexivity. Qed.

(* ================================================================= *)
(*  Граница role-limit: расходимость (процесс) и иррациональность      *)
(* ================================================================= *)

(** −log q → +∞ при q→0 есть НЕОГРАНИЧЕННЫЙ ПРОЦЕСС (role-limit), не завершённое значение:
    суражизал диадического токена превышает любой целый предел. *)
Lemma surprisal_unbounded : forall B : nat, exists k : nat, (B < k)%nat.
Proof. intro B. exists (S B). lia. Qed.

(** То же над ℚ: потеря nll(k) превосходит любую целую границу — у дивергенции нет рационального потолка. *)
Lemma nll_exceeds_integer_bounds :
  forall B : nat, exists k : nat, inject_Z (Z.of_nat B) < nll k.
Proof.
  intro B. exists (S B). unfold nll, Qlt, inject_Z; simpl; lia.
Qed.

(** Не-диадическое распределение (равномерный трит) имеет энтропию log₂3 — role-limit (иррационально):
    2^a = 3^b неразрешимо.  (DyadicBits, переинтерпретировано на уровень распределения.) *)
Theorem trit_entropy_role_limit :
  ~ (exists a b : nat, (1 <= b)%nat /\ Nat.pow 2 a = Nat.pow 3 b).
Proof. exact log2_3_irrational. Qed.

(* ================================================================= *)
(*  CAPSTONE                                                          *)
(* ================================================================= *)

(** ★★★ КРОСС-ЭНТРОПИЯ / KL НАД ℚ — ГРАНИЦА Element ↔ role-limit:
      (Element)    диадические H/CE/KL — ТОЧНЫЕ рациональные (терминируют): KL(p‖p)=0; KL = ℚ;
      (процесс)    KL=+∞ / −log q→∞ — НЕОГРАНИЧЕННЫЙ процесс, не завершённое значение;
      (role-limit) не-диадическое (трит) — иррациональная информация (log₂3).
    Стандартная запись KL∈[0,+∞] реифицирует role-limit; над ℚ дивергенция точна для диадических
    (Element) и есть процесс/role-limit иначе. *)
Theorem cross_entropy_boundary :
  (KL_dyad [1; 1]%nat [1; 1]%nat == 0)                              (* Element: KL(p‖p)=0 точно        *)
  /\ (KL_dyad [1; 1]%nat [1; 2]%nat == 1 # 2)                       (* Element: KL диад. = точная ℚ     *)
  /\ (forall B : nat, exists k : nat, (B < k)%nat)                  (* процесс: −log q→∞ неограничен    *)
  /\ ~ (exists a b : nat, (1 <= b)%nat /\ Nat.pow 2 a = Nat.pow 3 b). (* role-limit: трит = log₂3 иррац. *)
Proof.
  split; [ exact KL_self_zero
         | split; [ exact KL_dyadic_exact
                  | split; [ exact surprisal_unbounded
                           | exact trit_entropy_role_limit ] ] ].
Qed.

Print Assumptions cross_entropy_boundary.

(* ========================================================================= *)
(*  SUMMARY                                                                    *)
(*  12 Qed, 0 Admitted, 0 axioms.                                            *)
(*  Кросс-энтропия/KL над ℚ: диадические H/CE/KL = ТОЧНЫЕ рациональные        *)
(*  (Element; KL(p‖p)=0, KL=1/2); KL=+∞ / −log q→∞ = НЕОГРАНИЧЕННЫЙ процесс    *)
(*  (surprisal_unbounded), не завершённое значение; не-диадическое (трит) =    *)
(*  log₂3 = role-limit (trit_entropy_role_limit ⟸ DyadicBits). Капстоун       *)
(*  cross_entropy_boundary. Закрывает горизонт B отчёта AI-ProcessMath.        *)
(* ========================================================================= *)
