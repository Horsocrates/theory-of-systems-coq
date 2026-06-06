(** * PvsNP_Framing.v — P vs NP as an E/R/R FRAMING (NOT a proof) — Phase 5
      ⚠ THIS FILE FRAMES, IT DOES NOT SEPARATE.  No claim about P = NP or P <> NP is made or proved.
      The polynomial COST — the actual content of P vs NP — is deliberately NOT modelled.

      The honest three-level picture (within the project's Element / role-limit theme):
        (1) cost-free ∃-verification ("exists a certificate that verifies") is merely SEMI-decidable
            (Σ1) — role-limit-flavoured, like halting (Phases 0–4).
        (2) The REAL NP bounds certificate length (polynomial), so a bounded brute-force search
            DECIDES it — NP is TOTAL/decidable (Element).  Proven: `NP_search_decides`.
        (3) P vs NP is then the EFFICIENCY refinement WITHIN the decidable (Element) realm: is the
            search a polynomially-bounded process (P), or does it escape every polynomial
            (conjecturally NP∖P)?  This file does NOT model the cost, so it CANNOT and DOES NOT
            address (3).

      What is genuinely proven here (cost-free, honest): verification is an Element check; P ⊆ NP;
      a finite covering search space decides an NP problem (the question is its cost).

      The barriers (relativization, natural proofs, algebraization) are, in E/R/R terms, level-mixing
      diagnostics — DESCRIBED below, NOT formalized as theorems.

    Honest level: new-framing-of-known; EXPLICITLY not a proof.  0 axioms.

    Elements: inputs, certificates, the verifier/decider (bool functions = bounded checks)
    Roles:    a certificate = a witness-role making verification Element-bounded; "decided" = a
              status of the input; verifier/decider = role-oracles (Status != Role)
    Rules:    verification (a bounded check) + search over the certificate space (L5 traversal)

    ============ E/R/R разбор ============
      Rules (L5): верификация (ограниченная проверка) + поиск по пространству сертификатов (обход).
      Roles (L4): «сертификат» = роль-свидетель, делающий проверку Element-ограниченной;
                  «решено» = статус входа; верификатор/решатель = роль-оракулы.
      Elements  : входы, сертификаты, bool-функции проверки.
    ДИАГНОСТИКА (P4): P vs NP — уточнение по ЭФФЕКТИВНОСТИ внутри РАЗРЕШИМОГО (Element-в-смысле-
      терминирования) слоя, НЕ граница разрешимости.  Три уровня: (1) cost-free ∃-верификация =
      полуразрешимо (Σ1, role-limit как halting); (2) полиномиальные сертификаты = разрешимо
      перебором (Element, тотально); (3) P vs NP = полиномиален ли поиск (P) или ускользает от
      всякого полинома (NP∖P) — НЕ моделируется здесь.  Барьеры (релятивизация/natural proofs/
      алгебраизация) = диагностика смешения уровней (описаны, не формализованы).  ЭТО ОБРАМЛЕНИЕ,
      НЕ ДОКАЗАТЕЛЬСТВО; сепарация не заявляется.

    STATUS: 4 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import List Bool.
Import ListNotations.

Section PvsNP.

  Variable Input : Type.
  Variable Cert  : Type.
  Variable L : Input -> Prop.       (* the decision problem *)

  (** A verifier for L: x ∈ L iff some certificate makes the bounded check pass. *)
  Definition verifies (v : Input -> Cert -> bool) : Prop :=
    forall x, L x <-> exists c, v x c = true.

  (** A decider for L (decide WITHOUT a certificate). *)
  Definition Decider (dec : Input -> bool) : Prop :=
    forall x, dec x = true <-> L x.

  Definition in_NP : Prop := exists v, verifies v.
  Definition in_P  : Prop := exists dec, Decider dec.

  (** Verification is an ELEMENT check: with a certificate, the verifier terminates with a bool. *)
  Lemma verification_is_element :
    forall (v : Input -> Cert -> bool) x c, {v x c = true} + {v x c = false}.
  Proof. intros v x c. destruct (v x c); [left | right]; reflexivity. Qed.

  (** P ⊆ NP : a decider is a verifier that ignores the certificate. *)
  Lemma P_subset_NP : Cert -> in_P -> in_NP.
  Proof.
    intros c0 [dec Hdec]. exists (fun x _ => dec x). intro x. split.
    - intro Hx. exists c0. apply (proj2 (Hdec x)). exact Hx.
    - intros [c Hc]. apply (proj1 (Hdec x)). exact Hc.
  Qed.

  (** A finite COVERING search space decides an NP problem (bounded brute-force): NP is TOTAL.
      The open question is the COST of this search — NOT modelled here. *)
  Lemma NP_search_decides :
    forall (v : Input -> Cert -> bool), verifies v ->
    forall (certs : Input -> list Cert),
      (forall x c, v x c = true -> In c (certs x)) ->
      forall x, L x <-> existsb (v x) (certs x) = true.
  Proof.
    intros v Hver certs Hcov x. split.
    - intro Hx. apply (proj1 (Hver x)) in Hx. destruct Hx as [c Hc].
      apply existsb_exists. exists c. split; [apply Hcov; exact Hc | exact Hc].
    - intro He. apply existsb_exists in He. destruct He as [c [_ Hc]].
      apply (proj2 (Hver x)). exists c. exact Hc.
  Qed.

  (** The brute-force decider, explicitly: an NP problem with a bounded search is decidable
      (Element) — only the cost (here exponential) is the issue. *)
  Lemma NP_bounded_search_decidable :
    forall (v : Input -> Cert -> bool), verifies v ->
    forall (certs : Input -> list Cert),
      (forall x c, v x c = true -> In c (certs x)) ->
      Decider (fun x => existsb (v x) (certs x)).
  Proof.
    intros v Hver certs Hcov x. split; intro H.
    - exact (proj2 (NP_search_decides v Hver certs Hcov x) H).
    - exact (proj1 (NP_search_decides v Hver certs Hcov x) H).
  Qed.

  (** THE P vs NP QUESTION, NAMED — and PROVED NEITHER WAY.  In_NP -> in_P is not provable here
      (with unbounded certificates the ∃ is only semi-decidable; with bounded certificates the
      decider above is brute-force/exponential).  The REAL question is whether the polynomial COST
      can be achieved — which this file deliberately does not model. *)
  Definition P_collapses_NP : Prop := in_NP -> in_P.

End PvsNP.

(** Barriers as level-mixing diagnostics (DESCRIBED, not formalized):
      - Relativization (Baker–Gill–Solovay): a proof that relativizes treats the oracle as an
        Element you may consult freely — but P vs NP is sensitive to the oracle (∃ oracles both
        ways), so a relativizing argument mixes the level of the machine with the level of its
        oracle access.  An E/R/R-clean separation must be non-relativizing.
      - Natural proofs (Razborov–Rudich): a "largeness+constructivity" lower-bound property is
        itself an Element-decidable predicate on functions; if it were too effective it would break
        pseudorandomness — i.e. the diagnostic that the proof-method must not be a cheaply-decidable
        role over the function space.
      - Algebraization (Aaronson–Wigderson): extends relativization to low-degree oracle
        extensions — the same level-mixing one rung up.
    These say WHERE a separation must live (non-relativizing, non-natural, non-algebraizing); they
    are NOT a separation, and nothing here claims one. *)

Print Assumptions NP_search_decides.
Print Assumptions P_subset_NP.
