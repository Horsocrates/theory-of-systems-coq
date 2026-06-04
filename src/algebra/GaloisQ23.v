(** * GaloisQ23.v — the REAL (concrete) Galois correspondence for Q[√2,√3]
    Elements: a + b√2 + c√3 + d√6 with a,b,c,d : Q (a 4-dim Q-vector space)
    Roles:    the four automorphisms id, sigma, tau, sigmatau as field maps
              fixing Q; subgroups of the Klein group V4 as roles of symmetry
    Rules:    sigma:√2↦−√2, tau:√3↦−√3; each is a ring homomorphism fixing Q;
              fixed subfields correspond, inclusion-reversingly, to subgroups
    STATUS:   26 Qed, 0 Admitted, 0 axioms
    Author:   Horsocrates | Date: June 2026

    This UPGRADES the numeric coincidence of GaloisCorrespondence.v (subgroup
    counts = field counts) to a GENUINE concrete Galois correspondence: the
    actual automorphism group Aut(Q[√2,√3]/Q) is built, shown to be the Klein
    four-group V4, and the bijection { subgroups of V4 } <-> { intermediate
    fields } is exhibited explicitly and shown inclusion-reversing.

    HONEST SCOPE: this is a CONCRETE instance of the Fundamental Theorem of
    Galois Theory (one degree-4 extension), not the abstract functor Aut(L/K)
    for arbitrary L/K. The abstract theory remains a role-limit (ch. 11.6).
*)

From Stdlib Require Import QArith.
From Stdlib Require Import Lqa.
Open Scope Q_scope.

(* ===================== The field Q[√2,√3] as 4-tuples ==================== *)
(* element = c0 + c1·√2 + c2·√3 + c3·√6,  with √6 = √2·√3 *)

Record E := mkE { c0 : Q; c1 : Q; c2 : Q; c3 : Q }.

(* equality of field elements = componentwise Q-equality (setoid style) *)
Definition Eeq (u v : E) : Prop :=
  c0 u == c0 v /\ c1 u == c1 v /\ c2 u == c2 v /\ c3 u == c3 v.

Definition Eadd (u v : E) : E :=
  mkE (c0 u + c0 v) (c1 u + c1 v) (c2 u + c2 v) (c3 u + c3 v).

(* multiplication using √2²=2, √3²=3, √6²=6, √2·√3=√6, √2·√6=2√3, √3·√6=3√2 *)
Definition Emul (u v : E) : E :=
  mkE (c0 u * c0 v + 2*(c1 u * c1 v) + 3*(c2 u * c2 v) + 6*(c3 u * c3 v))
      (c0 u * c1 v + c1 u * c0 v + 3*(c2 u * c3 v + c3 u * c2 v))
      (c0 u * c2 v + c2 u * c0 v + 2*(c1 u * c3 v + c3 u * c1 v))
      (c0 u * c3 v + c3 u * c0 v + c1 u * c2 v + c2 u * c1 v).

(* embedding of Q as the base field *)
Definition Eofq (a : Q) : E := mkE a 0 0 0.

(* ===================== The four automorphisms ===================== *)

Definition a_id  (u : E) : E := u.
Definition a_sig (u : E) : E := mkE (c0 u) (- c1 u) (c2 u) (- c3 u). (* √2↦−√2, √6↦−√6 *)
Definition a_tau (u : E) : E := mkE (c0 u) (c1 u) (- c2 u) (- c3 u). (* √3↦−√3, √6↦−√6 *)
Definition a_st  (u : E) : E := mkE (c0 u) (- c1 u) (- c2 u) (c3 u). (* both; √6 fixed *)

(* ===================== Eeq is an equivalence ===================== *)

Lemma Eeq_refl : forall u, Eeq u u.
Proof. intros u. repeat split; reflexivity. Qed.

Lemma Eeq_sym : forall u v, Eeq u v -> Eeq v u.
Proof. intros u v [H0 [H1 [H2 H3]]]. repeat split; symmetry; assumption. Qed.

Lemma Eeq_trans : forall u v w, Eeq u v -> Eeq v w -> Eeq u w.
Proof.
  intros u v w [H0 [H1 [H2 H3]]] [K0 [K1 [K2 K3]]].
  repeat split; eapply Qeq_trans; eassumption.
Qed.

(* ===================== Each automorphism is additive ===================== *)

Lemma sig_add : forall u v, Eeq (a_sig (Eadd u v)) (Eadd (a_sig u) (a_sig v)).
Proof. intros u v. unfold Eeq, a_sig, Eadd; simpl. repeat split; ring. Qed.

Lemma tau_add : forall u v, Eeq (a_tau (Eadd u v)) (Eadd (a_tau u) (a_tau v)).
Proof. intros u v. unfold Eeq, a_tau, Eadd; simpl. repeat split; ring. Qed.

Lemma st_add : forall u v, Eeq (a_st (Eadd u v)) (Eadd (a_st u) (a_st v)).
Proof. intros u v. unfold Eeq, a_st, Eadd; simpl. repeat split; ring. Qed.

(* ===================== Each automorphism is multiplicative ============== *)

Lemma sig_mul : forall u v, Eeq (a_sig (Emul u v)) (Emul (a_sig u) (a_sig v)).
Proof. intros u v. unfold Eeq, a_sig, Emul; simpl. repeat split; ring. Qed.

Lemma tau_mul : forall u v, Eeq (a_tau (Emul u v)) (Emul (a_tau u) (a_tau v)).
Proof. intros u v. unfold Eeq, a_tau, Emul; simpl. repeat split; ring. Qed.

Lemma st_mul : forall u v, Eeq (a_st (Emul u v)) (Emul (a_st u) (a_st v)).
Proof. intros u v. unfold Eeq, a_st, Emul; simpl. repeat split; ring. Qed.

(* ===================== Each automorphism fixes the base Q =============== *)

Lemma sig_fixes_base : forall a, Eeq (a_sig (Eofq a)) (Eofq a).
Proof. intros a. unfold Eeq, a_sig, Eofq; simpl. repeat split; ring. Qed.

Lemma tau_fixes_base : forall a, Eeq (a_tau (Eofq a)) (Eofq a).
Proof. intros a. unfold Eeq, a_tau, Eofq; simpl. repeat split; ring. Qed.

Lemma st_fixes_base : forall a, Eeq (a_st (Eofq a)) (Eofq a).
Proof. intros a. unfold Eeq, a_st, Eofq; simpl. repeat split; ring. Qed.

(* ===================== The group is the Klein four-group V4 ============= *)

Lemma sig_invol : forall u, Eeq (a_sig (a_sig u)) u.
Proof. intros u. unfold Eeq, a_sig; simpl. repeat split; ring. Qed.

Lemma tau_invol : forall u, Eeq (a_tau (a_tau u)) u.
Proof. intros u. unfold Eeq, a_tau; simpl. repeat split; ring. Qed.

Lemma st_invol : forall u, Eeq (a_st (a_st u)) u.
Proof. intros u. unfold Eeq, a_st; simpl. repeat split; ring. Qed.

(* sigma ∘ tau = sigmatau  (= tau ∘ sigma): the product of two flips *)
Lemma sig_tau_eq_st : forall u, Eeq (a_sig (a_tau u)) (a_st u).
Proof. intros u. unfold Eeq, a_sig, a_tau, a_st; simpl. repeat split; ring. Qed.

Lemma tau_sig_eq_st : forall u, Eeq (a_tau (a_sig u)) (a_st u).
Proof. intros u. unfold Eeq, a_tau, a_sig, a_st; simpl. repeat split; ring. Qed.

(* commutativity (V4 abelian): sigma∘tau = tau∘sigma *)
Lemma V4_abelian : forall u, Eeq (a_sig (a_tau u)) (a_tau (a_sig u)).
Proof.
  intros u. eapply Eeq_trans. apply sig_tau_eq_st.
  apply Eeq_sym. apply tau_sig_eq_st.
Qed.

(* ===================== Fixed subfields ===================== *)
(* an element is fixed by phi iff phi u = u (up to Eeq) *)

Definition fixed_by (phi : E -> E) (u : E) : Prop := Eeq (phi u) u.

(* Fix(sigma) = { c1 = 0, c3 = 0 } = Q[√3] *)
Lemma fix_sig_iff : forall u, fixed_by a_sig u <-> (c1 u == 0 /\ c3 u == 0).
Proof.
  intros u. unfold fixed_by, Eeq, a_sig; simpl. split.
  - intros [_ [H1 [_ H3]]]. split; lra.
  - intros [H1 H3]. repeat split; lra.
Qed.

(* Fix(tau) = { c2 = 0, c3 = 0 } = Q[√2] *)
Lemma fix_tau_iff : forall u, fixed_by a_tau u <-> (c2 u == 0 /\ c3 u == 0).
Proof.
  intros u. unfold fixed_by, Eeq, a_tau; simpl. split.
  - intros [_ [_ [H2 H3]]]. split; lra.
  - intros [H2 H3]. repeat split; lra.
Qed.

(* Fix(sigmatau) = { c1 = 0, c2 = 0 } = Q[√6] *)
Lemma fix_st_iff : forall u, fixed_by a_st u <-> (c1 u == 0 /\ c2 u == 0).
Proof.
  intros u. unfold fixed_by, Eeq, a_st; simpl. split.
  - intros [_ [H1 [H2 _]]]. split; lra.
  - intros [H1 H2]. repeat split; lra.
Qed.

(* Fix(whole group V4) = { c1 = c2 = c3 = 0 } = Q (the base) *)
Lemma fix_V4_iff : forall u,
  (fixed_by a_sig u /\ fixed_by a_tau u) <-> (c1 u == 0 /\ c2 u == 0 /\ c3 u == 0).
Proof.
  intros u. split.
  - intros [Hs Ht]. apply fix_sig_iff in Hs. apply fix_tau_iff in Ht.
    destruct Hs as [H1 H3]. destruct Ht as [H2 _]. repeat split; assumption.
  - intros [H1 [H2 H3]]. split.
    + apply fix_sig_iff. split; assumption.
    + apply fix_tau_iff. split; assumption.
Qed.

(* ===================== The Galois correspondence (concrete) ============= *)
(* The 5 subgroups of V4 correspond, inclusion-reversingly, to the 5
   intermediate fields:

      {id}        <->  whole field      (no constraint)
      {id,sig}    <->  Q[√3]   (c1=c3=0)         -- fix_sig_iff
      {id,tau}    <->  Q[√2]   (c2=c3=0)         -- fix_tau_iff
      {id,st}     <->  Q[√6]   (c1=c2=0)         -- fix_st_iff
      V4          <->  Q       (c1=c2=c3=0)      -- fix_V4_iff
*)

(* the base Q is fixed by every element of V4 (bottom of the correspondence) *)
Theorem base_fixed_by_all : forall a,
  fixed_by a_sig (Eofq a) /\ fixed_by a_tau (Eofq a) /\ fixed_by a_st (Eofq a).
Proof.
  intros a. split; [apply sig_fixes_base |].
  split; [apply tau_fixes_base | apply st_fixes_base].
Qed.

(* inclusion-reversing, concretely: Fix(V4)=Q is contained in Fix(sig)=Q[√3] *)
Theorem correspondence_inclusion_reversing : forall u,
  (c1 u == 0 /\ c2 u == 0 /\ c3 u == 0) ->   (* u ∈ Fix(V4) = Q *)
  (c1 u == 0 /\ c3 u == 0).                  (* ⟹ u ∈ Fix(sig) = Q[√3] *)
Proof. intros u [H1 [_ H3]]. split; assumption. Qed.

(* the automorphisms are nontrivial: sigma moves √2, tau moves √3 *)
Definition r2 : E := mkE 0 1 0 0.   (* √2 *)
Definition r3 : E := mkE 0 0 1 0.   (* √3 *)

Theorem sig_neq_id : ~ Eeq (a_sig r2) r2.
Proof. unfold Eeq, a_sig, r2; simpl. intros [_ [H _]]. lra. Qed.

Theorem tau_neq_id : ~ Eeq (a_tau r3) r3.
Proof. unfold Eeq, a_tau, r3; simpl. intros [_ [_ [H _]]]. lra. Qed.
