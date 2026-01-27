(* ========================================================================= *)
(*                       HEINE-BOREL THEOREM                                 *)
(*           Compactness via Finite Subcovers as Processes                   *)
(*                                                                           *)
(*  Part of: Theory of Systems - Coq Formalization (E/R/R Framework)         *)
(*  Author:  Horsocrates | Version: 2.0 (E/R/R) | Date: January 2026         *)
(*                                                                           *)
(*  STATUS: 22 Qed, 2 Admitted (intentional - demonstrates Q limitation)     *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  E/R/R INTERPRETATION:                                                    *)
(*  =====================                                                    *)
(*                                                                           *)
(*  This file demonstrates a LIMITATION of Q-based processes:                *)
(*                                                                           *)
(*    Elements = RealProcess = nat -> Q (Cauchy sequences over Q)            *)
(*    Roles    = in_interval, covers relation                                *)
(*    Rules    = valid_cover (positive radius at each point)                 *)
(*                                                                           *)
(*  KEY INSIGHT (P4 + Completeness):                                         *)
(*    Heine-Borel requires COMPLETENESS which Q lacks.                       *)
(*    The admitted lemmas show where completeness would be needed.           *)
(*    This is NOT a failure but a DEMONSTRATION of Q's limitations.          *)
(*                                                                           *)
(*  PHILOSOPHICAL NOTE:                                                      *)
(*    In Theory of Systems, we work with PROCESSES (nat -> Q).               *)
(*    Heine-Borel over R requires actual limits, not just processes.         *)
(*    The file shows that compactness is about COMPLETION of processes.      *)
(*                                                                           *)
(* ========================================================================= *)

(**
  OVERVIEW
  --------
  We formalize the Heine-Borel theorem: every open cover of [a,b] has a
  finite subcover. The key insight is that we work with *processes* rather
  than completed infinite objects.
  
  An "open cover" is represented as a function that, given any point x in
  [a,b], returns a positive radius delta such that the interval 
  (x - delta, x + delta) is "covered". A finite subcover is a finite list
  of such intervals that covers [a,b].
  
  NO AXIOM OF INFINITY is used - all quantification is over natural numbers.
*)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qfield.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Q_scope.

(* ===== SECTION 1: BASIC DEFINITIONS ===== *)

Definition RealProcess := nat -> Q.

Definition is_Cauchy (R : RealProcess) : Prop := 
  forall eps : Q, eps > 0 -> exists N : nat, forall m n : nat, 
    (m > N)%nat -> (n > N)%nat -> Qabs (R m - R n) < eps.

Definition in_interval (a b : Q) (R : RealProcess) : Prop := 
  forall n : nat, a <= R n /\ R n <= b.

(* An open cover assigns to each point x a positive radius *)
Definition OpenCover := Q -> Q.

Definition valid_cover (C : OpenCover) (a b : Q) : Prop :=
  forall x : Q, a <= x <= b -> C x > 0.

(* IMPORTANT: valid_cover is pointwise, but Heine-Borel over Q requires
   a uniform lower bound. Without completeness, nested intervals may
   converge to an irrational, breaking the classical proof. *)

(* Uniform cover: there exists a global minimum radius (Lebesgue number) *)
Definition uniform_cover (C : OpenCover) (a b delta : Q) : Prop :=
  delta > 0 /\ forall x : Q, a <= x <= b -> C x >= delta.

(* A point y is covered by the ball around x with radius C(x) *)
Definition covered_by (C : OpenCover) (x y : Q) : Prop :=
  Qabs (y - x) < C x.

(* ===== SECTION 2: FINITE SUBCOVERS ===== *)

(* A finite subcover is a list of centers *)
Definition FiniteSubcover := list Q.

(* Check if y is covered by some ball in the subcover *)
Fixpoint is_covered (C : OpenCover) (centers : FiniteSubcover) (y : Q) : Prop :=
  match centers with
  | [] => False
  | x :: rest => covered_by C x y \/ is_covered C rest y
  end.

(* A finite subcover covers [a,b] *)
Definition covers_interval (C : OpenCover) (centers : FiniteSubcover) (a b : Q) : Prop :=
  forall y : Q, a <= y <= b -> is_covered C centers y.

(* ===== SECTION 3: LEBESGUE NUMBER ===== *)

(**
  The Lebesgue number lemma: for any open cover of a compact set,
  there exists delta > 0 such that every ball of radius delta is
  contained in some element of the cover.
  
  For us: exists delta such that for any x in [a,b], the ball
  B(x, delta) is contained in some B(c, C(c)) from the cover.
*)

Definition has_lebesgue_number (C : OpenCover) (a b delta : Q) : Prop :=
  delta > 0 /\
  forall x : Q, a <= x <= b ->
  exists c : Q, a <= c <= b /\ 
  forall y : Q, Qabs (y - x) < delta -> covered_by C c y.

(* ===== SECTION 4: BISECTION APPROACH ===== *)

(**
  We prove Heine-Borel by bisection: if [a,b] cannot be covered by
  finitely many balls, then neither can one of [a,m] or [m,b].
  This gives a nested sequence of intervals, which by Cauchy completeness
  converges to a point. But that point has a positive radius in the cover,
  contradiction.
*)

Fixpoint pow2 (n : nat) : positive :=
  match n with O => 1%positive | S n' => (2 * pow2 n')%positive end.

Definition Qpow2 (n : nat) : Q := Z.pos (pow2 n) # 1.

Lemma Qpow2_pos : forall n, 0 < Qpow2 n.
Proof. intro. unfold Qpow2, Qlt. simpl. lia. Qed.

Lemma Qpow2_nonzero : forall n, ~ Qpow2 n == 0.
Proof. intro n. intro H. pose proof (Qpow2_pos n). rewrite H in H0. apply Qlt_irrefl in H0. exact H0. Qed.

(* Bisection state *)
Record HBState := mkHB {
  hb_left : Q;
  hb_right : Q
}.

Definition hb_init (a b : Q) : HBState := mkHB a b.

(* For Heine-Borel, we need to track which half "cannot be finitely covered" *)
(* We use a simplified approach: just bisect and track intervals *)

Definition hb_step (s : HBState) (go_left : bool) : HBState :=
  let mid := (hb_left s + hb_right s) / 2 in
  if go_left 
  then mkHB (hb_left s) mid
  else mkHB mid (hb_right s).

(* Helper: hb_step halves width *)
Lemma hb_step_halves : forall s go_left,
  hb_right (hb_step s go_left) - hb_left (hb_step s go_left) ==
  (hb_right s - hb_left s) / 2.
Proof.
  intros s go_left. unfold hb_step.
  destruct go_left; simpl.
  - (* go_left = true: [l, (l+r)/2] *)
    unfold Qeq, Qminus, Qplus, Qdiv, Qmult, Qopp, Qinv. simpl.
    destruct (hb_left s) as [lp lq].
    destruct (hb_right s) as [rp rq]. simpl. lia.
  - (* go_left = false: [(l+r)/2, r] *)
    unfold Qeq, Qminus, Qplus, Qdiv, Qmult, Qopp, Qinv. simpl.
    destruct (hb_left s) as [lp lq].
    destruct (hb_right s) as [rp rq]. simpl. lia.
Qed.

Lemma Qpow2_S : forall n, Qpow2 (S n) == 2 * Qpow2 n.
Proof.
  intro n. unfold Qpow2. simpl. unfold Qeq, Qmult. simpl. lia.
Qed.

(* Width after n bisections *)
Lemma hb_width : forall a b n (choices : nat -> bool),
  let s := fold_left (fun s i => hb_step s (choices i)) (seq 0 n) (hb_init a b) in
  hb_right s - hb_left s == (b - a) / Qpow2 n.
Proof.
  intros a b n choices.
  (* Prove by induction on n *)
  induction n.
  - (* Base: n = 0 *)
    simpl. unfold hb_init. simpl.
    unfold Qeq, Qdiv, Qmult, Qminus, Qplus, Qopp, Qinv, Qpow2. simpl.
    destruct a as [ap aq], b as [bp bq]. simpl. lia.
  - (* Inductive: n = S n' *)
    (* seq 0 (S n) = seq 0 n ++ [n] *)
    rewrite seq_S.
    rewrite fold_left_app. simpl.
    (* After fold_left on seq 0 n, we have state s_n *)
    (* Then we apply one more hb_step *)
    set (s_n := fold_left (fun s i => hb_step s (choices i)) (seq 0 n) (hb_init a b)).
    (* By IH: hb_right s_n - hb_left s_n == (b-a)/2^n *)
    assert (IH : hb_right s_n - hb_left s_n == (b - a) / Qpow2 n).
    { unfold s_n. exact IHn. }
    (* After one more step: width halves *)
    apply Qeq_trans with ((hb_right s_n - hb_left s_n) / 2).
    + apply hb_step_halves.
    + rewrite IH. rewrite Qpow2_S.
      (* (b-a)/2^n / 2 == (b-a) / (2 * 2^n) *)
      unfold Qdiv.
      setoid_rewrite Qinv_mult_distr.
      ring.
Qed.

(* ===== SECTION 5: MAIN THEOREM ===== *)

(**
  Heine-Borel: For any valid open cover of [a,b], there exists
  a finite subcover.
  
  Proof sketch:
  1. Assume no finite subcover exists
  2. By bisection, construct a Cauchy sequence converging to some c
  3. The cover assigns positive delta = C(c) to c
  4. For large enough n, the bisection interval is contained in B(c, delta)
  5. But then that interval IS finitely covered, contradiction
*)

(* Helper: A single ball covers a small enough interval *)
(* For any x, c in [a,b]: |x - c| <= b - a *)

(* First, a helper about Qabs *)
Lemma Qabs_diff_le_width : forall a b x c : Q,
  a <= x -> x <= b -> a <= c -> c <= b ->
  Qabs (x - c) <= b - a.
Proof.
  intros a b x c Hax Hxb Hac Hcb.
  apply Qabs_Qle_condition.
  split.
  - (* -(b - a) <= x - c *)
    (* Equivalently: a - b <= x - c, i.e., a + c <= x + b *)
    (* From Hax (a <= x) and Hcb (c <= b) we get a + c <= x + b *)
    apply Qle_trans with (a - c).
    + (* -(b-a) <= a - c, i.e., -b + a <= a - c, i.e., -b <= -c, i.e., c <= b *)
      (* This is Hcb after manipulation *)
      setoid_replace (- (b - a)) with (a - b) by ring.
      unfold Qle, Qminus, Qplus, Qopp.
      destruct a as [ap aq], b as [bp bq], c as [cp cq]. simpl.
      unfold Qle in Hcb. simpl in Hcb.
      nia.
    + (* a - c <= x - c, i.e., a <= x *)
      unfold Qle, Qminus, Qplus, Qopp.
      destruct a as [ap aq], x as [xp xq], c as [cp cq]. simpl.
      unfold Qle in Hax. simpl in Hax.
      nia.
  - (* x - c <= b - a *)
    apply Qle_trans with (b - c).
    + (* x - c <= b - c, i.e., x <= b *)
      unfold Qle, Qminus, Qplus, Qopp.
      destruct b as [bp bq], x as [xp xq], c as [cp cq]. simpl.
      unfold Qle in Hxb. simpl in Hxb.
      nia.
    + (* b - c <= b - a, i.e., -c <= -a, i.e., a <= c *)
      unfold Qle, Qminus, Qplus, Qopp.
      destruct a as [ap aq], b as [bp bq], c as [cp cq]. simpl.
      unfold Qle in Hac. simpl in Hac.
      nia.
Qed.

Lemma ball_covers_small_interval : forall (C : OpenCover) a b c,
  a <= c <= b ->
  C c > 0 ->
  b - a < C c ->
  (forall x, a <= x <= b -> covered_by C c x).
Proof.
  intros C a b c Hc Hdelta Hsmall.
  intros x Hx.
  unfold covered_by.
  destruct Hx as [Hxa Hxb].
  destruct Hc as [Hca Hcb].
  apply Qle_lt_trans with (b - a); [|exact Hsmall].
  apply Qabs_diff_le_width; assumption.
Qed.

(* Archimedean: width eventually smaller than any positive number *)
(* First, pow2 grows without bound *)
Lemma pow2_S_eq : forall n, pow2 (S n) = (2 * pow2 n)%positive.
Proof. intro n. reflexivity. Qed.

Lemma pow2_ge_Sn : forall n, (Z.pos (pow2 n) >= Z.of_nat (S n))%Z.
Proof.
  induction n.
  - simpl. lia.
  - rewrite pow2_S_eq.
    rewrite Pos2Z.inj_mul.
    rewrite Nat2Z.inj_succ.
    lia.
Qed.

Lemma pow2_exceeds_pos : forall z : Z, (z > 0)%Z -> exists n, (Z.pos (pow2 n) > z)%Z.
Proof.
  intros z Hz.
  exists (Z.to_nat z).
  pose proof (pow2_ge_Sn (Z.to_nat z)) as H.
  (* H: Z.pos (pow2 (Z.to_nat z)) >= Z.of_nat (S (Z.to_nat z)) *)
  (* S (Z.to_nat z) = Z.to_nat z + 1 *)
  (* Z.of_nat (S (Z.to_nat z)) = Z.of_nat (Z.to_nat z) + 1 = z + 1 > z *)
  assert (Heq : Z.of_nat (S (Z.to_nat z)) = (z + 1)%Z).
  { rewrite Nat2Z.inj_succ. rewrite Z2Nat.id by lia. lia. }
  rewrite Heq in H. lia.
Qed.

Lemma pow2_eventually_large : forall w eps : Q,
  w > 0 -> eps > 0 ->
  exists N : nat, w / Qpow2 N < eps.
Proof.
  intros w eps Hw Heps.
  destruct w as [wp wq]. destruct eps as [ep eq].
  unfold Qlt in *. simpl in *.
  assert (Hwp : (wp > 0)%Z) by lia.
  assert (Hep : (ep > 0)%Z) by lia.
  destruct (pow2_exceeds_pos (wp * Z.pos eq)%Z) as [N HN].
  { lia. }
  exists N.
  unfold Qlt, Qdiv, Qmult, Qinv, Qpow2. simpl.
  ring_simplify.
  assert (H1 : (Z.pos (pow2 N) > wp * Z.pos eq)%Z) by exact HN.
  assert (H2 : (ep * Z.pos wq >= 1)%Z).
  { assert (Hep1 : (ep >= 1)%Z) by lia.
    assert (Hwq1 : (Z.pos wq >= 1)%Z) by lia.
    nia. }
  nia.
Qed.

(* ===== ADDITIONAL HELPERS FOR HEINE-BOREL ===== *)

(* Coverable predicate *)
Definition coverable (C : OpenCover) (a b : Q) : Prop :=
  exists centers, covers_interval C centers a b.

(* is_covered preserves under append *)
Lemma is_covered_app_l : forall C centers1 centers2 y,
  is_covered C centers1 y -> is_covered C (centers1 ++ centers2) y.
Proof.
  intros C c1 c2 y H.
  induction c1 as [|c rest IH]; simpl in *; [contradiction|].
  destruct H; [left | right; apply IH]; assumption.
Qed.

Lemma is_covered_app_r : forall C centers1 centers2 y,
  is_covered C centers2 y -> is_covered C (centers1 ++ centers2) y.
Proof.
  intros C c1 c2 y H.
  induction c1 as [|c rest IH]; simpl; [exact H | right; apply IH].
Qed.

(* Cover concatenation *)
Lemma cover_concat : forall C centers1 centers2 a m b,
  covers_interval C centers1 a m ->
  covers_interval C centers2 m b ->
  covers_interval C (centers1 ++ centers2) a b.
Proof.
  intros C c1 c2 a m b H1 H2 y [Hay Hyb].
  destruct (Qlt_le_dec y m) as [Hym | Hmy].
  - apply is_covered_app_l. apply H1. split; [exact Hay | apply Qlt_le_weak; exact Hym].
  - apply is_covered_app_r. apply H2. split; [exact Hmy | exact Hyb].
Qed.

(* If both halves coverable, whole is coverable *)
Lemma coverable_concat : forall C a m b,
  coverable C a m -> coverable C m b -> coverable C a b.
Proof.
  intros C a m b [c1 H1] [c2 H2].
  exists (c1 ++ c2). apply cover_concat with m; assumption.
Qed.

(* Classical: if whole not coverable, at least one half not coverable *)
Lemma not_coverable_half : forall C a b,
  ~coverable C a b -> ~coverable C a ((a+b)/2) \/ ~coverable C ((a+b)/2) b.
Proof.
  intros C a b Hnot.
  destruct (classic (coverable C a ((a+b)/2))) as [Hl|Hl];
  destruct (classic (coverable C ((a+b)/2) b)) as [Hr|Hr].
  - exfalso. apply Hnot. apply coverable_concat with ((a+b)/2); assumption.
  - right. exact Hr.
  - left. exact Hl.
  - left. exact Hl.
Qed.

(* Qabs bound for difference in interval *)
Lemma Qabs_diff_le : forall x y d, x <= y <= x + d -> d >= 0 -> Qabs (y - x) <= d.
Proof.
  intros x y d [Hxy Hyx] Hd.
  apply Qabs_Qle_condition. split.
  - unfold Qle, Qminus, Qplus, Qopp in *. destruct x, y, d. simpl in *. nia.
  - unfold Qle, Qminus, Qplus, Qopp in *. destruct x, y, d. simpl in *. nia.
Qed.

(* Small interval is coverable by single ball *)
Lemma small_interval_coverable : forall C a b c,
  a <= c <= b -> C c > 0 -> b - a < C c ->
  coverable C a b.
Proof.
  intros C a b c Hc Hdelta Hsmall.
  exists [c]. intros y Hy. simpl. left. unfold covered_by.
  apply Qle_lt_trans with (b - a).
  - apply Qabs_diff_le_width; [exact (proj1 Hy) | exact (proj2 Hy) | exact (proj1 Hc) | exact (proj2 Hc)].
  - exact Hsmall.
Qed.

(* Width positive *)
Lemma interval_width_pos : forall a b, a < b -> b - a > 0.
Proof.
  intros a b Hab.
  unfold Qlt, Qminus, Qplus, Qopp in *.
  destruct a as [ap aq], b as [bp bq]. simpl in *.
  ring_simplify. lia.
Qed.

(* ===== MAIN THEOREM ===== *)

(**
  NOTE ON HEINE-BOREL OVER Q:
  
  The classical Heine-Borel theorem (closed bounded interval is compact) 
  DOES NOT HOLD for Q. The reason is that Q lacks completeness:
  nested intervals can "converge" to an irrational number not in Q.
  
  Example: Cover Q  [0,1] with balls avoiding 2/2. No finite subcover
  exists because any finite collection leaves a gap near the irrational.
  
  For our formalization over Q, we ADD A UNIFORM BOUND requirement:
  there exists  > 0 such that C(x)   for all x in [a,b].
  
  This is equivalent to requiring the cover has a Lebesgue number.
  With this assumption, Heine-Borel becomes provable via bisection.
*)

(* Helper: (x/2)/2^N = x/2^{N+1} *)
Lemma div_half_pow2 : forall x N, (x / 2) / Qpow2 N == x / Qpow2 (S N).
Proof.
  intros x N. unfold Qpow2. simpl.
  unfold Qdiv, Qmult, Qinv. destruct x as [xn xd]. simpl.
  unfold Qeq. simpl. ring_simplify. lia.
Qed.

(* Strong induction on bisection depth *)
Lemma Heine_Borel_by_depth : forall N C a b delta,
  a < b ->
  uniform_cover C a b delta ->
  (b - a) / Qpow2 N < delta ->
  coverable C a b.
Proof.
  induction N as [|N IH]; intros C a b delta Hab [Hdelta Huniform] Hwidth.
  - (* N = 0: width = b - a < delta *)
    simpl in Hwidth. unfold Qpow2 in Hwidth. simpl in Hwidth.
    setoid_replace ((b - a) / (1#1)) with (b - a) in Hwidth by field.
    set (c := (a + b) / 2).
    assert (Hc_in : a <= c <= b).
    { split.
      * unfold c. apply Qle_shift_div_l. reflexivity.
        setoid_replace (a * 2) with (a + a) by ring.
        apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak. exact Hab.
      * unfold c. apply Qle_shift_div_r. reflexivity.
        setoid_replace (b * 2) with (b + b) by ring.
        apply Qplus_le_compat. apply Qlt_le_weak. exact Hab. apply Qle_refl. }
    assert (Hc_delta : C c >= delta) by (apply Huniform; exact Hc_in).
    apply small_interval_coverable with c.
    + exact Hc_in.
    + apply Qlt_le_trans with delta. exact Hdelta. exact Hc_delta.
    + apply Qlt_le_trans with delta. exact Hwidth. exact Hc_delta.
  - (* N = S N': bisect *)
    set (c := (a + b) / 2).
    assert (Hc_in : a <= c <= b).
    { split.
      * unfold c. apply Qle_shift_div_l. reflexivity.
        setoid_replace (a * 2) with (a + a) by ring.
        apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak. exact Hab.
      * unfold c. apply Qle_shift_div_r. reflexivity.
        setoid_replace (b * 2) with (b + b) by ring.
        apply Qplus_le_compat. apply Qlt_le_weak. exact Hab. apply Qle_refl. }
    assert (Ham : a < c).
    { unfold c, Qlt, Qdiv, Qplus, Qmult, Qinv in *. destruct a, b. simpl in *. nia. }
    assert (Hcb : c < b).
    { unfold c, Qlt, Qdiv, Qplus, Qmult, Qinv in *. destruct a, b. simpl in *. nia. }
    
    (* Width of each half *)
    assert (Hleft_width : c - a == (b - a) / 2) by (unfold c; field).
    assert (Hright_width : b - c == (b - a) / 2) by (unfold c; field).
    
    (* Bound on each half *)
    assert (Hleft_bound : (c - a) / Qpow2 N < delta).
    { rewrite Hleft_width. rewrite div_half_pow2. exact Hwidth. }
    assert (Hright_bound : (b - c) / Qpow2 N < delta).
    { rewrite Hright_width. rewrite div_half_pow2. exact Hwidth. }
    
    (* Uniform cover on each half *)
    assert (Huniform_left : uniform_cover C a c delta).
    { split. exact Hdelta.
      intros x [Hax Hxc]. apply Huniform. split. exact Hax.
      apply Qle_trans with c. exact Hxc. destruct Hc_in. exact H0. }
    assert (Huniform_right : uniform_cover C c b delta).
    { split. exact Hdelta.
      intros x [Hcx Hxb]. apply Huniform. split.
      apply Qle_trans with c. destruct Hc_in. exact H. exact Hcx. exact Hxb. }
    
    (* Both halves coverable by IH *)
    assert (Hcov_left : coverable C a c) by (apply IH with delta; assumption).
    assert (Hcov_right : coverable C c b) by (apply IH with delta; assumption).
    
    (* Concat *)
    apply coverable_concat with c; assumption.
Qed.

(* Heine-Borel with uniform bound: PROVEN over Q *)
Theorem Heine_Borel_uniform : forall (C : OpenCover) (a b delta : Q),
  a < b ->
  uniform_cover C a b delta ->
  exists centers : FiniteSubcover, covers_interval C centers a b.
Proof.
  intros C a b delta Hab Huniform.
  destruct Huniform as [Hdelta_pos Hbound].
  assert (Hw : b - a > 0).
  { unfold Qlt, Qminus, Qplus, Qopp in *. destruct a, b. simpl in *. lia. }
  destruct (pow2_eventually_large (b - a) delta Hw Hdelta_pos) as [N HN].
  apply Heine_Borel_by_depth with N delta.
  - exact Hab.
  - split. exact Hdelta_pos. exact Hbound.
  - exact HN.
Qed.

(* Original Heine-Borel without uniform bound: NOT PROVABLE over Q *)
(* This is kept as documentation of the classical statement *)
Theorem Heine_Borel : forall (C : OpenCover) (a b : Q),
  a < b ->
  valid_cover C a b ->
  exists centers : FiniteSubcover, covers_interval C centers a b.
Proof.
  intros C a b Hab Hvalid.
  (*
    THIS THEOREM IS FALSE OVER Q.
    
    Counterexample: Let C(x) = |x - 2/2| for x  Q  [0,1].
    Then C(x) > 0 for all rational x (since 2/2 is irrational),
    but there is no finite subcover because any finite collection
    of balls leaves uncovered rationals arbitrarily close to 2/2.
    
    The classical proof requires:
    1. Nested intervals converge to a LIMIT POINT
    2. The limit point c has C(c) > 0
    3. Ball around c covers sufficiently small interval
    
    Step 1 fails in Q: nested intervals may "converge" to an irrational.
    
    For a provable version, use Heine_Borel_uniform with a uniform
    lower bound on the cover radii (Lebesgue number assumption).
  *)
  admit.
Admitted.

(* ===== SECTION 6: COROLLARY - UNIFORM CONTINUITY ===== *)

(**
  A continuous function on [a,b] is uniformly continuous.
  
  Proof: Given eps > 0, for each x in [a,b], continuity gives delta(x) > 0.
  These deltas form an open cover. By Heine-Borel, take finite subcover.
  The minimum delta from the finite subcover works uniformly.
*)

Definition ContinuousFunction := Q -> Q.

Definition pointwise_continuous (f : ContinuousFunction) (x : Q) : Prop :=
  forall eps : Q, eps > 0 -> exists delta : Q, delta > 0 /\
    forall y : Q, Qabs (y - x) < delta -> Qabs (f y - f x) < eps.

Definition continuous_on (f : ContinuousFunction) (a b : Q) : Prop :=
  forall x : Q, a <= x <= b -> pointwise_continuous f x.

Definition uniformly_continuous_on (f : ContinuousFunction) (a b : Q) : Prop :=
  forall eps : Q, eps > 0 -> exists delta : Q, delta > 0 /\
    forall x y : Q, a <= x <= b -> a <= y <= b ->
    Qabs (x - y) < delta -> Qabs (f x - f y) < eps.

Theorem continuity_implies_uniform : forall f a b,
  a < b ->
  continuous_on f a b ->
  uniformly_continuous_on f a b.
Proof.
  intros f a b Hab Hcont.
  unfold uniformly_continuous_on.
  intros eps Heps.
  (*
    THIS THEOREM REQUIRES COMPLETENESS (or equivalent).
    
    The classical proof:
    1. For each x  [a,b], continuity gives delta(x) > 0
    2. These deltas form an open cover
    3. By Heine-Borel (classical), take finite subcover
    4. Minimum delta from finite subcover works uniformly
    
    The problem over Q:
    - Step 3 uses classical Heine-Borel, which is FALSE over Q
    - Even with Heine_Borel_uniform, we need a uniform lower bound on deltas
    - Pointwise continuity does NOT give such a bound
    
    For a provable version, assume uniform continuity directly,
    or work with a specific function class (Lipschitz, etc.).
  *)
  admit.
Admitted.

(* ===== SECTION 7: SUMMARY ===== *)

(**
  PROVEN LEMMAS (22 Qed):
  - Qpow2_pos, Qpow2_nonzero, pow2_eventually_large
  - Heine_Borel_by_depth (bisection induction with uniform bound)
  - Heine_Borel_uniform (main theorem WITH Lebesgue number assumption)
  - coverable_concat, not_coverable_half, small_interval_coverable
  - All helper lemmas for Q arithmetic
  
  ADMITTED (2 lemmas, documented as unprovable over Q):
  - Heine_Borel (classical version WITHOUT uniform bound - FALSE over Q)
  - continuity_implies_uniform (requires completeness - FALSE over Q)
  
  KEY INSIGHT:
  The classical Heine-Borel theorem requires completeness of the underlying
  space. In Q, nested intervals may "converge" to an irrational, breaking
  the proof. The Heine_Borel_uniform version adds a Lebesgue number assumption
  (uniform lower bound on cover radii), making the theorem provable via
  finite bisection.
  
  PHILOSOPHICAL NOTE:
  This demonstrates a genuine limitation: not all classical analysis theorems
  transfer to Q. The process-based approach using Cauchy sequences (nat  Q)
  can recover R-like behavior, but requires explicit completeness axioms.
*)

Print Assumptions Qpow2_pos.
Print Assumptions Qpow2_nonzero.
