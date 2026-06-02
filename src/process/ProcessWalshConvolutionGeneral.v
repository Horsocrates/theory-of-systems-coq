(** * ProcessWalshConvolutionGeneral.v — The Walsh convolution theorem for ALL N = 2ᵏ
      (Part VII, Batch 2 / proposal B2)

    Elements: rational f, g; XOR-indexed sums; N = 2ᵏ
    Roles:    ⊛ = dyadic (XOR) convolution; H = Walsh transform; pointwise product = image
    Rules:    H(f ⊛ g) = (Hf)·(Hg)  — the transform turns dyadic convolution into a
              pointwise product, for EVERY N = 2ᵏ (not just N=4)

    Upgrades the N=4 convolution theorem (ProcessWalshConvolution) to ALL 2ᵏ. The proof
    rests on two pillars: the Walsh CHARACTER property had_k(i,a⊕b)=had_k(i,a)·had_k(i,b)
    (ProcessWalshCharacter, B1), and the reindexing of a finite sum under the XOR-bijection
    n ↦ n⊕m — `xor_perm_q_sum` — proved here by Sylvester block recursion on k (the GPT
    plan-review's flagged bottleneck). All exact over ℚ, 0 axioms.

    HONEST FRONTIER: the continuous / complex Fourier convolution and the L¹ convolution
    algebra remain transcendental; here the dyadic-XOR convolution over ℚ is exact.

    ============ E/R/R разбор ============
      Rules (L5): H(f⊛g)=(Hf)·(Hg) для всех 2ᵏ; ⊛ (XOR-свёртка) ↦ поточечное произведение.
      Roles (L4): ⊛=роль-свёртка; H=роль-преобразование; перестановка n↦n⊕m=роль-переиндексация.
      Elements  : рациональные f,g, XOR-индексы, конечные суммы, N=2ᵏ (L1+P4).
    ДИАГНОСТИКА: точно над ℚ (0 акс) через характер (B1) + перестановочную инвариантность
    q_sum под XOR-биекцией (блочная рекурсия Сильвестра); непрерывная/комплексная — граница.

    STATUS: 7 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import QArith Qabs ZArith Lia Lqa Bool Arith NArith.
From ToS Require Import process.ProcessCore.
From ToS Require Import process.ProcessArithmetic.
From ToS Require Import process.ProcessMCT.
From ToS Require Import process.ProcessFubiniGeneral.      (* q_sum_ext, q_sum_scale, q_sum_swap *)
From ToS Require Import process.ProcessSelfAdjointSpectral. (* op_apply *)
From ToS Require Import process.ProcessL2BesselGeneral.    (* q_sum_ext_bounded *)
From ToS Require Import process.ProcessWalshHadamard.      (* had, pow2, pow2_pos, q_sum_split *)
From ToS Require Import process.ProcessWalshCharacter.     (* had_character, lxor_mod_pow2, leb_pow2_lxor, lt_pow2_of_high_bits, testbit_high_pow2, pow2_eq *)
From ToS Require Import process.ProcessWalshConvolution.   (* dconv *)

Open Scope Q_scope.

(* ===================================================================== *)
(*  Block arithmetic of XOR with a power-of-two split                      *)
(* ===================================================================== *)

(** For x < 2^{k+1}, division by 2ᵏ is exactly the leading bit (0 or 1). *)
Lemma div_pow2_S : forall k x, (x < pow2 (S k))%nat ->
  (x / pow2 k)%nat = (if Nat.leb (pow2 k) x then 1 else 0)%nat.
Proof.
  intros k x Hx.
  assert (Hp : (pow2 k <> 0)%nat) by (pose proof (pow2_pos k); lia).
  assert (Hx2 : (x < 2 * pow2 k)%nat) by (cbn [pow2] in Hx; lia).
  assert (Hd : (x / pow2 k < 2)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  pose proof (Nat.div_mod_eq x (pow2 k)) as Hdm.
  pose proof (Nat.mod_upper_bound x (pow2 k) Hp) as Hr.
  destruct (Nat.eq_dec (x / pow2 k) 0) as [E0 | E1].
  - rewrite E0 in Hdm. rewrite Nat.mul_0_r in Hdm.
    assert (Hlb : Nat.leb (pow2 k) x = false) by (apply Nat.leb_gt; lia).
    rewrite E0, Hlb. reflexivity.
  - assert (E1' : (x / pow2 k = 1)%nat) by lia.
    rewrite E1' in Hdm. rewrite Nat.mul_1_r in Hdm.
    assert (Hlb : Nat.leb (pow2 k) x = true) by (apply Nat.leb_le; lia).
    rewrite E1', Hlb. reflexivity.
Qed.

(** Reconstruct a XOR from its leading bit and its low part. *)
Lemma lxor_recon : forall k n m, (n < pow2 (S k))%nat -> (m < pow2 (S k))%nat ->
  Nat.lxor n m =
  ((if xorb (Nat.leb (pow2 k) n) (Nat.leb (pow2 k) m) then pow2 k else 0)
   + Nat.lxor (n mod pow2 k) (m mod pow2 k))%nat.
Proof.
  intros k n m Hn Hm.
  assert (Hxlt : (Nat.lxor n m < pow2 (S k))%nat).
  { rewrite pow2_eq. apply lt_pow2_of_high_bits. intros j Hj.
    rewrite Nat.lxor_spec, (testbit_high_pow2 n (S k) j Hn Hj),
            (testbit_high_pow2 m (S k) j Hm Hj). reflexivity. }
  pose proof (Nat.div_mod_eq (Nat.lxor n m) (pow2 k)) as Hdm.
  rewrite (lxor_mod_pow2 n m k) in Hdm.
  rewrite (div_pow2_S k (Nat.lxor n m) Hxlt) in Hdm.
  rewrite (leb_pow2_lxor k n m Hn Hm) in Hdm.
  rewrite Hdm.
  destruct (xorb (Nat.leb (pow2 k) n) (Nat.leb (pow2 k) m)); simpl; lia.
Qed.

(** XOR of a "high" index with a "low" index keeps the leading bit. *)
Lemma lxor_hi_lo : forall k i m, (i < pow2 k)%nat -> (m < pow2 k)%nat ->
  Nat.lxor (pow2 k + i) m = (pow2 k + Nat.lxor i m)%nat.
Proof.
  intros k i m Hi Hm.
  assert (Hni : (pow2 k + i < pow2 (S k))%nat) by (cbn [pow2]; lia).
  assert (Hm' : (m < pow2 (S k))%nat) by (cbn [pow2]; lia).
  rewrite (lxor_recon k (pow2 k + i) m Hni Hm').
  assert (L1 : Nat.leb (pow2 k) (pow2 k + i) = true) by (apply Nat.leb_le; lia).
  assert (L2 : Nat.leb (pow2 k) m = false) by (apply Nat.leb_gt; lia).
  assert (M1 : ((pow2 k + i) mod pow2 k = i)%nat).
  { replace (pow2 k + i)%nat with (i + 1 * pow2 k)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small; exact Hi. }
  assert (M2 : (m mod pow2 k = m)%nat) by (apply Nat.mod_small; exact Hm).
  rewrite L1, L2, M1, M2. simpl. reflexivity.
Qed.

(** XOR of two "high" indices cancels the leading bit. *)
Lemma lxor_hi_hi : forall k i m, (i < pow2 k)%nat -> (m < pow2 k)%nat ->
  Nat.lxor (pow2 k + i) (pow2 k + m) = Nat.lxor i m.
Proof.
  intros k i m Hi Hm.
  assert (Hni : (pow2 k + i < pow2 (S k))%nat) by (cbn [pow2]; lia).
  assert (Hnm : (pow2 k + m < pow2 (S k))%nat) by (cbn [pow2]; lia).
  rewrite (lxor_recon k (pow2 k + i) (pow2 k + m) Hni Hnm).
  assert (L1 : Nat.leb (pow2 k) (pow2 k + i) = true) by (apply Nat.leb_le; lia).
  assert (L2 : Nat.leb (pow2 k) (pow2 k + m) = true) by (apply Nat.leb_le; lia).
  assert (M1 : ((pow2 k + i) mod pow2 k = i)%nat).
  { replace (pow2 k + i)%nat with (i + 1 * pow2 k)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small; exact Hi. }
  assert (M2 : ((pow2 k + m) mod pow2 k = m)%nat).
  { replace (pow2 k + m)%nat with (m + 1 * pow2 k)%nat by lia.
    rewrite Nat.Div0.mod_add. apply Nat.mod_small; exact Hm. }
  rewrite L1, L2, M1, M2. simpl. reflexivity.
Qed.

(* ===================================================================== *)
(*  THE BOTTLENECK: q_sum is invariant under the XOR-bijection n ↦ n⊕m     *)
(* ===================================================================== *)

Lemma xor_perm_q_sum : forall k m F,
  (m < pow2 k)%nat ->
  q_sum (fun n => F (Nat.lxor n m)) (pow2 k) == q_sum F (pow2 k).
Proof.
  induction k as [|k IH]; intros m F Hm.
  - cbn [pow2] in Hm. assert (Hm0 : m = 0%nat) by lia. subst m.
    assert (HL : Nat.lxor 0 0 = 0%nat) by (vm_compute; reflexivity).
    cbn [pow2 q_sum]. rewrite HL. ring.
  - assert (Hpos := pow2_pos k).
    assert (Hsplit : pow2 (S k) = (pow2 k + pow2 k)%nat) by (cbn [pow2]; lia).
    assert (Hm2 : (m < 2 * pow2 k)%nat) by (cbn [pow2] in Hm; lia).
    rewrite Hsplit.
    rewrite (q_sum_split (fun n => F (Nat.lxor n m)) (pow2 k) (pow2 k)).
    rewrite (q_sum_split F (pow2 k) (pow2 k)).
    cbn beta.
    destruct (Nat.lt_ge_cases m (pow2 k)) as [Hmlt | Hmge].
    + (* m's leading bit is 0: low half permuted, high half shifted *)
      rewrite (IH m F Hmlt).
      assert (Hs2 : q_sum (fun i => F (Nat.lxor (pow2 k + i) m)) (pow2 k)
                    == q_sum (fun i => F (pow2 k + i)%nat) (pow2 k)).
      { transitivity (q_sum (fun i => (fun x => F (pow2 k + x)%nat) (Nat.lxor i m)) (pow2 k)).
        - apply q_sum_ext_bounded. intros i Hi. cbn beta.
          rewrite (lxor_hi_lo k i m Hi Hmlt). reflexivity.
        - exact (IH m (fun x => F (pow2 k + x)%nat) Hmlt). }
      rewrite Hs2. reflexivity.
    + (* m's leading bit is 1: halves swapped *)
      set (m0 := (m - pow2 k)%nat).
      assert (Hm0lt : (m0 < pow2 k)%nat) by (unfold m0; lia).
      assert (Hmeq : m = (pow2 k + m0)%nat) by (unfold m0; lia).
      assert (Hs1 : q_sum (fun n => F (Nat.lxor n m)) (pow2 k)
                    == q_sum (fun i => F (pow2 k + i)%nat) (pow2 k)).
      { transitivity (q_sum (fun n => (fun x => F (pow2 k + x)%nat) (Nat.lxor n m0)) (pow2 k)).
        - apply q_sum_ext_bounded. intros n Hn. cbn beta.
          rewrite Hmeq, (Nat.lxor_comm n (pow2 k + m0)),
                  (lxor_hi_lo k m0 n Hm0lt Hn), (Nat.lxor_comm m0 n). reflexivity.
        - exact (IH m0 (fun x => F (pow2 k + x)%nat) Hm0lt). }
      assert (Hs2 : q_sum (fun i => F (Nat.lxor (pow2 k + i) m)) (pow2 k)
                    == q_sum F (pow2 k)).
      { transitivity (q_sum (fun i => F (Nat.lxor i m0)) (pow2 k)).
        - apply q_sum_ext_bounded. intros i Hi. cbn beta.
          rewrite Hmeq, (lxor_hi_hi k i m0 Hi Hm0lt). reflexivity.
        - exact (IH m0 F Hm0lt). }
      rewrite Hs1, Hs2. lra.
Qed.

(* ===================================================================== *)
(*  Reindexing lemma: Σ_n had(i,n)·g(n⊕m) = had(i,m)·Σ_n had(i,n)·g(n)     *)
(* ===================================================================== *)

Lemma inner_reindex : forall k i m g, (i < pow2 k)%nat -> (m < pow2 k)%nat ->
  q_sum (fun n => had k i n * g (Nat.lxor n m)) (pow2 k)
  == had k i m * q_sum (fun n => had k i n * g n) (pow2 k).
Proof.
  intros k i m g Hi Hm.
  transitivity (q_sum (fun n => (fun p => had k i (Nat.lxor p m) * g p) (Nat.lxor n m)) (pow2 k)).
  { apply q_sum_ext. intro n. cbn beta.
    rewrite Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_r. reflexivity. }
  rewrite (xor_perm_q_sum k m (fun p => had k i (Nat.lxor p m) * g p) Hm).
  transitivity (q_sum (fun p => had k i m * (had k i p * g p)) (pow2 k)).
  { apply q_sum_ext_bounded. intros p Hp.
    rewrite (had_character k i p m Hi Hp Hm). ring. }
  apply q_sum_scale.
Qed.

(* ===================================================================== *)
(*  THE GENERAL WALSH CONVOLUTION THEOREM: H(f ⊛ g) = (Hf)·(Hg)            *)
(* ===================================================================== *)

Theorem walsh_convolution : forall k f g i, (i < pow2 k)%nat ->
  op_apply (had k) (dconv f g (pow2 k)) (pow2 k) i
  == op_apply (had k) f (pow2 k) i * op_apply (had k) g (pow2 k) i.
Proof.
  intros k f g i Hi. unfold op_apply, dconv. cbn beta.
  transitivity (q_sum (fun n => q_sum (fun m => had k i n * (f m * g (Nat.lxor n m))) (pow2 k))
                      (pow2 k)).
  { apply q_sum_ext. intro n. symmetry. apply q_sum_scale. }
  transitivity (q_sum (fun m => q_sum (fun n => had k i n * (f m * g (Nat.lxor n m))) (pow2 k))
                      (pow2 k)).
  { apply (q_sum_swap (fun n m => had k i n * (f m * g (Nat.lxor n m))) (pow2 k) (pow2 k)). }
  transitivity (q_sum (fun m => f m * q_sum (fun n => had k i n * g (Nat.lxor n m)) (pow2 k))
                      (pow2 k)).
  { apply q_sum_ext. intro m.
    rewrite <- (q_sum_scale (f m) (fun n => had k i n * g (Nat.lxor n m)) (pow2 k)).
    apply q_sum_ext. intro n. ring. }
  transitivity (q_sum (fun m => f m * (had k i m * q_sum (fun n => had k i n * g n) (pow2 k)))
                      (pow2 k)).
  { apply q_sum_ext_bounded. intros m Hm. rewrite (inner_reindex k i m g Hi Hm). reflexivity. }
  transitivity (q_sum (fun n => had k i n * g n) (pow2 k)
                * q_sum (fun m => had k i m * f m) (pow2 k)).
  { rewrite <- (q_sum_scale (q_sum (fun n => had k i n * g n) (pow2 k))
                            (fun m => had k i m * f m) (pow2 k)).
    apply q_sum_ext. intro m. ring. }
  ring.
Qed.

Print Assumptions walsh_convolution.
