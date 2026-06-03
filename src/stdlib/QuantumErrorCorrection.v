(** * QuantumErrorCorrection.v — the 3-qubit bit-flip code: continuum information protected
      by Element-side (finite, decidable bit) combinatorics.  The syndrome-extract /
      decode / recover logic is pure bit arithmetic; the protected amplitudes live in the
      continuum (the equal-superposition |+⟩_L names 1/√2).  Gottesman–Knill at the level
      of codes: error correction against bit-flips is classically tractable = Element.

    Elements: the bit words (b₁,b₂,b₃); the syndromes (bool,bool); the decoder; the
              syndrome table I→(F,F), X₁→(T,F), X₂→(T,T), X₃→(F,T) (L1 + P4)
    Roles:    Element side = the entire correction logic (syndrome, decode, recover) is
              finite decidable bit combinatorics; the four single errors {I,X₁,X₂,X₃} have
              four DISTINCT syndromes (correctable); role-limit = the protected amplitude
              (the equal superposition |+⟩_L has 1/√2 amplitudes, irrational)
    Rules:    codewords 000,111 (Hamming distance 3); the stabilizer syndrome
              σ(w)=(w₁⊕w₂,w₂⊕w₃) (independent of the logical bit); decode + XOR recovery;
              distance 3 ⟹ corrects 1 error

    THE DEEP POINT — QEC is continuum information protected by Element combinatorics.  The
    syndrome σ(w) = (w₁⊕w₂, w₂⊕w₃) is the stabilizer measurement; it depends ONLY on the
    error, not the logical bit (`syndrome_indep_of_logical`) — so it reveals the error
    without collapsing the protected superposition.  The four single-qubit errors have four
    distinct syndromes (`single_syndromes_distinct`), and a decoder recovers each error
    from its syndrome (`decode_corrects_single`); applying the decoded flip recovers the
    codeword (`correction_recovers`).  The codewords 000, 111 are at Hamming distance 3
    (`codeword_distance_3`), so 1 error is correctable.  ALL of this is finite, decidable
    BIT arithmetic — Element side.  But the protected state α|000⟩+β|111⟩ lives in the
    continuum: the equal-superposition |+⟩_L has amplitudes 1/√2, irrational
    (`logical_plus_role_limit`).  Element = the syndrome machinery; role-limit = the
    protected amplitude.  This is why QEC is efficiently computable (Gottesman–Knill): the
    correction never touches the continuum amplitudes, only the finite syndrome.

    ============ E/R/R разбор ============
      Rules (L5): кодовые слова 000,111 (расстояние 3); синдром σ(w)=(w₁⊕w₂,w₂⊕w₃) (не зависит
                  от логич. бита); декодер + XOR-восстановление; расстояние 3 ⟹ исправляет 1 ошибку.
      Roles (L4): Element = вся логика исправления (синдром, декод, восстановление) = конечная битовая
                  комбинаторика; 4 одиночные ошибки → 4 РАЗЛИЧНЫХ синдрома (корректируемость); role-limit
                  = защищаемая амплитуда (|+⟩_L имеет 1/√2).
      Elements  : битовые слова; синдромы; декодер; таблица I→(F,F),X₁→(T,F),X₂→(T,T),X₃→(F,T) (L1+P4).
    ДИАГНОСТИКА (P4): QEC = континуум-информация, защищаемая Element-комбинаторикой; синдром конечен/разрешим,
    не касается амплитуд (стабилизатор не коллапсирует логику) ⟹ QEC классически трактуем (Gottesman–Knill).
    Граница: Element-синдром / континуум-амплитуда (1/√2 = role-limit).

    STATUS: 8 Qed, 0 Admitted, 0 axioms
    Author: Horsocrates | Date: June 2026
*)

From Stdlib Require Import Bool QArith Lia.
From ToS Require Import analysis.Sqrt2Irrational.

(* ===================================================================== *)
(*  The 3-qubit bit-flip code: words, codewords, errors                   *)
(* ===================================================================== *)

Definition word : Type := (bool * bool * bool).

Definition c0 : word := (false, false, false).   (* logical |0⟩ = |000⟩ *)
Definition c1 : word := (true, true, true).       (* logical |1⟩ = |111⟩ *)

Definition errX1 : word := (true, false, false).  (* bit-flip on qubit 1 *)
Definition errX2 : word := (false, true, false).
Definition errX3 : word := (false, false, true).

(** Bitwise XOR: an error acts on a word by flipping the indicated bits. *)
Definition xor3 (u v : word) : word :=
  let '(a, b, c) := u in let '(x, y, z) := v in (xorb a x, xorb b y, xorb c z).

(** The stabilizer syndrome: the two parity checks Z₁Z₂, Z₂Z₃. *)
Definition syndrome (w : word) : bool * bool :=
  let '(a, b, c) := w in (xorb a b, xorb b c).

(** The decoder: recover the single-qubit error from its syndrome. *)
Definition decode (s : bool * bool) : word :=
  match s with
  | (false, false) => (false, false, false)   (* no error *)
  | (true, false)  => (true, false, false)    (* X₁ *)
  | (true, true)   => (false, true, false)    (* X₂ *)
  | (false, true)  => (false, false, true)    (* X₃ *)
  end.

(* ===================================================================== *)
(*  The codewords are in the code (syndrome 0)                            *)
(* ===================================================================== *)

(** Both codewords have zero syndrome — they are valid codewords. *)
Lemma codewords_in_code : syndrome c0 = (false, false) /\ syndrome c1 = (false, false).
Proof. split; reflexivity. Qed.

(** ★ The syndrome depends ONLY on the error, not the logical bit: σ(c₀⊕e)=σ(c₁⊕e).  So
    the stabilizer measurement reveals the error without collapsing the protected
    superposition. *)
Lemma syndrome_indep_of_logical : forall e : word,
  syndrome (xor3 c0 e) = syndrome (xor3 c1 e).
Proof. intros [[a b] c]. destruct a, b, c; reflexivity. Qed.

(* ===================================================================== *)
(*  Correctability: four single errors, four distinct syndromes           *)
(* ===================================================================== *)

(** ★ The decoder recovers each single-qubit error from its syndrome. *)
Lemma decode_corrects_single :
  decode (syndrome errX1) = errX1
  /\ decode (syndrome errX2) = errX2
  /\ decode (syndrome errX3) = errX3.
Proof. repeat split; reflexivity. Qed.

(** ★ The four single errors {I,X₁,X₂,X₃} have four pairwise-DISTINCT syndromes — so they
    are distinguishable, hence correctable. *)
Lemma single_syndromes_distinct :
  syndrome c0 <> syndrome errX1 /\ syndrome c0 <> syndrome errX2
  /\ syndrome c0 <> syndrome errX3 /\ syndrome errX1 <> syndrome errX2
  /\ syndrome errX1 <> syndrome errX3 /\ syndrome errX2 <> syndrome errX3.
Proof. repeat split; discriminate. Qed.

(** ★ Applying the decoded error-flip to the corrupted word recovers the codeword. *)
Lemma correction_recovers :
  xor3 (decode (syndrome (xor3 c0 errX1))) (xor3 c0 errX1) = c0
  /\ xor3 (decode (syndrome (xor3 c0 errX2))) (xor3 c0 errX2) = c0
  /\ xor3 (decode (syndrome (xor3 c0 errX3))) (xor3 c0 errX3) = c0.
Proof. repeat split; reflexivity. Qed.

(** The two codewords are at Hamming distance 3 (all three bits differ) — so the code has
    distance 3 and corrects ⌊(3−1)/2⌋ = 1 error. *)
Lemma codeword_distance_3 :
  fst (fst c0) <> fst (fst c1) /\ snd (fst c0) <> snd (fst c1) /\ snd c0 <> snd c1.
Proof. repeat split; discriminate. Qed.

(* ===================================================================== *)
(*  Role-limit: the protected amplitude (the |+⟩_L state) names 1/√2       *)
(* ===================================================================== *)

Open Scope Q_scope.

(** ★ The protected state α|000⟩+β|111⟩ lives in the continuum: the equal superposition
    |+⟩_L has amplitudes 1/√2, irrational (no rational squares to 1/2).  Element = the
    syndrome machinery above; role-limit = this protected amplitude. *)
Theorem logical_plus_role_limit : ~ (exists r : Q, r * r == 1 # 2).
Proof.
  intros [r Hr]. apply sqrt2_not_in_Q. exists (2 * r).
  assert (H : (2 * r) * (2 * r) == 4 * (r * r)) by ring.
  rewrite H, Hr. vm_compute. reflexivity.
Qed.

(* ===================================================================== *)
(*  Synthesis                                                             *)
(* ===================================================================== *)

(** The 3-qubit code, split by the finitization boundary:
      (a) the syndrome is independent of the logical bit (reveals error, not logic);
      (b) the decoder recovers each single error (correctable);
      (c) the four single errors have distinct syndromes (distinguishable);
      (d) the codewords are at Hamming distance 3;
      (e) ROLE-LIMIT — the protected |+⟩_L amplitude 1/√2 is irrational.
    Element = the finite bit syndrome/decode/recover; role-limit = the continuum amplitude. *)
Theorem qec_synthesis :
  (forall e : word, syndrome (xor3 c0 e) = syndrome (xor3 c1 e))
  /\ (decode (syndrome errX1) = errX1 /\ decode (syndrome errX2) = errX2
      /\ decode (syndrome errX3) = errX3)
  /\ (syndrome c0 <> syndrome errX1 /\ syndrome errX1 <> syndrome errX2)
  /\ (fst (fst c0) <> fst (fst c1) /\ snd c0 <> snd c1)
  /\ ~ (exists r : Q, r * r == 1 # 2).
Proof.
  split; [ exact syndrome_indep_of_logical | ].
  split; [ exact decode_corrects_single | ].
  split; [ split; discriminate | ].
  split; [ split; discriminate | ].
  exact logical_plus_role_limit.
Qed.
