---
title: "Chapter 3. Deriving the Laws of Logic from Distinction"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/01 Перво-различие и законы логики/03 Вывод законов логики из Distinction.md"
sourceBlob: 641929e42e95d3c42b3892d3c72611435fffe742
translated: 2026-10-20
status: draft
---

## From Structure to Theorems: Statement of the Problem

### What Was Established in Chapter 2

Chapter 2 introduced the record `Distinction` with four fields: the positive side, the negative side, mutual exclusion, and joint exhaustiveness. These four fields, as was shown in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#The Structure of the Act of Distinction|§ 2.2 “The Structure of the Act of Distinction”]], correspond to the four moments of the act of distinction analyzed in substance. The minimality of the record ([[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Minimality of the Record: Can One of the Four Fields Be Removed?|§ 2.6 “Minimality of the Record: Can One of the Four Fields Be Removed?”]]) guarantees that each field carries its own work and that none can be removed without losing the very structure of distinction.

At the close of Chapter 2, in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Preparation for Chapter 3 and Beyond|§ 2.6.7 “Preparation for Chapter 3 and Beyond”]], a correspondence was indicated to which Chapter 3 now turns systematically:

- The Law of Identity $L1$ rests on the fields `positive` and `negative` (the self-identity of the sides).
- The Law of Non-Contradiction $L2$ rests on the field `exclusive`.
- The Law of Excluded Middle $L3$ rests on the field `exhaustive`.
- The Law of Sufficient Reason $L4$ rests on the very structure of the record as a whole—through the requirement of justifications for all the fields.

This correspondence is not a rhetorical observation. In the present chapter each of the listed statements will be *formally proved* by the means of Rocq. The technical support is the file `LawsFromDistinction.v` of the ToS-Coq repository.

### The Laws of Logic and Their Derivation as Theorems

**The ontological primacy of the laws of logic.**  First of all, it is important to fix the ontological status of the laws of logic. According to [[Metaphysics|“Metaphysics”]] and the position fixed in the Methodological Introduction, the laws $L1$, $L2$, $L3$, $L4$, $L5$ are *ontologically primary*. They do not *follow* from anything more primary; they are the very structure of the work of Logic on $A = \exists$, the conditions of the very possibility of the existence of anything determinate. Without them there would be no acts of distinction, no record `Distinction`, and no formal system whatsoever. This is a fact of ontology, not a consequence of mathematical work.

**What “derivation as a theorem” means.**  Nevertheless, within the *formal system* Rocq, the laws of logic can be *derived as theorems*—that is, represented as provable statements about the properties of the record `Distinction`. This is not an ontological claim but a *methodological step* within the formal system: having the record `Distinction`, we formulate a law of logic as a statement about its properties and present a proof of this statement by the means of Rocq.

The difference is important. When we say that the law $L1$ “is derived as a theorem about `Distinction`,” we do *not* assert that in reality the law of identity arises from the act of distinction or depends on it. We assert something else: in the formal record in the language of Rocq there is a structural correspondence between the fields of `Distinction` and the laws of logic, and this correspondence can be fixed as a statement provable in Rocq.

**What this gives.**  This formal result has essential methodological significance without canceling the ontological primacy of the laws. In the formal system we obtain an explicit *structural expression* of how the laws of logic work at the very first level accessible to formalization—the level of the act of distinction. The fields of `Distinction` do not *bring the laws into being*; they *manifest* their work in the simplest recordable form. If in reality the laws of logic work wherever there is determinacy of existence, then the record `Distinction` is the formal object on which this work becomes *traceable step by step* in the formal system.

According to the position fixed in the Methodological Introduction—mathematics as a language for describing the logical structure of reality—the formal theorems of Chapter 3 *describe* how the laws of logic manifest themselves in the simplest formalizable structure. They do not *create* the laws, do not *postulate* them, do not *derive* them from anything more primary. They only make visible the structure of the work of Logic that in reality is always at work.

**Double numbering at work.**  The Methodological Introduction already fixed the double numbering of the laws: ontological (“Metaphysics”) and formal (Rocq). *Ontologically*, Sufficient Reason works as a meta-law over all the others; Identity and Non-Contradiction are primary as structural conditions; the Law of Excluded Middle is ontologically *derived* from them; the Law of Order is a structural condition of hierarchy. *Formally*, in Rocq all five laws are represented by self-standing theorems: $L3$ rests on the axiom `classic`, $L5$ on the separate type `Level`. This duality is not a contradiction but two levels of one work: ontological status and formal proof.

### The Technical Source of the Derivation

The technical basis of the present chapter is the file `LawsFromDistinction.v` (directory `src/foundation/`) of the ToS-Coq repository. The file imports two dependencies:

```coq
From ToS Require Import foundation.Distinction.
From ToS Require Import TheoryOfSystems_Core_ERR.
```

The first import is the record `Distinction` and the related constructions (including `distinction_of`) analyzed in Chapter 2. The second is the file containing the type `Level` and the order structures connected with it (the formalization of $L5$).

The file contains *twenty-two theorems* that implement the formal representation of all five laws and their combinations; this number is fixed in the file itself by the definition `laws_theorem_count`. The laws are represented by *unequal* numbers of forms: the number of forms of each law corresponds to its formal status.

- $L1$ and $L2$ have three forms: the general form (in the standard logical formulation for an arbitrary proposition, for example `Law_of_Identity : forall A, A = A`), the structural form (as a statement about an arbitrary `Distinction`, for example `L1_through_distinction`), and the canonical form (applied to the canonical distinction `distinction_of` $(P)$).
- $L3$ has three forms: the general form through the axiom `classic`, the structural form through the field `exhaustive`, and the equivalence theorem `L3_independence`.
- $L4$ has four forms: self-grounding, contraposition, canonical double negation, and classical double-negation elimination.
- $L5$ is placed in a separate apparatus of the type `Level` and is represented by its own set of theorems about the order of levels.

Such an *unequal* distribution of forms is not accidental: it reflects the difference in the formal status of the laws—$L1$ and $L2$ are constructive and read directly from the record, $L3$ requires a classical axiom, $L4$ has several working sides, and $L5$ rests on a separate layer of formalization. The chapter analyzes each law in the number of forms in which it is actually represented in the file.

Let us pass to the first law—the Law of Identity—and to its formal representation as a theorem about `Distinction`.

## The Law of Identity ($L1$)

### Formulation

The Law of Identity is the statement that something is identical to itself. Ontologically, it is *a structural condition of determinacy itself*: without identity the positive side of a distinction could not be a *determinate* side and would merge into the indistinguishable (see [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#The Positive Side: What “Is” Means in Distinction|§ 2.2.2 “The Positive Side: What “Is” Means in Distinction”]] of Chapter 2). The law is neither *introduced* by us nor *derived* from anything more primary—it is a condition of the very possibility of the existence of anything determinate.

In the formal system Rocq, the law is represented by a statement about an arbitrary proposition:

$$
\forall A : \mathbf{Prop},\quad A = A.
$$

In terms of the act of distinction: the positive side is identical to itself; the negative side is identical to itself.

### Three Forms of the Theorem

The file `LawsFromDistinction.v` represents $L1$ in three forms, corresponding to three levels of work: general propositions, the structure `Distinction`, and the canonical distinction.

**The general form: `Law_of_Identity`.**  The simplest formulation, for an arbitrary proposition:

```coq
Theorem Law_of_Identity : forall (A : Prop), A = A.
Proof. reflexivity. Qed.
```

The proof consists of a single tactic, `reflexivity`—a tactic built into Rocq that closes goals of the form $x = x$ by direct reference to the rule of type equality (reflexivity). This means that the statement is *computably* recognized by the system as trivially true—without appeal to any axioms, without any substantive work.

**Through the structure of distinction: `L1_through_distinction`.**  The law expressed as a statement about an arbitrary act of distinction:

```coq
Theorem L1_through_distinction : forall D : Distinction,
  positive D = positive D /\ negative D = negative D.
Proof. intro D; split; reflexivity. Qed.
```

Here it is asserted that both sides of an arbitrary act of distinction—the positive and the negative—are identical to themselves. The proof: take an arbitrary $D$, split the conjunction into two goals, and close each with the tactic `reflexivity`. Again: not a single axiom, not a single substantive step.

**The canonical form: `L1_distinction_preserves`.**  The law applied to the canonical distinction built from an arbitrary proposition:

```coq
Theorem L1_distinction_preserves : forall P : Prop,
  positive (distinction_of P) = P.
Proof. reflexivity. Qed.
```

Here it is asserted that the positive side of the canonical distinction built from $P$ is $P$ itself. This is the formal fixing of the fact that the construction `distinction_of` $(P)$, analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#The Construction distinction_of: Building a Distinction from a Proposition|§ 2.5 “The Construction distinction_of: Building a Distinction from a Proposition”]] of Chapter 2, *preserves* the content of the original proposition in the positive side—which is a direct expression of $L1$: $P$ remains $P$, without turning into anything else.

### The Triviality of the Proofs

All three proofs are one or two tactics, with no appeal to axioms. This does *not* mean that the law of identity is “too simple” or that its formal derivation shows nothing. The triviality of the proofs is a sign that the *record* `Distinction` already carries within itself all the information necessary for $L1$.

Concretely: the fields `positive` and `negative` have type `Prop` (see [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Why Prop and Not bool: The Position of Logical Realism|§ 2.4 “Why Prop and Not bool: The Position of Logical Realism”]]); propositions in CIC automatically satisfy the reflexivity of type equality; `positive` and `negative`, as sides of an act of distinction, are *by definition* determinate propositions, not indistinct ones. The proof of $L1$ does not *add* anything to this arrangement—it only *fixes* it as a theorem.

In this sense the triviality of the proof is *methodological evidence*: $L1$ corresponds so directly to the structure of the fields `positive` and `negative` that there are no additional steps between the structure and the law. The Law of Identity is *already built* into the very typing of the record.

### Substantive Meaning

In keeping with the fixed position—mathematics as a language for describing the logical structure of reality—these formal theorems describe a concrete aspect of the work of Logic in what really exists.

In reality, every determinacy presupposes the identity of what is determined. If a concrete physical system has a definite state, this state *is this state* and not another. If the mathematical statement “the function $f$ is continuous at the point $x_0$” has meaning, then this statement itself is identical to itself in any context where it is used—otherwise the very notion of “asserting” would lose its meaning. If a chemical molecule has a $C_3$ symmetry axis, then it is precisely $C_3$, not $C_2$ or $C_4$.

The $L1$ theorems in Rocq do not create this structural fact of reality. They give it a *formal record* in the terms of the record: the positive side is identical to itself (`L1_through_distinction`); the construction of the canonical distinction preserves the original proposition (`L1_distinction_preserves`). These theorems are not statements about reality itself but properties of the *formal object* `Distinction`, which agrees with reality because the record is built as a formalization of the real structure of the act of distinction.

With $L1$ it has been established that the positive and the negative sides of a distinction preserve their identity. The next law, $L2$, concerns their *relation*: the impossibility of their coinciding at once.

## The Law of Non-Contradiction ($L2$)

### Formulation

The Law of Non-Contradiction is the statement that something cannot be itself and not itself at once in one respect. Ontologically, it is *a structural condition of the very possibility of division*: without the mutual exclusion of the positive and the negative sides, the division itself would fall apart, since the “positive” and the “negative” sides would merge into one (see [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Mutual Exclusion: What Is Impossible in One Respect|§ 2.2.4 “Mutual Exclusion: What Is Impossible in One Respect”]] of Chapter 2). Like $L1$, $L2$ is not a consequence of mathematical work but a condition of the very possibility of the existence of anything determinate.

In the formal system Rocq, the law is represented by a statement about an arbitrary proposition:

$$
\forall A : \mathbf{Prop},\quad \neg(A \wedge \neg A).
$$

In terms of the act of distinction: the positive and the negative sides cannot hold at once.

### Three Forms of the Theorem

The file `LawsFromDistinction.v` represents $L2$ in three forms, parallel to the forms of $L1$ (“The Law of Identity ($L1$)”).

**The general form: `Law_of_NonContradiction`.**  For an arbitrary proposition:

```coq
Theorem Law_of_NonContradiction : forall (A : Prop), ~(A /\ ~A).
Proof. intros A [Ha Hna]. exact (Hna Ha). Qed.
```

The proof contains three tactics:

- `intros A [Ha Hna]`—the introduction of the parameter $A$ and the decomposition of the hypothesis $A \wedge \neg A$ into its components: `Ha : A` (a proof of $A$) and `Hna : ~ A` (a proof of $\neg A$).
- `exact (Hna Ha)`—the application of `Hna` (of type $A \to \mathtt{False}$) to `Ha` (of type $A$), which gives an element of type `False`—the contradiction that was to be obtained.
- `Qed`—the completion of the proof.

Unlike $L1$, here there *is* substantive work: we use the functional nature of negation ($\neg A = A \to \mathtt{False}$) to obtain a contradiction. But this work is *constructive*: it requires no appeal to any axioms. $L2$ is provable by the means of CIC itself, without extensions.

**Through the structure of distinction: `L2_from_distinction`.**  The law expressed as a statement about an arbitrary `Distinction`:

```coq
Theorem L2_from_distinction : forall D : Distinction,
  ~(positive D /\ negative D).
Proof. exact L2_exclusivity. Qed.
```

The proof is one line: `exact L2_exclusivity`, where `L2_exclusivity` is an auxiliary lemma[^1] expressing the work of the field `exclusive` as a statement about an arbitrary `Distinction`. The field `exclusive D` itself has the type $\neg(\texttt{positive} D \wedge \texttt{negative} D)$, that is, it *is* a direct proof of the required statement for a concrete $D$; the lemma `L2_exclusivity` merely generalizes this to a statement about *any* $D$.

This is a characteristic feature of work with records in Rocq, discussed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Over Everything: The Work of Sufficient Reason|§ 2.2.6 “Over Everything: The Work of Sufficient Reason”]] of Chapter 2: the fields of a record are *by themselves* proofs of the corresponding statements. The $L2$ theorem through the structure of distinction is merely the formal registration of the fact that the proof already exists, built into the record itself.

**The canonical form: `L2_canonical`.**  The law for an arbitrary proposition, repeating the content of the general form, but in terms of the canonical distinction:

```coq
Theorem L2_canonical : forall P : Prop, ~(P /\ ~P).
Proof. intros P [Hp Hnp]. exact (Hnp Hp). Qed.
```

The proof repeats the general form word for word—`L2_canonical` and `Law_of_NonContradiction` are identical in content. The difference lies only in the position in the file and in the name. Here it is important to clarify in what sense this form is *canonical*: the theorem is so called *not* because it syntactically contains `distinction_of`—it works with an arbitrary proposition $P$ directly—but because it concerns the canonical pair $P  /  \neg P$, which underlies the construction `distinction_of` $(P)$. Canonicity here is by subject matter (the canonical pair), not by the syntax of the entry.

### The Field `exclusive` as a Built-In Proof

The essential difference between $L2$ and $L1$ in formal structure is as follows. For $L1$ the proof is trivial, since the reflexivity of type equality is built into CIC itself. For $L2$, however, the proof rests on a concrete *field* of the record—`exclusive`. Without this field the law $L2$ *would not follow* from the record `Distinction`; it would have to be postulated separately or proved in a complicated way.

This agrees with the minimality of the record analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Minimality of the Record: Can One of the Four Fields Be Removed?|§ 2.6 “Minimality of the Record: Can One of the Four Fields Be Removed?”]] of Chapter 2: it was shown that without the field `exclusive` the record loses the status of a *distinction*, since the positive and the negative sides can coincide. Chapter 3 gives a formal correlate of this observation: without the field `exclusive`, the theorem `L2_from_distinction` *could not be proved*.

Thus the field `exclusive` plays a double role: in substance it fixes the mutual exclusion of the sides of the act of distinction; formally it is a built-in proof of $L2$ for every `Distinction`.

### Substantive Meaning

In keeping with the fixed position—mathematics as a language for describing the logical structure of reality—the $L2$ theorems describe a concrete aspect of the work of Logic in what really exists.

In reality, the simultaneous presence and absence of one and the same feature *in one respect* is impossible. A molecule cannot at once have and not have a $C_3$ symmetry axis (in one respect, relative to a concrete geometry and axis). An electron cannot at once be and not be in a given quantum state (for a given system of measurements). The statement “the function $f$ is continuous at the point $x_0$” cannot at once be true and false (for a given $f$ and a given $x_0$).

The qualification “in one respect” is key, and it was already analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Mutual Exclusion: What Is Impossible in One Respect|§ 2.2.4 “Mutual Exclusion: What Is Impossible in One Respect”]] of Chapter 2, with reference to Aristotle’s formulation in *Metaphysics* IV.3. The same object (for example, a chemical substance) can have *one* symmetry in one respect and lack *another* in another respect; there is no contradiction here. The Law of Non-Contradiction excludes only the simultaneous presence and absence of *one and the same* feature *in one and the same respect*.

The $L2$ theorems in Rocq do not create this structural fact of reality. They give it a formal record through the field `exclusive`: within an arbitrary act of distinction, the positive and the negative sides cannot hold at once. This formal record agrees with reality because the record `Distinction` is built as a formalization of the real structure of the act of distinction.

With $L1$ and $L2$, the identity of the sides and the impossibility of their coinciding at once have been established. The next law, $L3$, concerns the *completeness* of the division: the absence of a third between the sides.

## The Law of Excluded Middle ($L3$)

### The Double Status of the Law

The Law of Excluded Middle occupies a special place among the laws of logic. Ontologically, it is the condition of the *completeness of division*: in every act of distinction in which the identity of the sides ($L1$) and their exclusivity ($L2$) are already at work, no room remains for a “third”—something that would be neither the positive nor the negative side. This is a consequence of the joint work of the first two laws at the structural level: if there is identity and there is exclusivity, then there is no longer any space between the sides for anything else.

*Ontologically*, then, $L3$ is a *derived* law, deduced from the joint work of $L1$ and $L2$. This derivation is fixed in “Metaphysics” and briefly recalled in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Joint Exhaustiveness: That There Is No Third between the Sides|§ 2.2.5 “Joint Exhaustiveness: That There Is No Third between the Sides”]] of Chapter 2: if something determinately *is* (Identity) and cannot at once be and not be (Non-Contradiction), then the very structure of distinction leaves no room for a third. This is a structural consequence, not a self-standing condition.

A caveat is needed here, to avoid misunderstanding. What has been said is *not* a claim that $L3$ is *formally derived* from $L1$ and $L2$ in intuitionistic logic. Within CIC such a derivation is impossible: intuitionistic logic accepts both the reflexivity of equality and non-contradiction but does *not* prove $P \vee \neg P$ for an arbitrary proposition $P$. What is at issue is an *ontological* thesis of ToS: a complete act of distinction leaves no third region between the positive and the negative sides. This is a thesis about the structure of distinction, not a theorem of a formal calculus. Formally, this completeness is fixed through the axiom `classic`—precisely because the ontological thesis has no constructive formal counterpart.

*Formally*, however, in Rocq $L3$ as a statement *for an arbitrary proposition*, $\forall P : \mathbf{Prop},\;
P \vee \neg P$, is *not derivable* constructively. The reason was discussed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Joint Exhaustiveness: That There Is No Third between the Sides|§ 2.2.5 “Joint Exhaustiveness: That There Is No Third between the Sides”]] of Chapter 2: to prove a disjunction constructively for an arbitrary $P$, one must *present* a concrete path—a proof of $P$ or a proof of $\neg P$. But without knowing the content of $P$, an algorithm for such a presentation is impossible. Therefore in CIC the law is fixed as the *axiom* `classic`.

Herein lies the double status of $L3$: ontologically derived (from $L1$ and $L2$ in the structure of distinction), formally self-standing (since CIC does not reproduce the ontological derivation). This duality is not a contradiction but a manifestation of the difference between the ontological structure of Logic and the technical capabilities of a concrete formal system.

### Formulation

In the formal system Rocq, the law is represented by a statement about an arbitrary proposition:

$$
\forall A : \mathbf{Prop},\quad A \vee \neg A.
$$

In terms of the act of distinction: for an arbitrary $D : \texttt{Distinction}$, $\texttt{positive} D \vee \texttt{negative} D$ holds.

### The Axiom `classic` and Its Role

In the file `Distinction.v`, and through it in `LawsFromDistinction.v`, the following axiom is postulated:

```coq
Axiom classic : forall P : Prop, P \/ ~ P.
```

This axiom is one of the two fundamental axioms of the ToS-Coq repository (the second is `L4_witness`, discussed in the later chapter on the axiomatic layer). It asserts that for every proposition $P$, $P \vee \neg P$ holds.

**A comment of principle from the repository.**  In the source code of the file `LawsFromDistinction.v`, a comment is attached to this axiom that deserves to be quoted explicitly:

> L3 is not an EXTRA axiom: it IS our formalization of “distinction is
> exhaustive”. classic = L3.

This statement calls for clarification—and for precision. Technically, `classic` *is* an axiomatic extension of the constructive basis of CIC: in the pure Calculus of Inductive Constructions the statement $\forall P,\ P \vee \neg P$ is not provable, and `classic` is added to the system as a classical principle. This technical fact should not be denied. But the quoted comment speaks of something else—not of the technical status of `classic` in CIC but of its place *within* ToS. And here `classic` is not an external, extraneous addition to the ontology: it is the *formal record* of the law $L3$—of one of the four moments of the act of distinction, joint exhaustiveness ([[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Joint Exhaustiveness: That There Is No Third between the Sides|§ 2.2.5 “Joint Exhaustiveness: That There Is No Third between the Sides”]] of Chapter 2). The field `exhaustive` in the record `Distinction` *is* a concrete manifestation of the same content: it postulates that for a concrete act of distinction $D$ one of the two sides necessarily holds. The axiom `classic` generalizes this to a statement about an arbitrary proposition.

Thus the two levels must be kept apart. At the level of *technique*, `classic` is an axiomatic extension of CIC. At the level of the *ontology* of ToS, `classic` is not *added* to the structure `Distinction` as something alien; it *expresses* in general form what is already built into the record itself through the field `exhaustive`. This is a formal correlate of the ontological position: joint exhaustiveness is a necessary moment of the act of distinction, without which the division itself would be incomplete.

**The ontological grounding of accepting the axiom.**  The acceptance of `classic` in ToS is grounded ontologically: according to “Metaphysics,” in reality there is *always* a determinate state of affairs—either something holds or it does not (in one respect). That we have no algorithm to establish, for each concrete proposition $P$, which state of affairs holds does not cancel the ontological fact: the state of affairs is determinate. Constructive undecidability is an epistemological limitation (the impossibility of always finding out); the axiom `classic` is the fixing of ontological determinacy (one of the two always holds).

### Formal Theorems

The file `LawsFromDistinction.v` represents $L3$ in three forms.

**The general form: `Law_of_ExcludedMiddle`.**  The law in the standard formulation for an arbitrary proposition:

```coq
Theorem Law_of_ExcludedMiddle : forall (A : Prop), A \/ ~A.
Proof. exact classic. Qed.
```

The proof is one line: `exact classic`. The theorem is a direct application of the axiom `classic` to an arbitrary proposition. This is the literal expression of what the comment quoted above formulates in words: `classic = L3`.

**Through the structure of distinction: `L3_from_distinction`.**  The law expressed as a statement about an arbitrary `Distinction`:

```coq
Theorem L3_from_distinction : forall D : Distinction,
  positive D \/ negative D.
Proof. exact L3_totality. Qed.
```

The proof rests on the auxiliary lemma `L3_totality`[^2], which expresses the work of the field `exhaustive` as a statement about an arbitrary `Distinction`. The field `exhaustive D` itself has the type $\texttt{positive} D \vee \texttt{negative} D$, that is, it *is* a direct proof of the required statement for a concrete $D$; the lemma `L3_totality` generalizes this to a statement about *any* $D$.

Unlike `Law_of_ExcludedMiddle`, `L3_from_distinction` *does not require* a direct appeal to the axiom `classic` in its proof—the field `exhaustive` is enough for it. However, the very existence of the field `exhaustive` with arbitrary contents in the record `Distinction` is provided, in the final analysis, by the same axiom: the universal construction `distinction_of` $(P)$ ([[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#The Construction distinction_of: Building a Distinction from a Proposition|§ 2.5 “The Construction distinction_of: Building a Distinction from a Proposition”]] of Chapter 2) rests on `classic` in building the field `exhaustive` for an arbitrary $P$. Thus `classic` works in `distinction_of`, while `L3_from_distinction` works with an already built `Distinction`.

**The equivalence of `classic` and $L3$-through-distinction:
`L3_independence`.**  The file contains one more theorem about $L3$, which completes the picture:

```coq
Theorem L3_independence :
  (forall D : Distinction, positive D \/ negative D)
  -> (forall P : Prop, P \/ ~ P).
Proof. intros _ P. exact (classic P). Qed.
```

It asserts that excluded middle for every act of distinction implies excluded middle for every proposition. Together with `L3_from_distinction`, which gives the converse direction, this shows that $L3$-through-distinction and `classic` are *equivalent in strength*—the same identity `classic` $=$ $L3$, now carried through in both directions. The name of the theorem, `L3_independence`, indicates its role: $L3$ does not *reduce* to the other laws; it carries its own content, exactly coinciding with the content of `classic`. It is worth stating precisely, however, what the theorem does *not* do: it does not prove—and cannot prove *within* Rocq—the metatheoretical thesis that constructive logic satisfies $L1, L2, L4,
L5$ but not $L3$ (this thesis is genuinely metatheoretical, for it speaks of a system *without* `classic`, whereas we work in a system *with* `classic`). The theorem fixes the internally accessible part: the exact coincidence of $L3$-through-distinction and `classic`.

### The Field `exhaustive` and the Connection with Minimality

The situation parallels the case of $L2$: for $L3$, the proof `L3_from_distinction` rests on a concrete *field* of the record—`exhaustive`. Without this field the law $L3$ *would not follow* from the record `Distinction`.

This again agrees with the minimality of the record analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Minimality of the Record: Can One of the Four Fields Be Removed?|§ 2.6 “Minimality of the Record: Can One of the Four Fields Be Removed?”]] of Chapter 2: it was shown that without the field `exhaustive` the record loses the status of a *complete* division, since a “third way” may turn up between the sides. Chapter 3 gives the formal correlate: without the field `exhaustive`, the theorem `L3_from_distinction` would not be provable; one would have to apply `classic` separately, for each concrete $D$, to the concrete $\texttt{positive} D$ and $\texttt{negative} D$, which contradicts the idea of the *structure* of distinction as a self-standing object.

Thus the fields `exclusive` and `exhaustive` play parallel roles: in substance they fix two sides of the completeness of division (exclusivity and exhaustiveness); formally they serve as built-in proofs of $L2$ and $L3$, respectively, for every `Distinction`.

### Substantive Meaning

In keeping with the fixed position—mathematics as a language for describing the logical structure of reality—the $L3$ theorems describe a concrete aspect of the work of Logic in what really exists.

In reality, every determinate state of affairs *is determinate*: either something holds or it does not. A molecule either has a $C_3$ symmetry axis or does not (in one respect, relative to a concrete geometry). An integer is either even or not. A statement is either true for a given situation or not. There is no third—no state “neither true nor false”—in the real ontology of determinate existence.

The qualification “in one respect,” discussed in connection with $L2$, applies here as well: one and the same object can be in different states with respect to different features or in different respects, and in each respect the law $L3$ works separately.

The $L3$ theorems in Rocq do not create this structural fact of reality. They give it a formal record through the field `exhaustive` and the axiom `classic`: within an arbitrary act of distinction, the positive or the negative side necessarily holds. The axiom `classic` does not *add* anything to the structure of the act of distinction—it only *expresses* in general form the fact that is already built into the record itself through the field `exhaustive`.

With $L1$, $L2$, and $L3$, the identity of the sides, the impossibility of their coinciding, and the absence of a third between them have been established. The next law, $L4$, turns to the *groundedness* of the act of distinction itself, and here the work goes beyond a single record `Distinction` to its properties as a structure.

## The Law of Sufficient Reason ($L4$)

### Ontological Status: A Meta-Law

The Law of Sufficient Reason occupies a special position in ToS among the five laws of logic, different from that of $L1$, $L2$, and $L3$.

Ontologically, according to “Metaphysics,” $L4$ is a *meta-law*. It does not work “alongside” Identity, Non-Contradiction, and Excluded Middle as one of several equal laws; it works *over* them, as the very action of Logic in which grounding becomes possible. $L1$, $L2$, $L3$ are structural conditions of determinacy; $L4$ is the meta-structure in which these conditions have force, since each of them is *grounded*.

Applied to the act of distinction, this means that each of the four moments of the act (the identity of the sides, exclusivity, exhaustiveness, the division itself) has a *ground*, and the act itself as a whole has a ground for taking place as it does and not otherwise ([[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Over Everything: The Work of Sufficient Reason|§ 2.2.6 “Over Everything: The Work of Sufficient Reason”]] of Chapter 2). Without the work of $L4$, the other laws would remain empty formal requirements, connected with no determinate real structure.

This meta-role of $L4$ is expressed in Rocq in two ways. On the one hand, it is *built into* the very type system of CIC: every definition requires grounding (these are the types), every theorem requires a proof (these are the proof terms), every construction must be checkable (this is the kernel of the system). This built-in character was discussed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Over Everything: The Work of Sufficient Reason|§ 2.2.6 “Over Everything: The Work of Sufficient Reason”]] of Chapter 2 as “the work of Sufficient Reason as an organizing principle of the formal system.”

On the other hand, Rocq also has a *concrete* formal expression of $L4$—as a *property* of the record `Distinction`. The present section is devoted to this expression.

### Formalization: Self-Grounding

In `LawsFromDistinction.v`, the law of Sufficient Reason is formalized through the statement of the *self-grounding* of the act of distinction. The content of this statement is as follows: for an arbitrary `Distinction` $D$, if the positive side holds, then the negative side does not hold.

In formal notation:

$$
\forall D : \texttt{Distinction},\quad
  \texttt{positive} D \;\to\; \neg \texttt{negative} D.
$$

**Why precisely this formulation.**  At first glance this entry may seem remote from the classical Sufficient Reason (“everything has a ground”). But the connection is substantive and deserves clarification.

The positive side $\texttt{positive} D$ is the *grounding* of the determinacy of the act of distinction—of the fact that the given act distinguishes precisely *this* and not something else. If the positive ground holds, then the opposite side *has no ground* for holding at the same time—otherwise the act would cease to be an act of distinction. The statement $\texttt{positive} D \to \neg \texttt{negative} D$ is thus an expression of the fact that *the presence of a ground* for one side *closes off* the ground for the opposite one. Self-grounding *is* the structural manifestation of Sufficient Reason at the level of the record: each field of `Distinction` is grounded not from outside but through its connection with the other fields.

**Connection with the field `exclusive`.**  Formally, the statement $\texttt{positive} D \to \neg \texttt{negative} D$ is derived from the field `exclusive`, which has the type $\neg(\texttt{positive} D \wedge \texttt{negative} D)$. These are equivalent forms: “not both at once” is equivalent to “if one, then not the other.” In substance, however, these forms express different aspects of one structure: `exclusive` is a symmetric statement of incompatibility; `L4_self_grounding` is a directed statement that the presence of one side excludes the other. Sufficient Reason works in both forms, but in self-grounding it shows itself as an *asymmetric* consequence, which corresponds to the ontological character of grounding.

### Four Forms of the Theorem

The file `LawsFromDistinction.v` represents $L4$ in four forms. The first two are symmetric applications of self-grounding to the two sides of an arbitrary $D$; the last two are classical consequences for an arbitrary proposition.

**The direct form: `Law_of_SufficientReason`.**  Self-grounding from the positive to the negation of the negative:

```coq
Theorem Law_of_SufficientReason : forall D : Distinction,
  positive D -> ~ negative D.
Proof. exact L4_self_grounding. Qed.
```

The proof is one line: `exact L4_self_grounding`, where `L4_self_grounding` is an auxiliary lemma[^3] expressing self-grounding as a statement about an arbitrary `Distinction`. The lemma rests on the field `exclusive` (through an equivalent transformation).

**The contrapositive form: `L4_contra`.**  Self-grounding in the reverse direction:

```coq
Theorem L4_contra : forall D : Distinction,
  negative D -> ~ positive D.
Proof. exact L4_contrapositive. Qed.
```

If the negative side holds, then the positive side does not. This is a statement symmetric to `Law_of_SufficientReason`, resting on the same structural connection of the fields of the record.

**The canonical form: `L4_canonical`.**  Self-grounding for an arbitrary proposition (without appeal to `Distinction`):

```coq
Theorem L4_canonical : forall P : Prop, P -> ~~P.
Proof. intros P Hp Hnp. exact (Hnp Hp). Qed.
```

The statement: if $P$ holds, then the negation of $P$ does not hold—equivalently, “$P$ holds $\Rightarrow$ one cannot at the same time assert $\neg P$.” This is a standard rule of intuitionistic logic, provable *constructively*, without appeal to `classic`. As in the case of `L2_canonical`, the form is called canonical by subject matter, not by syntax: the theorem works with an arbitrary proposition $P$ directly and does not contain `distinction_of`, but it concerns the canonical pair $P  /  \neg P$ that underlies `distinction_of` $(P)$.

**Double negation: `L4_double_negation`.**  Here the form of the law requires the *reverse* implication:

```coq
Theorem L4_double_negation : forall P : Prop, ~~P -> P.
Proof. intros P Hnnp. destruct (classic P) as [Hp | Hnp].
  - exact Hp.
  - exfalso. exact (Hnnp Hnp). Qed.
```

The statement: if the double negation of $P$ holds, then $P$ itself holds as well. This is a *classical* result, not derivable constructively: the proof rests on the axiom `classic` (applied to an arbitrary $P$ to obtain the cases $P$ or $\neg P$, after which the argument is completed by handling each case).

**The connection of `L4_canonical` and `L4_double_negation`.**  These two theorems express *opposite directions* in one pair of statements: $P \to \neg\neg P$ (provable constructively) and $\neg\neg P \to P$ (requires `classic`). The direct direction expresses that the presence of a ground for $P$ excludes a ground for $\neg P$; the reverse direction, that the absence of a ground for $\neg P$ is itself a ground for $P$. The first is a structural consequence of exclusivity; the second is a manifestation of the completeness of division (the same as $L3$). Therefore the second direction requires the same axiom.

This deserves special emphasis. Despite the name `L4_double_negation` and its placement in the $L4$ block, the formal dependence of this theorem is $L3$: double-negation elimination is proved through `destruct (classic P)` and therefore rests on the classical axiom. Hence `L4_double_negation` is better understood not as a pure consequence of the self-grounding of $L4$ but as a *meeting point* of $L4$ and $L3$: the form belongs to the $L4$ block, while the formal carrier is $L3$.

### The Axiom `L4_witness`

The ToS-Coq repository has a second fundamental axiom (besides `classic`) connected with $L4$—the axiom `L4_witness`. Its role is to provide the *witnessing* of individual existence, not an arbitrary *choice*: the passage from the statement `exists x, P x` to a definite witness `{x | P x}`. This is a formal trace of the thesis of the determinedness of existence, and it *should not* be confused with the Axiom of Choice: the Axiom of Choice builds a choice function for an arbitrary family of sets, whereas `L4_witness` extracts a witness from a *single* fact of existence. In the context of the E/R/R status-transfer mechanism, this is the central technical means.

Here we only mention the existence of this axiom. Its detailed discussion is in the later chapter on the axiomatic layer of ToS, which analyzes both fundamental axioms (`classic` and `L4_witness`) and their relation to the principle $P4$ (the renunciation of the Axiom of Choice) and to the status-transfer mechanism in E/R/R.

### Substantive Meaning

In keeping with the fixed position—mathematics as a language for describing the logical structure of reality—the $L4$ theorems describe a concrete aspect of the work of Logic in what really exists.

In reality, every determinate state of affairs has a ground for being as it is. A molecule has a $C_3$ symmetry axis by virtue of the concrete geometry of the arrangement of its atoms and bonds, not arbitrarily. An integer is even by virtue of its concrete construction as a multiple of two, not “by chance.” The statement “the function $f$ is continuous at the point $x_0$” is true by virtue of the fact that for every $\varepsilon > 0$ there exists a corresponding $\delta$; it is not true out of nowhere.

At the same time, the presence of a ground for one determinacy *closes off* the ground for its opposite *in one respect*. If a molecule has a $C_3$ axis, then in the same geometric respect it does not have an “absence of a $C_3$ axis.” If a number is even, then in the same arithmetical respect it is not odd. The self-grounding of the act of distinction formally expresses this structural connection.

The special ontological status of $L4$ as a meta-law shows itself in the fact that in all the examples given, the *ground* of a concrete determinacy’s holding lies not “beside” the fact but *beneath* it—in a more fundamental structure of the real. The molecule has $C_3$ *thanks to* the concrete structure of its bonds; the number is even *thanks to* its concrete construction; the statement is true *thanks to* the concrete structure of the function. This underlying of grounds is a manifestation of the meta-role of $L4$ as the very action of Logic in which groundedness becomes possible.

The $L4$ theorems in Rocq do not create this structure of reality. They give its formal expression in the simplest form: the self-grounding of `Distinction` as the fact that the presence of one side excludes the other. The full unfolding of Sufficient Reason as the organizing principle of the whole formal system—through types, proofs, constructions—works at a broader level that does not reduce to a single theorem.

With $L1$, $L2$, $L3$, $L4$, four laws concerning the structure of a single act of distinction have been established. The last, $L5$, concerns the *hierarchy* of acts of distinction and works at another level, which requires a separate formal structure. We pass to it in the next section.

## The Law of Order ($L5$)

### The Level at Which $L5$ Works: The Hierarchy of Acts

The Law of Order differs from $L1$, $L2$, $L3$, $L4$ in the *level* of its action. The first four laws concern the structure of a *single* act of distinction—the identity of the sides, exclusivity, exhaustiveness, groundedness. $L5$ *makes possible* the very structure of *relations between* acts of distinction—their sequence, hierarchy, ordering.

Ontologically, $L5$ is a structural condition of *the very possibility of hierarchy*: every determinate existence unfolds at definite levels, and these levels stand in a relation of order. One level precedes another; one act of distinction logically or structurally presupposes another. Without this ordering there would be no sequence of reasoning, no possibility of *building* one thing on another—no formal system and no mathematical work at all.

This position is unfolded in a separate work by the author on the methodology of E/R/R[^4], where $L5$ is shown to be the condition of the very possibility of any determinate system. *Horizontally*, $L5$ shows itself in any sequence of elements at one level—in their ordering relative to one another. *Vertically*, in the hierarchy of levels: the elements of a system of level $n+1$ are themselves systems of level $n$. In the present chapter we touch only on the *formal* side of $L5$: the theorems proved in `LawsFromDistinction.v`. The full methodological unfolding of $L5$ through E/R/R is the subject of Chapter 4 of the present volume.

### The Formal Apparatus: The Type `Level`

Since $L5$ *gives* the hierarchy itself—makes it possible as a structure—its formalization requires a *separate* structure, one in which one can speak of levels and the relations between them. In ToS-Coq this structure is the type `Level`, defined in the file `TheoryOfSystems_Core_ERR.v`.

`Level` is introduced as an inductive type representing the levels of the hierarchy. In the current formalization in `TheoryOfSystems_Core_ERR.v`, $L_1$ is *not* an atomic level in the sense of “the level of atoms” but *the fundamental level of Logic and the ground*; the next level, $L_2$, is built over it, $L_3$ over $L_2$, and so on. On `Level` a strict order operator $\ll$ is defined (formally `level_lt`, abbreviated `<<`); the entry $l_1 \ll l_2$ reads: *$l_1$ is more fundamental, closer to the ground, than $l_2$*. A function `level_depth : Level -> nat` is also defined, giving the depth of each level.

Here we do not unfold the definitions of `Level` and $\ll$ in full—they belong to the later chapter on the structure of levels, which discusses the formal apparatus of $L5$ as a self-standing structure, its role in the work of E/R/R, and its connection with the principles $P1$ (*Level Separation*) and $P2$ (*Hierarchy*). In the present section we concentrate on the *theorems* that formulate the properties of this structure as a formalization of $L5$.

### The Theorems of $L5$

The file `LawsFromDistinction.v` represents $L5$ through five theorems about the properties of the type `Level`.

**Irreflexivity: `L5_hierarchy`.**  No level precedes itself:

```coq
Theorem L5_hierarchy : forall l : Level, ~ (l << l).
Proof. exact level_lt_irrefl. Qed.
```

This is the central structural property of the order. If a level preceded itself, the hierarchy would lose its meaning—it would be impossible to speak of “higher” and “lower,” since every level would be both higher and lower than itself. Irreflexivity guarantees that the hierarchy is a *strict* structure, not a cyclic one.[^5]

**Transitivity: `L5_transitivity`.**  The order is transitive:

```coq
Theorem L5_transitivity : forall l1 l2 l3 : Level,
  l1 << l2 -> l2 << l3 -> l1 << l3.
Proof. exact level_lt_trans. Qed.
```

If $l_1$ precedes $l_2$ and $l_2$ precedes $l_3$, then $l_1$ precedes $l_3$. This is a standard property of a strict order, ensuring that the hierarchy is consistent: a chain of relations leads from any lower level to any higher one through the intermediate ones.

**A concrete relation: `L5_concrete`.**  A concrete manifestation of the order:

```coq
Theorem L5_concrete : L1 << L2.
Proof. exact L1_lt_L2. Qed.
```

The atomic level $L_1$ precedes the level $L_2$. This is not a general statement about arbitrary levels but a concrete one, fixing a concrete relation in the hierarchy. $L_2 \ll L_3$ and so on are proved similarly.

**A chain: `L5_chain`.**  The combination of concrete relations into a chain:

```coq
Theorem L5_chain : L1 << L2 /\ L2 << L3.
Proof. split.
  - exact L1_lt_L2.
  - exact L2_lt_L3. Qed.
```

The atomic level precedes the second, and the second precedes the third. Combining two concrete statements demonstrates that the hierarchy *extends* through the levels successively, forming a chain.

**The absence of infinite descent: `L5_no_infinite_descent`.**  Every level has a finite depth:

```coq
Theorem L5_no_infinite_descent : forall l : Level,
  exists n : nat, level_depth l = n.
Proof. intro l. exists (level_depth l). reflexivity. Qed.
```

For every level $l$ there exists a natural number $n$ expressing its depth. The name `L5_no_infinite_descent` should be understood as an *interpretation*, not as the literal content of the theorem. Formally, the theorem proves a weaker statement: each level is assigned a finite natural depth, and this follows trivially from the definition of `level_depth`. It does *not* formulate or prove the absence of an infinite descending chain as a statement about the relation on sequences of levels—that is, it does not assert $\neg \exists f : \mathbb{N} \to \texttt{Level},\
\forall n,\ f(n{+}1) \ll f(n)$. The substantive interpretation is nonetheless legitimate: since `Level` is given inductively and each level has a finite depth, the very construction of the type points to the absence of non-well-founded descent—the hierarchy is grounded from below, and a descent through the levels sooner or later reaches the fundamental level $L_1$. But it is important to distinguish: *this* is an interpretation resting on the inductive arrangement of `Level`, whereas the theorem `L5_no_infinite_descent` itself fixes only the finiteness of depth. The property agrees with the principle $P4$ (constructivity, the completedness of processes), which will be analyzed in detail in the later chapter on the axiomatic layer.

### What the $L5$ Theorems Show

Unlike $L1$–$L4$, the $L5$ theorems are not tied to a single record `Distinction`. They work with a self-standing structure—the type `Level` and the operator $\ll$. This is a structural manifestation of the fact that $L5$ *gives* the very possibility of a hierarchy of acts and does not work on the structure of a single act.

At the same time, the connection with `Distinction` is preserved at the ontological level: every act of distinction takes place *at a definite level*, and the passage from one act to another (for example, from distinguishing types of numbers to distinguishing types of functions over them) is a passage between levels. The record `Distinction` formalizes the structure of a single act; the type `Level` formalizes the structure of relations between the levels at which acts take place.

The five $L5$ theorems—irreflexivity, transitivity, concrete relations, the chain, the absence of infinite descent—characterize the order $\ll$ as strict, transitive, concretely realizable, and grounded from below. These are the minimal structural conditions under which the hierarchy can work as a basis for the formal derivation of more complex structures, which is what happens in the subsequent parts of the present volume.

### Substantive Meaning

In keeping with the fixed position—mathematics as a language for describing the logical structure of reality—the $L5$ theorems describe a concrete aspect of the work of Logic in what really exists.

In reality, every determinate structure *unfolds at levels* that stand in a relation of order. In the physical world: the level of elementary particles, the level of atoms, the level of molecules, the level of macroscopic bodies—each subsequent level is built on the preceding one and has no meaning without it. In mathematics: the level of the natural numbers, the level of sets of natural numbers, the level of functions over these sets—the same hierarchy. In reasoning: the recognition of an object, its clarification, the selection of a framework, comparison, inference—steps arranged in a definite order, without which reasoning falls apart.[^6]

The irreflexivity of the order ($l \not\ll l$) expresses that a level cannot precede itself—a molecule does not precede a molecule, a number does not precede itself, a step of reasoning does not precede itself. Transitivity ($l_1 \ll l_2 \wedge l_2 \ll l_3 \to l_1 \ll l_3$) expresses that hierarchical relations are consistent: if elementary particles precede atoms and atoms precede molecules, then particles precede molecules. The absence of infinite descent expresses that the hierarchy has a ground—some base level below which there is nothing.

The $L5$ theorems in Rocq do not create these structural facts of reality. They give them formal expression through the type `Level` and the operator $\ll$. The full disclosure of $L5$ as a structural condition of all work with hierarchical systems is in the later chapters: in the chapter on the structure of levels (the formal apparatus) and in the chapter on the methodology of E/R/R (in which $L5$ corresponds to the category *Rules*—the rules that order the work of a system).

With $L1$, $L2$, $L3$, $L4$, $L5$, all five laws of logic have been established in their formal representation in Rocq. The file `LawsFromDistinction.v` also contains theorems that unite these laws into a single structure—we pass to them in the next section.

## Unifying Theorems

The five preceding sections presented the formal derivations of each of the laws $L1$, $L2$, $L3$, $L4$, $L5$ separately. The file `LawsFromDistinction.v` also contains theorems that *unite* these laws into a single structure. These unifying theorems are not a sum of what has already been said but self-standing formal statements showing that the laws work *jointly* in one and the same record `Distinction`, in one and the same hierarchy `Level`, in agreement with one another.

### Five Laws at Once: `five_laws_from_distinction`

The central unifying theorem in `LawsFromDistinction.v` formulates all five laws as a joint property of an arbitrary `Distinction` in the context of the levels `Level`:

```coq
Theorem five_laws_from_distinction : forall D : Distinction,
  (* L1: stability  *) (positive D = positive D
                        /\ negative D = negative D) /\
  (* L2: exclusivity *) (~ (positive D /\ negative D)) /\
  (* L3: totality   *) (positive D \/ negative D) /\
  (* L4: self-grounding *) (positive D -> ~ negative D) /\
  (* L5: hierarchy  *) (forall l : Level, ~ (l << l)).
```

This statement formulates that for every act of distinction $D$ all five structural conditions hold *at once*: the identity of both sides, the exclusivity of the sides, their exhaustiveness, self-grounding, and the hierarchy of levels.

The unifying theorem gives each of the five laws in its *full* form. The law $L1$ is represented by the identity of *both* sides—both the positive, `positive D = positive D`, and the negative, `negative D = negative D`. The law $L5$ is represented by a general statement of irreflexivity *for every level*, $\forall l,\ \neg(l \ll l)$, not only for the base one. Thus the theorem does not cut down any of the laws for the sake of brevity: each of the five conjuncts is the law in the same strength in which it was analyzed separately in “The Law of Identity ($L1$)”–“The Law of Order ($L5$).”

The proof of the theorem is the conjunction of the proofs of each of the laws separately, analyzed in “The Law of Identity ($L1$)”–“The Law of Order ($L5$).” In substance the theorem shows that the five laws *do not compete* and *do not contradict one another*: they are five aspects of one structural integrity, each of which works at full strength without canceling the others.

### The Existence of a Consistent `Distinction`: `laws_consistent`

The next theorem of `LawsFromDistinction.v` gives an *existential* result:

```coq
Theorem laws_consistent : exists D : Distinction,
  positive D /\ ~ negative D.
```

The statement: there exists an act of distinction $D$ in which the positive side holds and the negative side does not. In other words, the structure `Distinction` is *not empty* even in the strict sense that an instance with concrete determinate content is realizable in it—one that is not only formally admissible but also substantively consistent.

The existence of such an instance is a nontrivial formal result. The definition of `Distinction` as a record with four fields does not by itself guarantee that any instance at all can be built with substantively nonzero fields. The theorem `laws_consistent` shows that the building is possible: the universal construction `distinction_of` $(P)$, analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#The Construction distinction_of: Building a Distinction from a Proposition|§ 2.5 “The Construction distinction_of: Building a Distinction from a Proposition”]] of Chapter 2, gives the required instance for any provable proposition $P$.

In substance this means that the laws of logic represented in the record `Distinction` are *realizable*. They are not empty, do not contradict themselves, and leave room for the existence of objects that satisfy all of them at once. This agrees with the ontological position: the structure of the real work of Logic cannot be empty, since the real *is*.

### Paired Unions: `L1_L2_combined` and `L3_L4_combined`

Besides the general five and the existential theorem, `LawsFromDistinction.v` contains *paired* unions that group the laws two by two:

```coq
Theorem L1_L2_combined : forall D : Distinction,
  positive D = positive D /\ ~ (positive D /\ negative D).

Theorem L3_L4_combined : forall D : Distinction,
  (positive D \/ negative D) /\ (positive D -> ~ negative D).
```

The first theorem (`L1_L2_combined`) unites the identity of the positive side and the impossibility of the positive and the negative being present at once. In substance, this is a structural characteristic of *the determinacy of one side*: the positive is the positive, and it *is not* at the same time the negative.

The second theorem (`L3_L4_combined`) unites joint exhaustiveness and self-grounding. In substance, it is a structural characteristic of *the completeness of division with grounding*: either the positive or the negative, and if the positive, then not the negative.

**What the paired unions are for.**  The paired unions are not random combinations. They single out two blocks of meaning within the structure of a single act of distinction:

- The block $L1 + L2$: *determinacy and incompatibility*. A side is itself, and it is not itself and not-itself at once. This is the minimal structural condition of *any determinacy whatsoever*, provable *fully constructively*, without appeal to `classic`.
- The block $L3 + L4$: *completeness and groundedness*. There is no third between the sides, and the presence of one side grounds the absence of the other. This is the structural condition of *the completeness of division*, in which a dependence on the axiom `classic` appears (through `exhaustive`).

The paired unions thus do not duplicate the general five but *structure* it into two levels: the primary constructive conditions ($L1, L2$) and the conditions requiring the classical axiom ($L3, L4$ in full form). $L5$ works at a separate level of the hierarchy and does not enter these paired unions.

### What the Collection of Theorems Shows

The twenty-two theorems of the file `LawsFromDistinction.v`—three forms for $L1$, three for $L2$, three for $L3$, four for $L4$, five for $L5$, plus four unifying ones—jointly show the following.

**The five laws work in one structure.**  The record `Distinction` with four fields and the type `Level` with its order operator form *one* formal structure in which all five laws receive their formal representations. This means that the laws are not “added” to one another from different sources; they are *read* from one and the same structure from different angles.

**Minimality is confirmed.**  Each law rests on a concrete place in the structure:

- $L1$, on the fields `positive` and `negative` (through the reflexivity of their types `Prop`);
- $L2$, on the field `exclusive`;
- $L3$, on the field `exhaustive` (and on the axiom `classic` in the general form);
- $L4$, on the self-grounding lemma, derivable from the field `exclusive`;
- $L5$, on the type `Level` and the operator $\ll$.

This is a structural confirmation of the minimality of the record analyzed in [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record#Minimality of the Record: Can One of the Four Fields Be Removed?|§ 2.6 “Minimality of the Record: Can One of the Four Fields Be Removed?”]] of Chapter 2—but this minimality must be understood precisely. What is at issue is the minimality of the *chosen structural interface*, not an absolute metatheorem about the impossibility of any other encodings. One can imagine another formalization as well—for example, one where the negative side is defined as $\neg P$, so that part of the fields would be computed rather than stored. The claim of the chapter is more modest and more precise: *if* we want to store explicitly the positive side, the negative side, their exclusivity, their exhaustiveness, and the level of the hierarchy, *then* each of these places carries separate formal work, irreducible to the others—the four fields of `Distinction` plus the type `Level`. This is a claim about the minimality of this ontologically transparent record, not about the impossibility of other formalizations.

**Consistency through `laws_consistent`.**  Precision matters here. The theorem `laws_consistent` is *not* a metatheoretical proof of the consistency of the whole formal system Rocq or of the whole formalization of ToS—an internal theorem of Rocq cannot give such a proof. It shows a more modest but important fact: the record `Distinction` is *inhabited* by a concrete instance in which the positive side holds and the negative side does not. This is the local realizability of the record, a sanity check: the structure is not empty and admits a substantive example. From this it is clear that the five laws represented in the record `Distinction` leave room for the existence of an object that satisfies them jointly—but to assert the consistency of the whole system on the basis of this one theorem would be an exaggeration.

**Connection with the fixed ontology.**  In accordance with the position fixed in the Methodological Introduction and spelled out in “From Structure to Theorems: Statement of the Problem” of the present chapter, the formal theorems $L1$–$L5$ neither *create* nor *ground* the laws of logic. These laws are ontologically primary; their work in reality does not depend on any formal system. The collection of theorems of `LawsFromDistinction.v` shows something else: that the simplest formalizable object (the record `Distinction`) already carries within itself all five laws as its *structural properties*, accessible to machine checking. This is formal evidence of how deeply the work of Logic is built into the very possibility of determinate existence: even a minimal formal record of the act of distinction is insufficient to hide any of the five laws—all of them manifest themselves in it ineliminably.

---

[^1]: The lemma `L2_exclusivity` is defined in the file `Distinction.v`.
[^2]: The lemma `L3_totality` is defined in the file `Distinction.v`.
[^3]: The lemma `L4_self_grounding` is defined in the file `Distinction.v`.
[^4]: Horsocrates, *The E/R/R Framework: Structure, Resolution, and the Diagnosis of Paradoxes*, April 2026.
[^5]: The proof rests on the lemma `level_lt_irrefl` from the file `TheoryOfSystems_Core_ERR.v`.
[^6]: The application of $L5$ to the structure of reasoning itself—through the six domains of reasoning $D_1$–$D_6$ (Recognition, Clarification, Framework Selection, Comparison, Inference, Reflection)—is the subject of the branch [[Architecture of Reasoning|“Architecture of Reasoning”]]. In the present volume we merely point to this fact as one more manifestation of the general structural condition $L5$.

---

Part: [[01 First Distinction and Laws of Logic|Part I. The First Distinction and the Laws of Logic]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Order]] · [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/02 Act of Distinction and Its Record|Chapter 2. The Act of Distinction: The Distinction Record]] · [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/04 ERR Ontology of a System|Chapter 4. E/R/R: The Ontology of a System]] →
