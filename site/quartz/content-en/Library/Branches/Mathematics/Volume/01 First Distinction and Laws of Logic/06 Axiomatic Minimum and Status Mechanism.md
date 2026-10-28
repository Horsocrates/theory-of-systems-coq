---
title: "Chapter 6. The Axiomatic Minimum and the Status Mechanism"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/01 Перво-различие и законы логики/06 Аксиоматический минимум и механизм статуса.md"
sourceBlob: 3f9d15818aef7f4520ef84125d2126f00f5b81ce
translated: 2026-10-20
status: draft
---

## The Layers of Formal Work

### The Setting of the Chapter

Chapter 5 ended with an observation: formal work in ToS lives at two
levels—at the level of Elements, where operations are applied to
ready-made determinacies, and at the level of Roles and Rules, where the
arrangement is specified within which determinacies receive their
positions. This two-level picture has a concrete *technical* consequence,
which the present chapter unfolds: behind the working formal apparatus
stands a small, clearly surveyable collection of statements declared in
the repository as `Axiom`—that is, as statements that have no proof
inside the type system of CIC.

Before analyzing each such statement separately, it is important to
establish exactly what it *is* in ToS and what it *is not*. This
clarification is fundamental, because without it a discussion of
technique is easily taken for a discussion of postulates.

**What the axioms of ToS are not.** 
The axioms declared in the file `ToS_Axioms.v` of the repository are
*not* the author’s choice. They are not “what we decided to accept
instead of something else.” They are not postulates competing with the
postulates of other theories—such as the axioms of $\mathrm{ZFC}$ or the
axioms of $\mathrm{NBG}$—on the principle “this system chooses some
axioms, that one others, and the choice is a matter of convenience or
taste.”

**What the axioms of ToS are.** 
They are *technical attestations* that certain structural facts, which
in ToS are *derivable* from the arrangement of the act of distinction,
cannot be formally proved inside the type system of CIC. They mark the
places where ontologically primary laws meet the concrete features of
the implementing platform—and where the formal checking of the
corresponding statements requires an explicit declaration in Coq.

This is a precise technical characterization, not a philosophical
nuance. The Law of Excluded Middle ($L3$) follows ontologically from the
structure of the act of distinction and from the laws $L1$, $L2$,
analyzed in Chapter 3. But CIC, as a formal theory, is *constructive* by
default: in it, $L3$ *is not derived* as a theorem for an arbitrary
proposition $P$. Therefore, in order to work in Coq with $L3$ in its
classical form, the repository declares the axiom `classic`. This is not
a *choice* by ToS to accept $L3$ additionally; it is the *registration in
code* of the fact that the ontologically derivable $L3$ requires an
explicit declaration in CIC. The substantive justification of $L3$
remains a derivation from the act of distinction, not a postulate.

The axiom `L4_witness`, connected with the law $L4$ (sufficient reason /
self-grounding), has the same character. In substance, $L4$ is derived
from the arrangement of the act of distinction together with the other
laws; technically, the extraction of a witness from a pure existential is
not derivable in CIC without an explicit declaration; that declaration is
the axiom `L4_witness`.

*Formally, `classic` and `L4_witness` are genuine axioms: in the Rocq
system they are statements accepted by the checking system without proof,
and `L4_witness` is declared directly through `Axiom`. Ontologically,
however, they are not foundations of ToS: in the place of each such axiom
stands an ontologically primary law ($L3$, $L4$), derivable from the
arrangement of the act of distinction, and `Axiom` in the code is a way to
register this law in the CIC environment, which otherwise does not have
it. In short: formally, an axiomatic status in CIC; ontologically, a
derivational status in ToS. We shall hold to this terminological pair
throughout the chapter.*

### Three Layers of Formal Work

With these clarifications made, formal work in the ToS-Coq repository
naturally divides into three layers.

**Layer A: the CIC platform.** 
The first layer is what is available in Rocq *by the very fact* of the
implementation of CIC as a type system. It includes:

- **Inductive types.** A way of specifying new types by listing their constructors (as `nat := O | S nat`). This is a *formation rule* built into the language of types, not an axiom; induction principles (`nat_ind` and its analogues) are derived automatically for every declared inductive type.
- **The universe hierarchy.** The type Prop, the type `Type`$_0$, `Type`$_1$, and so on—a structural hierarchy that does not allow a type to contain a type of its own level. This is the structural counterpart of the principle $P1$ (Chapter 4) built into CIC; [[Russells Paradox|Russell’s paradox]] is blocked here before it can even be written down.
- **$\beta$-reduction, recursion, unification.** The computational part of CIC: the rules by which terms are simplified, equalities are checked, and definitions are unfolded. These rules work automatically, without special axioms.
- **The type Prop as the universe of propositions.** In CIC the type Prop is singled out specially: its inhabitants are propositions (not data), and for them the principle of *propositional proof irrelevance* is adopted in *extractions*, but not inside the theory itself. This is a structural convention of the platform, not a separate axiom.

It is essential that the choice of CIC as the implementation platform is
not accidental. CIC structurally supports the position of ToS: the
hierarchy of universes supports $P1$, and inductive types support
potential (but not completed) infinity, which agrees with $P4$
(Chapter 4). This is what makes it possible to work in the ToS repository
with a minimal number of explicit declarations: a significant part of the
substantive requirements of ToS is already structurally built into CIC.

**Layer B: the technical attestations of $L3$ and $L4$ in CIC.** 
The second layer is two statements declared in the file
`ToS_Axioms.v` of the repository[^1] as `Axiom`. They are:

- **`classic`**—the statement that for every proposition $P$, $P \vee \neg P$ holds. In substance, the law $L3$, derived in ToS from the arrangement of the act of distinction (Chapter 3, § 3.4). Technically, a declaration needed for working with $L3$ in the CIC environment, which does not have it by default.
- **`L4_witness`**—the statement that from an existence $\exists x.  P(x)$ one can extract a concrete element $x$ together with a proof of $P(x)$. In substance, the formal apparatus of self-grounding by the law $L4$ (Chapter 3, § 3.5). Technically, a declaration needed for the constructive extraction of a witness in CIC.

This layer is discussed in detail in § 6.2 (`classic`) and § 6.3
(`L4_witness`) of the present chapter. One thing is essential now:
*beyond the CIC platform, ToS-Coq has no other `Axiom` declarations*.

**Layer C: the definitions and theorems of ToS.** 
The third layer is all the remaining content of the repository: the
record `Distinction`, the construction `distinction_of`, the lemma
`co_constitution`, the $E/R/R$ structure (Chapter 4), the theorems
$L1$–$L5$ (Chapter 3), the theorems $P1$–$P4$ (Chapter 4), and the work
of the subsequent parts of the present volume. These are definitions and
proved statements; they introduce no new axioms but work on the two lower
layers.

*All the content of the ToS repository that goes beyond the CIC platform
reduces *logically* to two laws requiring axiomatic registration—$L3$
and $L4$. These registrations are not founding postulates; they are
technical marks that indicate the places where ontologically primary laws
meet the concrete type system of CIC. (Technically, $L3$ is registered in
more than one place in the current repository—see § 6.2; this is a
matter of synchronization, not an extension of the axiomatics.)*

### A Terminological Clarification: $L4$ and `L4_level`

Before passing to the analysis of each of the two `Axiom` declarations
separately, it is necessary to remove one terminological difficulty that
arises in the repository for technical reasons and that the volume will
systematically keep apart.

In the volume, $L4$ is the *Law of Sufficient Reason*, the fourth of the
laws of logic, analyzed in Chapter 3 (§ 3.5). In substance: every
statement requires a ground that secures its status; in the formal part,
this is the law of the self-grounding of an instance of `Distinction`
through the presentation of a witness.

The repository also contains the technical designation `L4_level` in one
of the main files of the
code[^2].
This is the *fourth level* of the type hierarchy
`Level := L1 | LS Level`, defined as `LS (LS (LS L1))`—that is, as the
third step of succession above the base level $L_1$. This object belongs
to the structure of the $P1$ hierarchy, not to a law of logic.

To avoid confusion, the volume keeps the following distinction:

- $L4$ (the notation for a law)—a law of logic, the fourth of the five laws.
- `L4_level` (entirely in monospace)—a technical object of Coq, the fourth level of the type hierarchy.

At the first appearance of a technical name, the volume always states
explicitly that the code is meant, not the law. The axiom analyzed in
§ 6.3 below, `L4_witness`, belongs to the law $L4$, not to the level
`L4_level`; its name contains “L4” precisely because of its connection
with the law.

### Axiom, Theorem, Derived Principle

In the remaining part of the present chapter we shall regularly use the
distinction among three categories of formal statements: the *axiom*,
the *theorem*, and the *derived principle*. It is not useless to spell
them out explicitly before they begin to work on concrete examples.

**An axiom**  in CIC is a statement declared by the directive `Axiom` and
accepted by the type checker without proof. A statement from an axiom is
available in all files that import the module in which the axiom is
declared. From the point of view of the code checker, an axiom is a
request: “take this on faith.” The substantive justification of an axiom
is a separate question; in ToS, as already said, both axioms have an
exact substantive ground (the derivability of $L3$ and $L4$ from the
arrangement of the act of distinction), even though inside CIC they are
declared as `Axiom`.

**A theorem**  in CIC is a statement derived from previously introduced
definitions, axioms, and other theorems by an explicit proof (by tactics
or terms). A proved theorem is automatically checked by the type checker.

**A derived principle**  is a statement that is formally a theorem but in
substance plays a role analogous to an axiom and is systematically
applied in further work. In ToS such derived principles are, for example,
`L3_informative` and `L4_definite` in `ToS_Axioms.v`: they are not
declared as axioms but proved from `classic` and `L4_witness`, and they
are systematically used in subsequent code.

The distinction among axiom, theorem, and derived principle is the only
technical categorial labeling needed for the remaining work of the
present chapter. With these clarifications we pass to the analysis of
the first of the two axioms—`classic`, the technical attestation of the
law $L3$ in CIC.

## `classic`: The Technical Attestation of $L3$ in CIC

### The Declaration and Its Source

The statement declared in the file `ToS_Axioms.v` as `classic` has the
signature:

```coq
classic : forall P : Prop, P \/ ~P.
```

In words: for every proposition $P$, either $P$ or $\neg P$ holds. This
is the classical Law of Excluded Middle.

In the ToS repository `classic` is not declared anew. In the line of the
file `ToS_Axioms.v`:

```coq
Require Export Coq.Logic.Classical_Prop.
```

the standard module `Classical_Prop` of the Rocq library, in which
`classic` is already declared as an `Axiom`, is imported and re-exported.
After this line the statement `classic` is available in all files that
import `ToS_Axioms`.

That `classic` is taken from the standard library is *not* an accidental
circumstance: the author of the ToS repository does not invent a separate
variant of the Law of Excluded Middle but uses what is already fixed in
the Rocq platform—the very fact that working with classical logic in CIC
requires an explicit declaration exists in Rocq independently of ToS.

A precise remark on the current state of the repository is, however,
necessary. Logically, the project has *two* assumed axiomatic
declarations—$L3$ and $L4$. Technically, however, $L3$ is registered in
more than one place: besides the re-export from `ToS_Axioms.v`, in some
early foundation files—in particular, in `Distinction.v`—$L3$ is declared
*locally*, by the direct line
`Axiom classic : forall P : Prop, P \/ ~ P`,
with the accompanying comment “1 axiom (classic = L3).” In substance this
is the very same $L3$; but technically it is a separate local `Axiom`
declaration, not reduced to the central `ToS_Axioms.v`. Therefore the
thesis “everything beyond the CIC platform fits into two declarations”
should be understood *logically* (two laws—$L3$ and $L4$), not as a claim
that the code contains exactly two physical `Axiom` lines. This is a
place that should be synchronized in the repository: remove the local
`Axiom classic` from `Distinction.v` and replace it with an import of
`ToS_Axioms`, bringing the project to a single center of axioms.

### Why CIC Does Not Have $L3$ by Default

To understand why `classic` has to be declared as an `Axiom` (rather than
derived as a theorem), one must have a clear picture of the
*constructive* character of CIC.

In CIC a proof of a proposition $P$ is the *construction* of an object of
type $P$. For a proposition $P \vee Q$, the construction is an indication
of which of the two sides is chosen, together with a proof of that side:
either a proof of $P$ placed in the *left* branch or a proof of $Q$ placed
in the *right* branch. In the particular case $P \vee \neg P$, the right
branch is a proof of $\neg P$, that is, a function $P \to \bot$.

Applied to $P \vee \neg P$, this means the following. To prove
$P \vee \neg P$ constructively for an *arbitrary* proposition $P$, one
must, for every such $P$, either build a proof of $P$ or build a function
from $P$ to $\bot$. But if $P$ is an *arbitrary* proposition, we have no
general way of doing either: which particular $P$ we shall have to handle
is unknown until a concrete $P$ is received. Constructing an indication of
the left or the right side for all $P$ at once is constructively
impossible.

**An example of structural undecidability.** 
Consider the following class of propositions. Let $p$ be a natural
number encoding a program (for example, in the sense of a universal
Turing machine or an equivalent model), and let $x$ be a natural number
given as input to this program. The proposition $H(p, x)$—“the program
$p$ halts on input $x$”—is a concrete statement for each pair $(p, x)$.

For individual concrete $(p, x)$ the value of $H(p, x)$ may be known: for
some programs halting is obvious, for others it is provably impossible.
However, there is no *general* algorithm deciding $H(p, x)$ for an
arbitrary pair—this is Turing’s classical result (the halting problem is
structurally undecidable). This is *not* a statement about the limits of
our present knowledge; it is a *proved* structural fact about the absence
of a general decider.

Accordingly, for an arbitrary pair $(p, x)$ one cannot in general
constructively present *either* a proof of $H(p, x)$ *or* a proof of
$\neg H(p, x)$—not for an epistemic reason (“we do not know yet”) but for
a structural one (no general constructive method exists). Nevertheless,
by $L3$, for each concrete pair exactly one of the two holds. It is
precisely this situation—where $L3$ is structurally true but not
constructively derivable—for the sake of which `classic` is declared in
the ToS repository.

**What CIC gives without `classic`.** 
CIC does not rule out $L3$—it simply does not *derive* it as a general
theorem. If for a concrete proposition $P$ a proof of $P$ or a proof of
$\neg P$ is known, the constructive system accepts it; if decidability
has been proved for $P$ (the existence of an algorithm that answers, for
each case, whether $P$ holds or not), this too does not require
`classic`. `classic` becomes necessary precisely when the work is carried
on with an *arbitrary* proposition for which neither a proof, nor a
refutation, nor decidability is known in advance.

**A methodological remark.** 
The declaration `classic` secures work with $L3$ for arbitrary
propositions, but this does not mean that in ToS every statement of
existence should be justified through `classic`. When the existence of a
mathematical object—a number, a function, a structure—is at issue, the
preferred path is not to enumerate candidates in the hope of finding one
but to present a *formula of construction*, that is, a *process* that
produces this object. A process on $ℕ$ works potentially—by $P4$,
$ℕ$ is an inductive rule unfolded step by step, not a completed set; and
the existence of an object given by a process is a *property of the
process*, not the result of a lucky enumeration.

In this sense `classic` is a technical means applicable where other paths
are not feasible (as in the case of structural undecidability), not the
preferred way of working with existence in ToS. In substance ToS inclines
toward a process ontology—existence through construction—and turns to
`classic` when the corresponding process is impossible *by structure*,
not for lack of effort.

*In CIC the Law of Excluded Middle is *not* ruled out. It is not
*derived* as a general theorem. Declaring `classic` as an `Axiom` is the
formal way of introducing it into the system while keeping strict control
over where exactly it is used.*

### $L3$ as a Structural Law of the Act of Distinction

The fact that CIC does not derive $L3$ as a general theorem says nothing
about the *substantive* status of $L3$. This is a limitation of a *formal
system*, not a statement about the structure of the act of distinction.

The substantive justification of $L3$ is in Chapter 3, § 3.4. Let us
briefly recall the structure of the derivation. By its structure the act
of distinction is *total*: when $A$ is singled out from $\neg A$,
everything that is not $A$ is assigned to $\neg A$ by that very act. No
*third* region, belonging neither to $A$ nor to $\neg A$, is left in the
act of distinction itself. If such a region arises, this means that the
distinction *was not* an act of distinction with respect to $A$—that is,
a *different* distinction took place, or the distinction did not take
place.

In the record `Distinction` this totality is fixed by the field
`exhaustive : positive \\/ negative`, which *requires* a proof that one
of the sides holds. This field is the formal expression of $L3$ within
`Distinction`; and it is this field that requires `classic` when
`distinction_of P` is built for an arbitrary proposition $P$.

The substantive path:

- the totality of the act of distinction;
- $L3$ as a law;
- the field `exhaustive` in the record `Distinction`;
- `classic` as an `Axiom` in `ToS_Axioms.v`, because CIC by default does not derive $L3$.

The technical path:

- CIC is constructive;
- $L3$ requires a declaration;
- `classic` is declared as an `Axiom`;
- work with `Distinction` becomes possible for arbitrary propositions.

These two paths *meet* in one line of code—the declaration of `classic`
as an `Axiom`[^3].
Substantive derivability and the technical necessity of a declaration
coincide here in result but differ in nature.

### Derived Principles from `classic`

From `classic`, as from an initial statement, the ToS repository derives
several frequently used derived principles. They are theorems (not
axioms), but they are systematically applied in further code; it is
useful to fix them already in the present section.

**Double negation (`NNPP_from_L3`).** 
The statement $\neg \neg P \to P$—so-called *double negation*—is
classically valid but not constructively derivable. In the ToS repository
it is proved:

```coq
Lemma NNPP_from_L3 : forall P : Prop, ~~P -> P.
Proof. intros P Hnn. destruct (classic P); [assumption | contradiction]. Qed.
```

The proof applies `classic` to $P$, examines both cases ($P$ holds—then
$P$ is what is sought; $\neg P$ holds—then from
$\neg \neg P$ and $\neg P$ we obtain a contradiction), and in each case
completes the proof.

**The computational version (`L3_informative`).** 
CIC distinguishes between the propositional disjunction $P \vee Q$
(type Prop) and the informative disjunction $\{P\} + \{Q\}$ (type `Set`
or `Type`). The first asserts the *existence* of one of the cases; the
second makes it possible to distinguish *computationally* which of the
cases holds.

The ToS repository proves:

```coq
Lemma L3_informative : forall P : Prop, {P} + {~P}.
```

The proof rests on `classic` (as the source of $L3$ in propositional
form) and on `L4_witness` (as the source of the possibility of extracting
a concrete case from existence)—that is, on *both* axioms of ToS. This
statement is essential: it makes it possible to pass from a statement of
the existence of one of the sides to the *computational* distinguishing
of this side.

Here it is important to avoid an inaccuracy. `L3_informative` is *not*
required for the construction `distinction_of`: as can be seen from the
file `Distinction.v`, `distinction_of` $(P)$ lives in Prop and, for the
field `exhaustive`, uses only `classic` $P : P \vee \neg P$—a
propositional disjunction, not the informative $\{P\}+\{\neg P\}$.
`L3_informative` is needed in *other* places—where a branch must be
distinguished computationally, that is, where a passage from a
propositional disjunction to an informative one (from Prop to `Type`) has
to be made. It is precisely for such a passage that *both* axioms are
needed; `distinction_of` makes no such passage.

Having fixed `classic` as the first of the two `Axiom` declarations in
ToS and its substantive connection with the law $L3$, we pass to the
analysis of the second declaration—`L4_witness`, the technical
attestation of the law $L4$ in CIC.

## `L4_witness`: The Technical Attestation of $L4$ in CIC

### The Declaration

The second of the two `Axiom` declarations of ToS, declared in the file
`ToS_Axioms.v`, has the following signature:

```coq
Axiom L4_witness : forall (A : Type) (P : A -> Prop),
  (exists x, P x) -> {x : A | P x}.
```

In words: for every type $A$ and predicate $P : A \to
Prop$, if there exists an element $x : A$ satisfying $P$, then this
element can be *extracted* together with a proof of $P(x)$.

Unlike `classic`, which is re-exported from the Rocq standard library,
`L4_witness` is declared directly in the ToS-Coq repository. The Rocq
standard library has analogous constructions, but in the ToS repository
all of them are *excluded* from import[^4]. The reason
for the exclusion will become clear in the course of the present section and is
analyzed in detail in § 6.4.

### From `exists` to `sig`: What the Axiom Does

To understand exactly what `L4_witness` asserts, one must have a clear
picture of the difference between two related constructions of CIC—
`exists` and `sig`.

**Propositional existence (`exists`).** 
The notation `exists x, P x` has type Prop. It is a *proposition*
asserting that *some* $x$ satisfying $P$ exists. Precision is needed
here. A proof of `exists x, P x` in CIC is usually built through the
constructor `ex_intro` and *contains* a concrete witness $x_0$. But since
this proof lives in Prop, the elimination restriction applies to it: in
general, $x_0$ *cannot* be extracted as a computational value of type
`Type`. It is therefore wrong to say that the proposition
`exists x, P x` “carries no witness”; it is more exact to say that the
witness *is there* in its proof but is in general *inaccessible* as a
computational value. It is this inaccessibility, not the absence of a
witness, that constitutes the barrier.

**Informative existence (`sig`).** 
The notation $\{x : A \mid P x\}$—short for `sig P`—has type `Type`. It
is a *pair* consisting of an element $x_0 : A$ and a proof of $P(x_0)$.
Unlike the propositional construction, this one *gives access* to the
witness: having an object of type $\{x : A \mid P x\}$, one can
computationally extract its first component and work with it further.

**The barrier between Prop and Type.** 
In CIC there is a structural barrier between these two constructions.
Having a proof of `exists x, P x` (that is, an object of type Prop), one
*cannot* in general constructively build from it an object of type
$\{x : A \mid P x\}$ (of type `Type`). This barrier is connected with
*singleton elimination*—a rule of CIC that by and large does not allow
propositional objects to be used to build informative ones, in order to
keep the propositional level independent of the computational one.

The axiom `L4_witness` precisely *overcomes* this barrier: it asserts
that the passage from the propositional form $\exists x.  P(x)$ to the
informative form $\{x : A \mid P x\}$ is *always possible*. This is the
technical content of the axiom.

### The Substantive Ground: The Determinacy of Existence

Why `L4_witness` corresponds precisely to the law $L4$ requires an exact
substantive analysis, since technically it is a statement about the
extraction of a witness, whereas in substance $L4$ (Chapter 3, § 3.5) is
the Law of Sufficient Reason. The connection between these two
formulations is as follows.

**Existence = determinacy.** 
In the position of ToS, existence is never “being as a fog.” To exist is
to be *set apart* from what is not, that is, to be *determinate*. This is
the content of [[Metaphysics|“Metaphysics”]] and the content of the law $L4$ unfolded in
Chapter 3. When we assert “there exists an $x$ satisfying $P$,” we assert
the presence of a *determinate* $x$, distinguishable from everything
else, not a vague possibility of something of the kind.

Applied to the existential $\exists x.  P(x)$, this means the following:
if this existential is true, the existing $x$ is *some particular* $x$,
not “a cloud of possibilities.” The fact that the name of this $x$ is not
shown in the propositional notation is a feature of the *notation*, not of
the structure of existence. Structurally, $x$ is determinate; formally,
`L4_witness` gives a way to *access* this determinacy.

**Self-grounding as the meaning of $L4$.** 
In Chapter 3 (§ 3.5) the Law of Sufficient Reason was formulated through
the idea of *self-grounding*: every act of distinction presents within
itself the ground of its own realizability—the witness with respect to
which the distinction took place. For $\exists x.  P(x)$ such a witness
is $x_0$ itself, satisfying $P$: the *presence* of $x_0$ is the ground of
the truth of the existential.

In the formal part, the axiom `L4_witness` translates this substantive
observation into constructive form: “where there is a ground, there is
access to it.” If an insurmountable barrier stood between an existential
and its witness, a state of affairs would be possible in which existence
is asserted without the possibility of accessing what exists. Such a
state of affairs contradicts the position of ToS, and `L4_witness`
formally excludes it.

*Extracting a witness by `L4_witness` is not an act of *choice* from a
set of possible options. It is the *acknowledgment* that existence is
always determinate. The witness is not chosen; it *is presented* as the
ground of the very fact of existence.*

### The Distinction from the Axiom of Choice

It is easy to look at the signature of `L4_witness` as a “little Axiom
of Choice”: in both cases an element is extracted from a statement of
existence. Such a view is superficial and mistaken. The difference
between the two statements—`L4_witness` and the Axiom of Choice—is
structural and essential.

**What `L4_witness` works with.** 
*One* existential $\exists x.  P(x)$ is taken, and *one* witness is
extracted from it. There is no “choice between alternatives” here: for
the given $P$ the witness is already determined (structurally), and the
axiom only gives constructive access to it. This is a *local* operation,
concerning one particular existential.

**What the Axiom of Choice works with.** 
A *family* of existentials $\{\exists x.  P(i, x) \mid
i \in I\}$ is taken, indexed by some set $I$, and the existence of a
*choice function* $f : I \to A$ is asserted, which for each index $i$
presents the corresponding witness. This is a *global* operation,
requiring a consistent choice over all indices at once, while for
different $i$ the witnesses are independent.

**Where the difference lies.** 
`L4_witness` says: “each individual existence is determinate.” The Axiom
of Choice in its set-theoretic sense says: “witnesses can be consistently
chosen for an arbitrarily large family of existences simultaneously.” The
first is a statement about the determinacy of each existence separately;
the second, a statement about the possibility of gathering them
simultaneously into a function. The difference here is *structural*,
categorial: `L4_witness` extracts a witness from one existential, whereas
the set-theoretic Axiom of Choice asserts a choice function for a
completed family of sets.

**A technical caveat: choice-like strength.** 
Here, however, an honest technical caveat is needed, without which the
distinction would sound stronger than it is. It would be *wrong* to claim
that `L4_witness` “does not allow the Axiom of
Choice to be derived” at all. `L4_witness` is declared as a principle
*polymorphic* over `Type`:

$$
\texttt{L4\_witness} : \forall (A : \texttt{Type}) (P : A \to Prop),\;
  (\exists x,\ P x) \;\to\; \{x : A \mid P x\}.
$$

From such a form, if a family of existences is given as a function
$\forall i : I,\ \exists x : A_i,\ P_i x$, a choice function *is built*:
it suffices to apply `L4_witness` under a lambda over $i$ and take the
first projection. That is, as a type-theoretic principle of passage from
`exists` to `sig`, `L4_witness` has *choice-like* strength—in essence it
is the principle of indefinite description.

The correct formulation is therefore as follows. `L4_witness` *is not*
the Axiom of Choice in the set-theoretic sense of choice from a completed
family of sets—and it is precisely this set-theoretic AC that the
principle $P4$ does not admit, as a completed infinity (§ 6.5). But as a
polymorphic type-theoretic principle, `L4_witness` has choice-like
strength: given a family of proofs of existence, it allows one to define
a function that chooses a witness at each index. In the volume these two
things must be kept apart: the set-theoretic AC, incompatible with $P4$,
which `L4_witness` is *not*, and the *type-theoretic* strength of
`L4_witness` as a principle of description. What separates ToS from
theories with set-theoretic AC is not the absence of choice-like strength
at the level of types but the refusal of a *completed* family of
simultaneous choices.

A full analysis of the hierarchy of classical axioms and of the place of
`L4_witness` in it is given in § 6.4.

### A Derived Principle: `L4_definite`

From `L4_witness` the repository derives the principle `L4_definite`,
which concerns *unique* existentials:

```coq
Lemma L4_definite : forall (A : Type) (P : A -> Prop),
  (exists! x, P x) -> {x : A | P x}.
```

Here $\exists! x.  P(x)$ is the standard notation for “there exists a
unique $x$ satisfying $P$.” The statement `L4_definite` extracts this
unique $x$ as an informative value of type $\{x :
A \mid P x\}$.

In substance, `L4_definite` is a strictly weaker version of
`L4_witness`: it requires not merely existence but existence *and
uniqueness*. The proof in the repository reduces it to `L4_witness`
trivially: $\exists x.  P(x)$ is extracted from $\exists! x.  P(x)$, and
`L4_witness` is applied.

One thing is essential: even if `L4_witness` should seem to someone “too
strong,” there is an explicitly stated weaker form—one that works only in
the case of unique existences—and this form is fixed in the repository
separately. This makes it possible to distinguish explicitly in the code
between situations that require the full strength of `L4_witness` and
situations in which `L4_definite` suffices.

Having fixed `L4_witness` as the second of the two `Axiom` declarations
of ToS, its substantive connection with the law $L4$, and its fundamental
difference from the Axiom of Choice, we pass to an exact formal analysis
of the hierarchy of classical axioms, in which `L4_witness` occupies a
strictly determined place.

## The Derivational Nature of the Position of ToS

### Postulate and Derivation

Before passing to the analysis of the structural incompatibilities of ToS
with classical axioms (§ 6.5), it is useful to fix the very *nature* of
the position of ToS with respect to postulates—a nature that differs
essentially from that of the classical axiomatic foundations and that
determines how the comparison of ToS with such foundations should be
understood *at all*.

**The postulational position.** 
In the classical axiomatic foundations of mathematics—from $\mathrm{ZFC}$
to $\mathrm{NBG}$ and beyond—the basic method is as follows. A set of
statements—*axioms*—is chosen and declared accepted. This set fixes what
counts in the system as true “by definition”; all the remaining content is
derived from the axioms. The axioms themselves are justified *outside*
the system—by arguments of mathematical convenience, agreement with
intuition, historical tradition, explanatory power. Inside the system the
axioms are true simply because they have been accepted.

In this position, *to accept one thing or another* is, in an essential
sense, a *choice* by the author of the axiomatization. $\mathrm{ZFC}$
*chooses* the Axiom of Choice; constructive systems *do not choose* it;
different scholars may propose different sets, and the dispute over which
set is “more correct” is conducted outside the formal system—by means of
substantive persuasion.

**The derivational position.** 
ToS works on a different basis. Here no set of axioms is chosen for the
subsequent derivation of everything else. Here *everything is
derived*—from a single initial fact: the act of distinction is possible,
and its structure is observable. From this structure the five Laws are
derived ($L1$–$L5$, Chapter 3); from them, the four Principles
($P1$–$P4$, Chapter 4); from these, the $E/R/R$ analysis, the
construction `Distinction`, and the subsequent parts of the volume.

The technical declarations in `ToS_Axioms.v`—`classic` and
`L4_witness`—are *not* postulates of ToS. ToS as a theory does not build
its content on a set of postulates; its starting point is *one*
structural fact—the act of distinction is possible—and from this fact
the Laws $L1$–$L5$, the Principles $P1$–$P4$, and the whole subsequent
apparatus are derived. As for `classic` and `L4_witness` in the
repository—these are, as was already said in § 6.1 and § 6.3,
declarations that have a *formal-axiomatic* status in CIC and an
*ontological-derivational* status in ToS: formally they are axioms of the
platform; ontologically, the registration of the already derived Laws
$L3$ and $L4$.

*The starting point of ToS is one structural fact: the act of
distinction. All the content of ToS is derived from the arrangement of
this fact. The declarations `classic` and `L4_witness` have a
formal-axiomatic status in CIC but an ontological-derivational status in
ToS: they register in the code Laws that have already been derived, and
they do not serve as the foundation of the theory. Therefore a comparison
of ToS with $\mathrm{ZFC}$ “by whose axioms are better” is ill-posed:
these systems are arranged differently—$\mathrm{ZFC}$ postulates, while
ToS traces a derivation from one structural fact.*

### Why Comparing ToS with ZFC by the Strength of Axioms Is Ill-Posed

The question of comparing ToS with other formal systems naturally arises.
In classical proof theory it is customary to characterize a system by the
*deductive strength* of its axioms—by how extensive a set of theorems is
derivable from it. The more is accepted, the stronger the system; the
less, the weaker. On this scale $\mathrm{ZFC}$ is stronger than systems
without the Axiom of Choice, and constructive systems without $L3$ are
weaker than $\mathrm{ZFC}$.

There is a temptation to place ToS on this scale. The temptation is
deceptive, and understanding why it is deceptive gives an exact
understanding of the position of ToS.

**What “taking a place on the scale of strength” means.** 
To place a theory on the scale of strength is to treat it as a *set of
postulates* compared with other sets of postulates by the extent of what
is derivable. This applies to $\mathrm{ZFC}$, to $\mathrm{NBG}$, to
constructive systems—to systems that *are* sets of postulates and offer
themselves precisely in that capacity.

**Why ToS is not such a set.** 
ToS does not offer itself as a set of postulates. The technical
declarations `classic` and `L4_witness` in the repository do *not*
characterize the position of ToS as “such-and-such a chosen
axiomatization.” They mark the points at which Laws *already derived* in
ToS require technical registration in CIC—and nothing more.

The axioms of $\mathrm{ZFC}$ are justified substantively: they are
offered as a successful shaping of the intuitive concepts of set and
membership. The technical declarations of ToS are justified by
*derivation*: the Law of Excluded Middle is derived from the totality of
the act of distinction, the Law of Sufficient Reason from the
self-grounding of distinction. These two ways of justification differ in
nature.

**What a comparison “on the merits” would be.** 
To compare ToS with $\mathrm{ZFC}$ on the merits would mean asking: *does
$\mathrm{ZFC}$ derive its axioms from anything*, as ToS derives its Laws?
The answer: $\mathrm{ZFC}$ does not derive its axioms. They are accepted.
A comparison by deductive strength keeps its meaning when two *sets* of
postulates are compared; for ToS, in which there is no “set of
postulates” at all, such a comparison turns out to be a translation from
one language—the derivational—into a foreign one—the postulational.

*A comparison of ToS with $\mathrm{ZFC}$ by “strength” is technically
possible but loses its meaning methodologically. One can calculate that
`classic` plus `L4_witness` is deductively weaker than $\mathrm{ZFC}$
with its Axiom of Choice. But this calculation in no way reflects the
fact that in ToS `classic` and `L4_witness` are not an axiomatics chosen
as an alternative to the axioms of $\mathrm{ZFC}$. They are technical
attestations of Laws already *derived* in ToS, registering these Laws in
CIC; ToS has no axiomatics of its own as its foundation.*

### What “Strength” Means in the Position of ToS

If a comparison by the amount of what is accepted does not apply to ToS,
a counter-question arises: what characterizes the *strength* of the
position of ToS? What makes it a working formal system rather than simply
a less postulational version of the classical approach?

The answer lies in the *precision of derivation*. The strength of ToS
lies not in the amount of what is accepted but in the *density* of the
derivational connection between the initial fact and each subsequent
statement. Each Law of logic is derived from the structure of the act of
distinction through the steps analyzed in Chapter 3. Each Principle is
derived from the Laws through the steps analyzed in Chapter 4. The record
`Distinction` is derived from the requirements for fixing the act of
distinction; `co_constitution`, from the joint definition of the sides.
And so on.

This derivational fabric is not a “small axiomatics.” It is a *single
structure of derivation*, proceeding from one point and unfolding into a
full apparatus. The points at which an `Axiom` declaration is required
are the two places where this derivation meets the features of the CIC
platform, nothing more. They are not the “foundations” of the derivation;
they are technical attestations that the derivation has reached points at
which a particular platform requires registration.

**Consequence for the rest of the chapter.** 
§ 6.5 below discusses classical axioms and constructions that are
*incompatible* with the position of ToS. It is essential to understand
in what sense they are incompatible. They are *not* rejected as
“postulates that ToS chooses not to accept”—such a choice would come from
the postulational position, in which ToS does not stand. They turn out to
be excluded as a *consequence*: the derivation from the act of
distinction, unfolded in ToS, excludes them as structurally impossible.
The principle $P4$ of Chapter 4 is a *theorem*, not an axiom (it is
derived from the arrangement of the act of distinction through a chain of
steps); and this theorem has a consequence: completed infinity as an
object is structurally impossible. The Axiom of Choice, which requires
completed infinity for its formulation, turns out to be incompatible with
$P4$—not by our refusal, but by strict formal consequence.

Having fixed the derivational nature of the position of ToS and having
indicated that the incompatibilities with classical constructions are
*consequences* of the derivation, not *choices* from a list of
candidates, we pass to the analysis of the concrete incompatibilities
formally proved in the repository.

## The Constructions of ToS and Their Relation to Classical Objects

### The Setting of the Section

§ 6.4 fixed that at the foundation of ToS lies not a set of axioms but a
*derivation* from a single structural fact—the act of distinction. From
this derivation ToS obtains its own constructions—its own infinity, its
own mechanism of choice, its own way of specifying objects, its own
hierarchy of levels. These constructions live independently and need no
appeal to classical material for their justification.

However, contemporary mathematical practice uses a number of classical
constructions—the Axiom of Choice, the Axiom of Infinity, completed
infinite sets, impredicative definitions—which are accepted in
foundations such as $\mathrm{ZFC}$ and noticeably shape the face of
contemporary mathematics. Since ToS claims to be a working formal
apparatus, it is natural to ask: which of these classical items are found
in ToS, and which are not?

*It is essential* that the question is posed *after* our constructions
have already been derived, and it does not have the character of a
choice. It is a question of *observing* the result: which classical
objects turn out to be constructible in our system and which do not, and
why precisely so.

### Constructions Derived in ToS

Let us list the main constructions obtained in ToS as consequences of the
arrangement of the act of distinction—without appeal to classical
axiomatics.

**Process infinity.** 
It follows from the principle $P4$ (Chapter 4) that infinity in ToS is a
*process*, not an object. The natural numbers are specified as the
inductive type $ℕ := O \mid S ℕ$: each individual number is finite and
obtained by a finite number of applications of the constructor $S$; for
every number already obtained there exists the next one. Infinity works
*potentially*—as the possibility of unfolding, not as a ready-made
collection of all numbers at once.[^5]

**The mechanism of choice through $L5$.** 
The law $L5$ (Chapter 3, § 3.6) gives ontological priority: the
hierarchically senior has precedence over the junior. In the formal
apparatus this turns into a *mechanism of choice by ontological
seniority that respects the hierarchy*: for a nonempty finite list, $L5$
determines which element has the status of “first.” Extracting an element
from a nonempty list is an operation laid into the construction itself:
$L5$ does not choose between equally valid alternatives but realizes the
ontological order laid into the structure.[^6]

**The stratification of levels.** 
The principle $P1$ (Chapter 4) gives the hierarchy of levels: $L1$,
`LS L1`, `LS (LS L1)`, and so on. Objects are distinguished by levels; an
object of level $L$ cannot contain objects of the same level. This
stratification is built into the type system of CIC through the universe
hierarchy ($Prop$, $\texttt{Type}_0$, $\texttt{Type}_1$, $…$); in substance it
expresses a structural consequence of the act of distinction—the
impossibility of self-inclusion, analyzed in Chapter 4.

**The $E/R/R$ structure.** 
From the arrangement of distinction unfolded in Chapter 4, the separation
of roles and rules of formation is derived: every system has a level of
elements (Elements), a level of roles (Roles), and a level of rules
(Rules). This separation works in the formal part as well, as a
structural principle of organization: roles correspond to types, rules
to dependencies between types, elements to values. A detailed analysis
of the $E/R/R$ mechanism for the case of choice is given in § 6.6 below.

**Inductive definitions.** 
The objects of ToS are specified *inductively*—by listing constructors,
not by quantification over a totality. An object of an inductive type is
the result of a finite number of applications of constructors; its
construction is fully transparent and requires no appeal to any completed
collections.

This way of specifying objects is not a choice of implementation; it is a
direct consequence of $P4$: everything actually presented is finite, and
every definition of an object works through this actual finiteness.

*The constructions listed—process infinity, the $L5$ mechanism, the
stratification of levels, $E/R/R$, inductive definitions—are obtained in
ToS from the arrangement of the act of distinction. They exist
independently, as consequences of the derivation, not as an answer to the
classical axioms. The further analysis—of which parts of classical
mathematics prove reproducible in these constructions and which do
not—is an *observation of the result*, not a revision of the
constructions themselves.*

### Which Classical Objects Are Reproduced

Some classical constructions find a full or close analogue in ToS.

**The natural numbers.** 
The classical concept of “the set of natural numbers” is partly
reproduced: each individual number is available in ToS as an element of
the inductive type $ℕ$; all of first-order arithmetic works. What is not
reproduced is the understanding of $ℕ$ as a *ready-made collection of
all* natural numbers; more on this below.

**Finite arithmetic and combinatorics.** 
All finite operations—addition, multiplication, factorial, finite sums,
finite products—work in full. The file `P4_Eliminates_Infinity.v`
contains concrete examples: `factorial(5) = 120`, finite partial sums,
and the like.

**Finite choice.** 
In a finite situation—when the indexed family of existentials is
finite—choice is made through the $L5$ mechanism, as described above.
This is the structural counterpart of what in classical theory is
trivially provable for finite families without appeal to the Axiom of
Choice. In ToS the same result is achieved through its own apparatus, not
through a weakened variant of the classical one.

**Induction as a principle of proof.** 
The principle of induction over the natural numbers, `nat_ind`, is
derived automatically for the inductive type $ℕ$—this is a standard
feature of CIC. Proofs by induction work in ToS exactly as in classical
arithmetic: for the base and the step—and then the statement extends to
all natural numbers.

**Constructive concrete ordinals.** 
The principle called “Arithmetical Transfinite Recursion”
($\mathrm{ATR}_0$) in reverse mathematics motivates in ToS a construction
of transfinite iteration through `Fixpoint` definitions on the inductive
type of ordinals
`Ord := OZero | OSucc Ord | OLim (nat -> Ord)`.
Precision is needed here. A file of the repository[^7] shows that certain schemes of transfinite
iteration can be realized as *structural recursion* on the inductive type
of ordinals, accepted by the means of CIC without a separate axiom. This
is a *$P4$-version of the motif* $\mathrm{ATR}_0$, and *not* a proof that
the whole classical system $\mathrm{ATR}_0$ of reverse mathematics is
entirely reduced to a definition: the file contains no such proof and
does not claim it. To put it exactly: transfinite iteration over a
concrete inductive type of ordinals is constructive; full equivalence
with $\mathrm{ATR}_0$ is a question beyond the scope of this file.

**Second-order quantification over functions.** 
In reverse mathematics, the principle $\Pi^1_1$-Comprehension asserts the
existence of sets singled out by $\Pi^1_1$-formulas (quantification over
functions $ℕ \to ℕ$). ToS introduces a *$P4$-bounded, computable* version
of such quantification: a function is considered as a process-program
encoded by a natural number, and “quantification over all functions” is
replaced by quantification over program codes[^8]. This
gives an *arithmetical analogue* of the corresponding arguments, but it is
*not* a literal reproduction of classical $\Pi^1_1$-Comprehension over
*all* functions $ℕ \to ℕ$: the claim that every function $ℕ \to ℕ$ is a
program is not proved by the file—the reduction is built into the
definition of $P4$-quantification. The exact formula: ToS replaces
quantification over all functions by its $P4$-computable version, and in
this version the $\Pi^1_1$ motif becomes arithmetical.

### Which Classical Objects Are Not Reproduced

Some classical constructions turn out to be impossible to build in ToS.
This is the result of structure, not a consequence of refusal: the means
by which these constructions are specified in the classical setting are
absent in ToS, and an attempt to reproduce them runs into a structural
contradiction with the principles already derived.

**Completed infinity as a ready-made object.** 
In classical mathematics the existence of some infinite set *as a whole*
is postulated—as an object available for operating with: “the set of all
natural numbers exists.” In $\mathrm{ZFC}$ this postulation takes the
form of the Axiom of Infinity.

In ToS infinity is a process. The statement “all natural numbers exist as
a ready-made object” would mean the presence of a predicate true for all
$n : ℕ$ simultaneously and *actually*—that is, an actual infinite
totality of what is presented. This comes into contradiction with $P4$.
Here, however, precision is needed as to the form in which the
contradiction is proved. A file of the repository[^9]
proves a contradiction *in the presence of three premises*: a completed
infinite set (`CompletedInfSet`), the $P4$-boundedness of actuality at
each stage (`P4_stage_bounded`), and a *bridge* (`bridge`) that
translates membership in the completed set into actual presentedness at
stage 0. That is, the formal theorem is this: completed infinity
contradicts $P4$ *in the presence of a bridge* connecting membership with
actuality at a stage. The philosophical interpretation of ToS is
broader—completed infinity as a ready-made object is rejected in
principle; but the Rocq theorem has precisely a conditional form, and one
should not ascribe to the code an unconditional exclusion of “any completed
infinity.”

**The Axiom of Choice in its full formulation.** 
The Axiom of Choice asserts the existence of a choice function
$f : I \to A$ for an arbitrarily large indexed family of existentials. If
$I$ is potentially infinite, such a function *as an object* means the
simultaneous holding of infinitely many values—that is, a completed
infinity. For the reason already analyzed, this is not built in ToS: the
presence of a choice function $f : ℕ \to ℕ$ produces the graph
$\{(n, f(n)) \mid n \in ℕ\}$—a completed infinite object, incompatible
with $P4$.[^10]

The work for which classical mathematics requires the Axiom of Choice is
performed in ToS by the $L5$ mechanism—but *only* for finite families.
The case of infinite families has no analogue in ToS for a principled
reason: simultaneous choice over infinitely many independent places is
structurally incompatible with the process nature of infinity.

**Russell’s paradox.** 
The construction “the set of all sets that do not contain themselves,”
on which Russell’s paradox is built, requires two structural
presuppositions. *First*, the possibility of specifying a set through a
property that objects can have with respect to themselves (that is, the
ambiguity “an object can be both a set and an element of the same
level”). *Second*, a completed totality of all sets.

In ToS both presuppositions are absent. The first is blocked by $P1$: the
hierarchy of levels (Chapter 4) does not admit self-inclusion; an object
of level $L$ cannot contain objects of the same level. The second is
blocked by $P4$: in ToS there is no completed totality of all objects.

In ToS, Russell’s paradox is not an “avoided paradox”: it simply *cannot
be formulated*. The construction on which it is built has no place in the
system.[^11]

**Impredicative definitions through a totality.** 
Definitions of the kind “$X$ is the object having such-and-such a
property among all objects of its type,” in which what is being defined
quantifies over a totality of which it is itself a part, are impossible in
ToS precisely because the system has no corresponding *completed*
totalities. Their role is played by inductive definitions, in which an
object is specified by *listing* constructors, not by selection from a
totality.

### The Rocq Standard Library: Which Modules Are Not Used

The Rocq standard library contains a number of modules that implement
classical constructions which turned out to be impossible in ToS:

- `Coq.Logic.ClassicalDescription`—the definition of an object through a property, relying on the Axiom of Choice.
- `Coq.Logic.ClassicalEpsilon`—Hilbert’s $\epsilon$-operator, which chooses an arbitrary witness, relying on the Axiom of Choice.
- `Coq.Logic.IndefiniteDescription`—indefinite description, another form of choice.

These modules are not imported in the ToS repository. This is not an exclusion
in the sense of an act of will—it is a natural consequence of the fact
that these modules bring into CIC what ToS does not have (the Axiom of
Choice and its variants). Were they imported, a construction would appear
in the repository that has no ground in the derivation from the act of
distinction. In a comment of the file `ToS_Axioms.v` the corresponding
modules are explicitly marked as unused—this mark is a technical
reminder, not an additional rule.

Having fixed the relation of the constructions of ToS to classical
material—what of the classical is reproducible, what is not, and why
precisely so—we pass to a detailed analysis of the central apparatus that
performs in ToS the work of the Axiom of Choice without accepting it.
This apparatus—the mechanism of status transfer through the structure
$E/R/R$—is unfolded in § 6.6.

## Status, Role, Transfer: The Mechanism through $E/R/R$

### The Setting of the Section

§ 6.5 showed that the Axiom of Choice in its full formulation is not
reproduced in ToS: simultaneously holding witnesses over an infinite
family means a completed infinity, which has no place in the system. At
the same time, another apparatus works in ToS, performing the work of
choice—but arranged on a different principle. The present section
analyzes this apparatus on a concrete example.

It is essential that what is analyzed below is not a “weakened Axiom of
Choice” or a “local version” of it. It is a *different* construction,
obtained directly from the arrangement of $E/R/R$ and the Laws
$L1$–$L5$. It works not through choice between alternatives but through
the assignment of *status* in a structured process.

### Setup: Element, Number, Status

Let us consider a simple problem: a sequence of natural numbers is given,
and it is required to determine which of them has the status of the
greatest. In the classical setting this is the problem of finding the
maximum: run through the list, comparing each number with the current
leader, and at the end present the result.

On the *ontological* side, a distinction among three things is
essential; without it the further analysis would be inexact.

**Position, element, number.** 
In an unfolding process three things are distinguished. A *position* is a
place in the unfolding: first, second, third, and so on. An *element* is
what *occupies* this position, entering the process. A *number* is the
*value* of an element. These are not one and the same: an element *is*
not a position, it *occupies* one; and an element *is* not a number, it
*carries* it as its value. When one says “the second element is the
number $3$,” what is meant is: the element that has occupied the
*second* position carries the *value*—the number $3$.

The distinction is essential. In the example analyzed below, one and the
same number—$5$—will appear twice: as the value of the element that has
occupied the *fourth* position, and as the value of the element that has
occupied the *sixth*. These are *different elements*—they have occupied
different positions in the process—although their value is the same.
Without the distinction between element and number, the repetition of a
value would be indistinguishable from identity, and a *repeated* maximum
would make no sense.

**Status.** 
There is no greatest number apart from the process; a number receives
the status of the greatest *because* this status has been assigned to it
in the process. Status is a property that arises *in the process*, not a
property of the number *in itself*: outside the process of passing
through there is no ground for ascribing a status to any number, while
inside the process status is assigned by clear rules.

We may be interested not only in the status of the greatest but also in
the *repeated* appearance of the greatest value—elements whose number
equals the standing maximum. If such repeats interest us, they must not
pass unnoticed; they need a status *of their own*.

The further analysis proceeds in ontological order: *first* the rules
(the questions the process answers), *then* the roles (the statuses
assigned according to the answers). The rules are primary: a role is a
status assigned according to the answer to a rule, and without a rule a
role has no determinacy.

### The Rules

At each step the process takes *one* current element—the next position of
the unfolding, filled with some number—and puts two questions to this
element, in order.

**Rule 1: does the number of the current element exceed
the standing maximum?** 
The question requires a ground for a positive answer. Such a ground is
*strict excess*: if the number of the current element is strictly greater
than the standing maximum, the ground is there. This is $L4$ (the Law of
Sufficient Reason): strict excess is the sufficient reason for the
current element to be assigned the status of maximum and for the former
bearer of this status to lose it.

If there is no strict excess, Rule 1 gives no positive answer, and the
process passes to Rule 2.

**Rule 2: is the number of the current element equal to the standing
maximum?** 
If the number of the current element is *equal* to the standing maximum,
the current element receives the status of *repeated maximum*. If the
number is less than the standing maximum, the current element receives
the status neither of maximum nor of repeated maximum.

*The two rules exhaust the possible outcomes of a step. Rule 1 answers
the question of the *transfer* of the status of maximum and rests on
$L4$. Rule 2 answers the question of the *repetition* of the maximum.
The case in which the number of the current element is less than the
standing maximum is simply the absence of a positive answer to both
rules; the status of the standing maximum does not change, and no
separate law requires changing it—there is no ground for a change.*

### Roles: Basic and Status Roles

Roles in ToS divide into two classes, and for the mechanism under analysis
this distinction is essential.

**Basic roles.** 
A basic role is a role *required* for the actualization of a system.
Without at least one basic role filled, the system is not actualized: it
has only potential. In the problem under analysis, the basic role is the
role by which a number enters the process as its element at all. Every
element that enters the process *already* fills this basic role; *that is
why* it is an element of the process, and *that is why* the questions of
Rules 1 and 2 can be put to it. The particular name of the basic role
depends on which system is being considered; for the present example it
is enough that this role secures the presence of the element in the
process.

**Status roles.** 
A status role is a role assigned *on top of* the basic one according to
the answers to the rules. Unlike the basic role, a status role *may
remain unfilled*: if not a single repeat occurs in the process, the status
role of repeated maximum will never be filled. In the problem under
analysis there are two status roles:

- *Maximum*—the status assigned upon a positive answer to Rule 1. At each stage of the process this status is carried by exactly one element—the one whose number has, at the current moment, strictly exceeded the numbers of all previous ones. When Rule 1 fires, the status is transferred: the former bearer loses it, the new one receives it.
- *Repeated maximum*—the status assigned upon a positive answer to Rule 2. There may be several repeated maxima in a process—one for each step at which Rule 2 has fired. They form a *list*—but this list is not given in advance as a ready-made object: it is *created and extended* in the course of the process, one position for each firing of Rule 2. At any stage the list of repeated maxima exists actually in exactly the extent to which the process has already passed—in full agreement with $P4$: it is a process, not a completed object.

*An element whose number is less than the standing maximum is not left
“without a role.” It fills the basic role—*that is why* it is an element
of the process. It merely receives no *status* role—neither maximum nor
repeated maximum. There can be no element “without a role” in a system:
to be in a system is to carry a role. The difference lies between the
basic role and the status role, not between “a role” and “the absence of
a role.”*

### Where $L4$ Works and Where $L5$ Works

Before analyzing the example, let us fix exactly which Law works where.

**$L4$—within a step.** 
$L4$ works in Rule 1: the strict excess of the number of the current
element over the standing maximum is the *sufficient reason* for
assigning the status of maximum. This is a law acting *within an
individual step*: at each step $L4$ either gives a ground for the transfer
of the status or does not.

**$L5$—the order of the unfolding of the process.** 
$L5$—the Law of Order—works differently. It is not an operation on
elements and does not choose “the first among equals.” $L5$ is the law
that *gives the ordered unfolding of the process*. Thanks to $L5$ the
process is a sequence of steps: there is the *current* element and there
is the *standing* maximum, established at the *past* steps; there is an
ontological seniority of stages—the past is senior to the current, the
current to the subsequent.

It is $L5$ that makes the very arrangement of the process possible.
Without the order of unfolding there would be no “standing” maximum with
which the number of the “current” element is compared; there would be no
“next position” in the list of repeated maxima. The list of repeated
maxima is extended *in order*—each new repeated maximum occupies the next
position—precisely because $L5$, as the Law of Order, gives the order in
which the process unfolds.

*$L4$ acts within a step—as the ground for the transfer of status. $L5$
acts at the level of the whole process—as the Law of Order, which gives
the ordered unfolding thanks to which the process is a sequence of steps
and the list of repeated maxima is extended in a definite order.*

### A Full Analysis on an Example

Let us apply the apparatus to a concrete sequence of values: $1,\; 3,\;
2,\; 5,\; 4,\; 5,\; 7,\;
7$.

**Step 0: the system is not unfolded.** 
Step 0 is the *absence of a step*. The rules are defined, the classes of
roles are defined, but the first assignment has not yet been made: no
element has entered the process, no basic role has been filled. The
system has *potential* but is not *actualized*: the first act of
unfolding has not yet taken place. There is no standing maximum.

**Step 1: the first element, number $1$.** 
The first act of unfolding. The *first* element enters the process,
filling the basic role; the value of this element is the number $1$.
Until now there has been no standing maximum, and there is nothing to
compare with: the first element takes the status of maximum as the
starting one. Standing maximum: $1$. List of repeated maxima: empty.

**Step 2: the second element, number $3$.** 
The *second* element enters the process; its value is the number $3$.
Rule 1: $3 > 1$—strict excess. $L4$ gives the ground. The status of
maximum is transferred to the second element. Standing maximum: $3$. List
of repeats: empty.

**Step 3: the third element, number $2$.** 
The value of the third element is $2$. Rule 1: $2 > 3$? No. Rule 2:
$2 = 3$? No. Neither rule gave a positive answer. The third element fills
the basic role (that is why it is in the process) but receives no status
role. The standing maximum remains $3$—there is no ground for a change.
List of repeats: empty.

**Step 4: the fourth element, number $5$.** 
Rule 1: $5 > 3$. $L4$ gives the ground. The status of maximum goes to the
fourth element. Standing maximum: $5$. List of repeats: empty.

**Step 5: the fifth element, number $4$.** 
Rule 1: $4 > 5$? No. Rule 2: $4 = 5$? No. The fifth element receives no
status role. The standing maximum remains $5$. List of repeats: empty.

**Step 6: the sixth element, number $5$.** 
*This is the key step of the example.* The value of the sixth element is
$5$. It is essential that this is a *different element* from the fourth,
although their value is the same. Rule 1: $5 > 5$? No—$L4$ requires
*strict* excess, and equality does not give it. Rule 2: $5 = 5$? Yes. The
sixth element receives the status role of *repeated maximum*. The
standing maximum remains the same: $5$ (the value of the fourth element).
The list of repeated maxima—that is, of repeats of the *standing*
maximum—is extended: a first position appears in it, and the sixth
element occupies it.

**Step 7: the seventh element, number $7$.** 
Rule 1: $7 > 5$. $L4$ gives the ground. The status of maximum goes to the
seventh element. Standing maximum: $7$. When the standing maximum
changes, the list of repeats that related to the former maximum $5$ is
no longer in force: repeats of the value $5$ are not repeats of the *new*
standing maximum. The list of repeated maxima is *empty again*—there have
been no repeats of the value $7$ yet.

**Step 8: the eighth element, number $7$.** 
The value of the eighth element is $7$; this is a different element from
the seventh. Rule 1: $7 > 7$? No. Rule 2: $7 = 7$? Yes. The eighth
element receives the status role of repeated maximum. The standing
maximum remains $7$. The list of repeated maxima (for the standing
maximum $7$) is extended: the eighth element occupies the first position.

**Summary.** 
At the end of the process the status of maximum is carried by the seventh
element—its value is $7$; the list of repeated maxima has one position,
occupied by the eighth element. Two firings of Rule 2 are recorded: at
step 6 and at step 8—each assigned the status role of repeated maximum to
the corresponding element.

**Status as a process characteristic.** 
The step-by-step analysis reveals something essential: status is a
*process* characteristic, not a final one. Status exists *at a step* and
can be acquired and lost in the course of the process. The sixth element
received the status role of repeated maximum at step 6—and lost it at
step 7, when the standing maximum changed from $5$ to $7$: the repeat of
the value $5$ ceased to be a repeat of the standing maximum. The list of
repeated maxima contained one position at step 6, was empty again at
step 7, and again contained one at step 8.

This is a direct manifestation of $P4$: there is no “final state of the
system” as a ready-made object existing apart from the process. There is
a state *at each stage*—which element carries the status of maximum,
which elements carry the status of repeated maximum—and this state
*changes* from step to step. The status mechanism makes it possible to
trace these changes step by step, and this very traceability is a
consequence of the arrangement of ToS being one of processes, not of
objects.

*In the process there was not a single act of choice between equally
valid options. At each step two rules were posed; the answer to them—by
$L4$ for Rule 1—determined the outcome unambiguously. $L5$ did not take
part in the individual steps as an operation—it gave *the very order* of
the passage, thanks to which at each step the “standing” maximum, the
“current” element, and the “next” position in the list of repeats were
determined.*

### Why This Is Not the Axiom of Choice

The statement of the problem may recall the classical one: “a nonempty
set is given; choose an element.” In this setting the Axiom of Choice
asserts the possibility of choosing by an arbitrary principle. In the
status mechanism analyzed above there is neither a “set” nor a “choice”
in this sense.

**There is no set; there is a process.** 
In the classical understanding, choice is made *from a ready-made set*:
all the elements are already given, and one of them must be indicated. In
the status mechanism the elements *unfold successively* (by $P4$, with
the order of unfolding given by $L5$); at each stage only the elements
passed through are actually presented; status is determined on the
current *state of the process*, not on a set.

**There is no choice; there is the assignment of status by rules.** 
In the classical understanding, choice is an act of indicating one of
several equally valid options. In the status mechanism there is no act of
indication: at each step a status role is either assigned to the current
element (according to the answer to a rule) or not. The outcome of each
step is determined structurally: $L4$ either gives a ground for the
transfer of the status of maximum or does not; equality with the standing
maximum either holds or does not. There are no two “equally valid”
outcomes between which one would have to choose.

**Where it works where the Axiom of Choice does not.** 
The main thing about the status mechanism is that it works not only for
finite processes but also for *potentially continuing* ones—such as the
observable processes from the chapter on coinductive
systems[^12].
In such processes there is no “whole set” as a ready-made object; there
is the current stage and the possibility of passing to the next one. The
Axiom of Choice does not work here, since it requires completed infinity;
the status mechanism works, since it requires only local determinacy at
each stage—the determinacy of the *current* element and of the *standing*
status.

### The Formal Registration of the Mechanism

Precision is needed here as to what has been formalized in the repository
and what has not yet been.

The repository formalizes a *simpler* mechanism than the full status
mechanism analyzed in § 6.6. Namely: the resolution of a nonempty list by
order—the lemma `l5_res_rule` in the file
`src/FormationRules.v`[^13]—and the choice of the first element—the
function `L5_choose` in the file
`src/foundation/P4_Eliminates_AC.v`. These constructions formalize that,
given an order on the elements and a nonempty list, a process unfolded by
$L5$ always arrives at a definite result.

The full status mechanism described in § 6.6—with a state of the form
“standing maximum plus list of repeated maxima,” with a step function,
and with the reset of repeats when the maximum changes—is *not*
formalized in the current repository as a separate automaton file. For
now it should be understood as a *substantive scheme*: an exact
description of how the process of status assignment is arranged, which
*can* be formalized by a separate finite-automaton file (with a state
record, a step function, and theorems about the uniqueness of the status
of maximum at each stage and about the reset of repeats). The sequence
$1,3,2,5,4,5,7,7$ analyzed step by step is an exact illustration of this
scheme; but it is not yet backed by a machine-checked registration of the
whole mechanism.

**A remark on two files: `AC_is_L5` and the exclusion of AC.** 
Let us separately note a place that requires care—and, apparently,
synchronization in the repository itself. The file
`P4_Eliminates_AC.v` contains the theorem `AC_is_L5`
(and the equal theorem `P4_eliminates_AC`):

$$
\forall  (*family* : \mathbb{N} \to \texttt{list nat}),\;
  (\forall i,\ *family*\ i \neq []) \;\to\;
  \exists f,\ \forall i,\ f i \in *family*\ i,
$$

that is, choice over an *$\mathbb{N}$-indexed* family of nonempty
lists—the index $i$ ranges over *all* of $\mathbb{N}$, with no finite
bound. The file `P4ProhibitsAC.v`, by contrast, defines `AC_on_nat` with
*the same* signature ($\mathbb{N} \to \texttt{list nat}$) and proves that it
entails completed infinity and is therefore incompatible with $P4$. An
apparent tension results: one theorem presents $\mathbb{N}$-indexed
choice as a constructive “$L5$,” the other as something $P4$ does not
admit. Only the *finite* version is constructively
indisputable—`finite_choice` with an explicit finite index $n < N$—and it
is indeed present in both files. The correct position for the volume is
this: *finite* choice (over a list, over a finite index) is constructive
and compatible with $P4$; *process* choice over stages is compatible with
$P4$ only when presented as a stage function, not as a completed graph;
and the $\mathbb{N}$-indexed theorem `AC_is_L5` in its current form is a
place that should be reconciled in the repository with `P4ProhibitsAC.v`
(by restricting `AC_is_L5` to a finite index or by explicitly marking it
as a statement about a stage-wise, not a completed, function). Until such
synchronization, the volume must not present the conflict between $P4$ and
AC as already fully disentangled formally.

Having fixed the status mechanism through $E/R/R$ as a construction that
performs in ToS the work of the Axiom of Choice without accepting it, let
us pass to the concluding sections of the chapter—the analysis of what is
built into CIC structurally and requires no declarations (§ 6.7), and the
analysis of the difference between ontological Laws and technical axioms
(§ 6.8).

## What Is Built into CIC Structurally

### The Setting: The Third Layer

In § 6.1 the formal work of ToS was divided into three layers: the CIC
platform (Layer A), the two technical declarations `classic` and
`L4_witness` (Layer B), and the definitions and theorems of ToS
(Layer C). Sections § 6.2–6.6 analyzed Layer B and part of Layer C. The
present section returns to Layer A—to the platform.

This return is not a digression. The essential fact is that a
significant part of the structural requirements of ToS is *already built
into* CIC—not as axioms declared by someone, but as the arrangement of
the type system itself. This is why the ToS repository manages with only
two technical declarations: the CIC platform is structurally consonant
with the position of ToS, and much of what would otherwise have to be
introduced explicitly is already present in CIC by construction.

To analyze what exactly is built in is to understand exactly *where the
boundary runs* between what ToS adds and what it receives from the
platform. Without such an analysis it is easy to take the built-in
properties of CIC for hidden axioms of ToS—which they are not.

### The Universe Hierarchy and $P1$

The first thing built into CIC structurally is the *hierarchy of
universes*.

In CIC every type itself has a type. The type Prop (the universe of
propositions) and the type `Set` have the type `Type`$_0$; `Type`$_0$ has
the type `Type`$_1$; and so on—upward along an infinite (in the potential
sense) hierarchy. The essential property of this hierarchy: *a universe
does not contain itself*. There is no type that would be an inhabitant of
itself; `Type`$_n$ always inhabits the strictly higher `Type`$_{n+1}$.

This arrangement is the structural counterpart of the principle $P1$
(Chapter 4): a hierarchy of levels in which an object cannot contain an
object of its own level or itself. CIC implements $P1$ not as a declared
axiom but as a *built-in rule of type formation*: an attempt to write a
type that inhabits itself does not pass type checking—such an expression
in CIC is simply not well-formed.

**Consequence: Russell’s paradox is inexpressible.** 
As already noted in § 6.5, Russell’s paradox cannot even be formulated in
ToS. Now it is clear at what level this is blocked. “The set of all sets
that do not contain themselves” requires an object capable of containing
objects of its own level (including, possibly, itself). In CIC such an
object *cannot be written*: the universe hierarchy does not allow “the
set of all sets” to be expressed as an object inhabiting the same level
as its elements. The paradox is blocked neither by an axiom nor by an
after-the-fact check—it is blocked by the fact that *the corresponding
expression is not a well-formed type*.

In the repository the hierarchy of levels of ToS[^14] is built on top of
the universe hierarchy of CIC: the formal type hierarchy of ToS rests on
the one that CIC already has.

### Inductive Types and $P4$

The second built-in property is the mechanism of *inductive types*.

In CIC a new type can be specified by listing its *constructors*. The
standard example is the natural numbers: `nat` is specified by two
constructors—`O` (zero) and `S` (the passage to the next). Every
inhabitant of `nat` is the result of a finite number of applications of
constructors: `O`, `S O`, `S (S O)`, and so on. There is no *infinite*
inhabitant—one obtained by an infinite number of applications of
`S`—in `nat`.

This arrangement is the structural counterpart of the principle $P4$
(Chapter 4): what is actually presented is finite, and infinity works
potentially. The inductive type `nat` gives exactly this: each individual
number is finite (obtained in a finite number of steps), and at the same
time every number has a next one (the constructor `S` is always
applicable). Precision is needed here. `nat` in CIC *is* an inductive
type and therefore an object of the language—one *can* quantify over it
(`forall n : nat, …`); it would be wrong to say that “CIC has no type of
all natural numbers.” The type `nat` exists. The question is how ToS
*reads* this type: *not* as a completed set in the set-theoretic
sense—as a totality gathered as a whole—but as a *rule of generation*,
by which every inhabitant is obtained by a finite number of applications
of a constructor. CIC does not compel us to read `nat` as a completed
infinite collection; ToS uses this freedom and reads it as a process. The
difference here lies in the *interpretation* of the type `nat`, not in
its presence or absence.

**The induction principle is derived automatically.** 
For every declared inductive type CIC *automatically* builds the
corresponding induction principle—for `nat` it is `nat_ind`. This
principle is not declared as an axiom: it is a direct consequence of how
an inductive type is arranged. Proofs by induction in ToS rest on these
automatically built principles, not on separate declarations.

### Computation as a Built-In Rule

The third built-in property is the *computational semantics* of CIC.

The terms of CIC are not static: they *compute*. The application of a
function to an argument is simplified ($\beta$-reduction); definitions
are unfolded; expressions over constructors are computed down to a
result. The equality of two terms in CIC is checked, among other ways,
*by computation*: if two expressions reduce to one and the same thing,
they are equal by definition, without any proof.

This computational part is neither an axiom nor a declaration. It is a
*built-in rule* of the type system: CIC is by construction not only a
language for writing statements but also a language of computation. When
ToS checks that `factorial 5` equals `120`, this is checked *by
computation*—the system unfolds the definition of the factorial and
calculates; no axiom is needed for this.

What is essential for the position of ToS is that computability is built
in. What is defined through a finite procedure of construction *is
computed*—and computed without appeal to anything except the built-in
rules of reduction. This agrees with the process ontology of ToS: the
construction of an object is its computation.

### Why the Platform’s Consonance Is Not a Proof of the Position

The built-in properties of CIC analyzed above—the universe hierarchy,
inductive types, the computational semantics—are structurally consonant
with the principles of ToS: $P1$, $P4$, the process ontology. There is a
temptation to strengthen this observation into the claim: “CIC *proves*
the position of ToS” or “CIC *confirms* the truth of ToS.” Such a
strengthening would be a methodological error, and it is important to
understand why.

CIC is an *implementation environment*. The fact that ToS can be
implemented in CIC without doing violence to the platform—that the
principles of ToS fit the arrangement of CIC naturally, not against
it—is evidence of the *realizability* of ToS, not of the *truth* of its
initial structural fact. The truth of the position of ToS is grounded by
the derivation from the act of distinction (Chapters 1–4), not by
consonance with any platform.

One can imagine a different type system in which ToS would not fit so
naturally; this would mean only that the given platform is a less
convenient implementation environment, and it would say nothing about
the truth or falsity of the position of ToS. And conversely: the
consonance of CIC and ToS does not make the position of ToS “true because
CIC is arranged this way.”

*The consonance of CIC and ToS works in one direction: it shows that the
position of ToS is *realizable*—that its principles can be carried
through a rigorous formal check without coming into conflict with the
platform. It does not work in the opposite direction: CIC does not
*ground* the position of ToS. The grounding lies in the derivation from
the act of distinction; CIC only shows that this derivation withstands
formalization.*

This result leads to the last substantive question of the chapter. If
`classic` and `L4_witness` are technical declarations, not ontological
foundations; if the built-in properties of CIC are an implementation
environment, not axioms of ToS; then what exactly does the *ontological*
status of the Laws $L1$–$L5$ consist in, and how does it differ from the
status of everything technical? The next section is devoted to this distinction—between ontological Laws and technical
axioms.

## Ontological Laws and Technical Axioms

### Two Kinds of What Is Present in Formal Work

One distinction has run through the whole of the present chapter, and it
should now be brought together and fixed as a methodological instrument.
In the formal work of ToS, statements of *two different kinds* are
present, and confusing these kinds is the source of the most frequent
misunderstandings regarding the position of ToS.

**Ontological Laws.** 
The first kind is the Laws $L1$–$L5$ (Chapter 3) and the Principles
$P1$–$P4$ (Chapter 4). They are *derived* from the arrangement of the act
of distinction. Their justification is derivation: each of them is
obtained by a chain of steps from a single structural fact. They do not
depend on the platform on which the formal work is carried out: the Law
of Identity or the Law of Sufficient Reason is what it is regardless of
whether ToS is implemented in CIC, in another type system, or without any
formalization at all.

**Technical axioms.** 
The second kind is the declarations `classic` and `L4_witness` in the
file `ToS_Axioms.v`. They are *not derived* inside CIC—they are declared
by the directive `Axiom`. Their presence is due to a concrete
circumstance: CIC is constructive by default and does not derive $L3$ and
the apparatus of witness extraction as theorems. The technical axioms are
the *registration* in code of the already derived Laws $L3$ and
$L4$—a registration needed precisely because the CIC platform is arranged
in a particular way.

*An ontological Law and a technical axiom are different kinds.
A Law is derived from the act of distinction and does not depend on the
platform. A technical axiom is a declaration due to the arrangement of a
particular platform. In the place of `classic` and `L4_witness`
stand the ontologically primary Laws $L3$ and $L4$; these declarations
themselves are only the form in which the Laws are registered in CIC.*

### The Criterion: Invariance with Respect to the Platform

The distinction between the two kinds can be made operational—by setting
a *criterion* that makes it possible to determine, for every statement of
the formal work of ToS, to which kind it belongs.

**The criterion.** 
A statement belongs to the kind of *ontological Laws* if it is
*invariant with respect to the platform*: when the type system in which
the formalization is carried out is changed, it remains the same—because
its justification lies in the derivation from the act of distinction,
not in the arrangement of the platform.

A statement belongs to the kind of *technical axioms* if it *depends on
the platform*: its presence, its form, or its very existence is due to the
fact that a particular platform is arranged in a particular way. With a
change of platform such a statement could disappear, change, or become a
theorem.

**Applying the criterion.** 
The law $L3$ (Excluded Middle) is invariant: it is derived from the
totality of the act of distinction (Chapter 3) and remains the same in
whatever system the formalization is carried out. The declaration
`classic` depends on the platform: it exists *because* CIC is
constructive. In a type system in which Excluded Middle is built in, the
declaration `classic` would be unnecessary—while the law $L3$ would
remain exactly the same.

Similarly, $L4$ (Sufficient Reason) is invariant; the declaration
`L4_witness` depends on the fact that CIC does not derive witness
extraction constructively.

### A Thought Experiment: Changing the Platform

The criterion of invariance is clarified by a thought experiment.

Let us imagine that ToS is formalized not in CIC but in some other type
system—one in which Excluded Middle is *built in* (that is,
$P \vee \neg P$ is derived as a theorem for any proposition). In such a
system the declaration `classic` *would not be needed*: what it
registers, the platform would provide itself.

What would change in ToS under such a transfer? *In the technical
layer*, one declaration would disappear (`classic` would become
unnecessary). *In the ontological layer*, *nothing*. The law
$L3$ would remain derived from the totality of the act of distinction,
just as it was. The totality of the act of distinction does not depend on
a change of platform; neither does the derivation of $L3$ from it.

This experimental shift reveals the boundary exactly. What *can
disappear or change* with a change of platform is the technical layer.
What *remains unchanged* with a change of platform is the ontological
layer. The Laws $L1$–$L5$ and the Principles
$P1$–$P4$ belong to the second; `classic` and
`L4_witness`, to the first.

*The technical axioms of ToS change together with the platform: on one
platform they are needed, on another they are not. The ontological Laws
of ToS do not change with any platform: they are derived from the act of
distinction, and this derivation is not accountable to any platform. This
is precisely why the Laws are the foundation of ToS, while the technical
axioms are only an artifact of implementation.*

### Why the Distinction Is Necessary

Without a clear distinction between the two kinds, the position of ToS
is read incorrectly—and in two opposite ways.

**The first error: taking the technical axioms for the foundation.** 
If `classic` and `L4_witness` are taken for “the real foundations of
ToS,” there arises a picture of ToS as one more postulational theory:
“here is a system; it has chosen such-and-such two axioms.” This picture
is false. Formally, `classic` and `L4_witness` are genuine axioms of
CIC; ontologically, however, they are technical declarations that
register two Laws on the platform, not the *foundations* of ToS. The
ontological foundation of ToS is the derivation from the act of
distinction, and it has a derivational, not an axiomatic, status.

**The second error: taking the Laws for “mere axioms.”** 
The opposite error is to regard the Laws $L1$–$L5$ as “mere axioms among
others,” a set of postulates that ToS has chosen instead of the
postulates of $\mathrm{ZFC}$. This picture is false as well. The Laws are
neither chosen nor postulated; they are *derived*. To call them axioms is
to erase the derivational nature of ToS analyzed in § 6.4.

**The exact picture.** 
Between these two errors lies the exact picture. ToS has an ontological
foundation—the derivation from the act of distinction, unfolding into the
Laws and Principles. ToS has a technical layer—two declarations that
register two of the Laws on a particular platform. The first is the
foundation; the second, an artifact of implementation. Merging them into
one (“the axioms of ToS”) erases precisely the feature that distinguishes
ToS from postulational foundations.

### “Axiomatic Minimum”: The Exact Reading

The present chapter is called “The Axiomatic Minimum and the Status
Mechanism.” The analysis carried out allows us to read this title
exactly.

“Axiomatic minimum” does *not* mean “the minimal set of foundations of
ToS.” Formally ToS does have axioms—two declarations in CIC; but they are
not its ontological *foundation*: the foundation is the derivation from
the act of distinction, which has a derivational status, not the status
of a postulate.

“Axiomatic minimum” means the minimal amount of *technical
declarations* needed to carry ToS through a formal check in CIC. This
amount is two declarations, `classic` and `L4_witness`. They are minimal
not in the sense of “we chose to take fewer,” but in the sense of “CIC,
by its arrangement, requires exactly this many, and no more”: everything
else that ToS needs is either built into the platform (§ 6.7) or derived
(Laws, Principles, definitions, theorems).

*The axiomatic minimum of ToS is not the minimum of what ToS *stands*
on, but the minimum of what ToS *declares* on a particular platform. ToS
stands on the derivation from the act of distinction; ToS declares two
technical axioms in CIC. The first is the foundation, unchanging; the
second is an implementation minimum, dependent on the platform. The
chapter is about how little of the second is required when the first is
arranged as a derivation.*

With this distinction—between ontological Laws and technical axioms—the
chapter on the formal foundations of ToS is complete in its main part.
One subject remains that goes beyond formal technique proper but is
closely connected with it: the question of non-completion—of how the
process ontology of ToS relates to the openness found in mathematics
itself and beyond it. The concluding section of the chapter is devoted
to this.

##  Non-Completion: Mathematics and Quantum Superposition

### Non-Completion as the Through-Line of the Chapter

One motif has run through the whole of the present chapter, and in
conclusion it is worth naming it directly. The principle $P4$ excludes
completed infinity as an object: infinity is a process. The status
mechanism (§ 6.6) works on potentially continuing processes, without
requiring a ready-made set. Status turned out to be a process
characteristic—existing *at a step*, acquired and lost in the course of
the unfolding. The list of repeated maxima *is extended*; it is not given
in advance.

In all these cases one and the same thing is at work: *non-completion*.
There is no ready-made final object apart from the process and prior to
it; there is unfolding, and at each stage the state of that stage.
Non-completion here is not a defect of construction, not “something that
ToS has failed to reach.” It is a structural feature that follows
directly from the arrangement of the act of distinction: the act of
distinction is always *open* to the next act, and completedness as a
ready-made totality has no provision in it.

### Non-Completion within Mathematics

It is worth stating distinctly: the non-completion at issue is a property
of mathematics itself in its arrangement according to ToS, not a
temporary state of knowledge.

When it is said that the natural numbers do *not* form a completed set,
this does not mean “mathematics has not yet gathered them all.” It
means: *the structure makes no provision for gathering them into a
ready-made object*. The natural numbers are an inductive process; “all
the natural numbers at once” is not something toward which the process
strives and which it fails to reach—it is a construction that *has no
meaning* as an object in the process ontology.

In just the same way, the list of repeated maxima in § 6.6 is not a
ready-made object that the process “gradually reveals.” It is what the
process *creates*; outside the process it does not exist, and to speak of
it as of a preexisting given would be an error of the same kind as
speaking of a completed set of all natural numbers.

*Non-completion in ToS is not a limit at which mathematics stops. It is
the arrangement by which mathematics works. Determinacy—of a number, a
status, a result—arises *in* the process, and apart from the process
there is none. A ready-made totality is not a goal that mathematics has
failed to reach; it is a construction for which no place is allotted in
the process ontology.*

### Determinacy as an Act: From Mathematics to Physics

The motif of non-completion—determinacy arising in a process rather than
lying ready before it—is not confined to the foundations of mathematics.
The same motif lies at the basis of how ToS approaches the physical
world.

In the quantum-mechanical description, a system before measurement is in
a state that does *not* ascribe to the observable quantity a single
ready-made value. A determinate value—what is registered—arises *in the
act of measurement*; before this act it does not preexist as a hidden
ready-made fact merely awaiting discovery. Superposition is not “the
value is already there but unknown,” but “the value is not determined as
ready-made.”

This is the same structural motif as in the process ontology of
ToS[^15]: *determinacy is the result of an act, not a property lying
ready before the act*. In $P4$, infinity does not preexist as a
ready-made object—it unfolds. In the status mechanism (§ 6.6), status
does not preexist the process—it is assigned at a step. In quantum
measurement, a determinate value does not preexist the measurement—it is
registered in it.

And all of this is, at its root, the motif of the act of distinction with
which ToS begins: determinacy arises *in* the act of distinction, not
*before* it. What has not been distinguished is not “determinate but
hidden”; it is *indeterminate*, and determinacy comes with the act.

### The Derivation of Physics: Beyond the Volume

What has been said requires a clarification—an exact and important one.
The coincidence of the structural motif of mathematics and of the quantum
description is not a mere consonance of two independent domains. ToS
derives from the act of distinction the laws not only of logic and
mathematics but also of *physics*: the first principle $A = \exists$ is
one, and the unfolding from it does not stop at the mathematical
apparatus.

In particular, the physical program of ToS connects the arrangement of
the act of distinction with the unistochastic structure of quantum
theory—the structure that the program of the stochastic-quantum
correspondence takes as its starting point. This is sketched as follows:
the law $L1$ (the absence of a privileged position) is matched with the
double stochasticity of the transition matrix; the connection between
the two sides of a distinction, applied to a graph structure, with
unitarity; the law $L5$, with the indivisibility of the process. Here,
however, precision is needed regarding formalization. The repository
*already contains* files that check *individual mathematical components*
of the unistochastic structure[^16]. But this is *not* the same as a full
derivation of quantum theory from the act of distinction: what has been
checked are individual matrix lemmas, not the philosophical-physical
derivation of the structure as a whole. The full unfolding of this
derivation—from the act of distinction to the structure of a physical
theory—belongs to *physics* and must not be presented in the
present chapter as already fully carried out and machine-checked.

*The derivation of the laws of physics from the act of distinction—including
the derivation of the unistochastic structure of quantum theory—rests on
the mathematical instruments built in the present volume. The present section only
marks this bridge and this program: the process ontology of ToS, unfolded
in mathematics, continues into physics. Individual mathematical
components of this derivation have already been formalized; the full
derivation is the subject of physics.*

### The Completion of the Chapter

Chapter 6 has completed the *formal* dimension of Part I: the apparatus
has been analyzed—the Laws, the Principles, the $E/R/R$ structure, the
technical foundations of the implementation in Rocq, the status
mechanism. This apparatus has been built and formally checked.

There remains, however, one more layer of Part I—not a formal but an
*ontological* one. Throughout Chapters 1–6, positional decisions were
repeatedly found that ToS makes tacitly, by the very arrangement of its
apparatus: infinity as a process, not an object; the list as the primary
structure, and the set as a derivative mode of working with it;
determinacy as the result of an act of distinction. These decisions were
at work in Chapters 1–6 but were not *gathered* and *explicitly declared*
as ontological positions of the volume.

Chapter 7, the concluding chapter of Part I, is devoted to this. It is
*ontological*: it brings out into the open the ontological positions to which
the volume will return throughout all subsequent parts, and declares them
explicitly. After Chapter 7, Part I—“The First Distinction and the Laws
of Logic”—will be complete in both its dimensions, formal and
ontological, and the unfolded apparatus will be ready for application in
concrete areas of mathematics: to number systems, to the structure of
the continuum, to the foundations of analysis.

---

[^1]: The corresponding file is `src/ToS_Axioms.v` in the repository `theory-of-systems-coq`.
[^2]: The corresponding file is `src/TheoryOfSystems_Core_ERR.v` in the repository.
[^3]: More precisely, through the line `Require Export Coq.Logic.Classical_Prop` in the file `ToS_Axioms.v`: `classic` is declared as an `Axiom` in the Rocq standard library and re-exported from there.
[^4]: These are the modules `Coq.Logic.ClassicalDescription`, `Coq.Logic.ClassicalEpsilon`, and `Coq.Logic.IndefiniteDescription`, listed in a comment of the file `ToS_Axioms.v` as excluded from import.
[^5]: The formal check of this arrangement is in the file `src/foundation/P4_Eliminates_Infinity.v` of the repository `theory-of-systems-coq`.
[^6]: The formalization of the mechanism is the function `L5_choose` in the file `src/foundation/P4ProhibitsAC.v` and the theorem `AC_is_L5` in the file `src/foundation/P4_Eliminates_AC.v`.
[^7]: The file `src/foundation/P4_Eliminates_ATR.v`. The theorem `P4_eliminates_ATR0` in it fixes the base and step equations of the iteration (`iterate_pred` at `OZero` and at `OSucc`).
[^8]: The file `src/foundation/P4_Eliminates_Pi11.v`. In it `Program := nat`, and `eval_program` is declared as a `Parameter`; the theorem `P4_eliminates_Pi11` establishes the equivalence of the $P4$-defined quantification `P4_forall_functions` with quantification over `nat`.
[^9]: The file `src/foundation/P4CompletedInfinity.v`, the type `CompletedInfSet`. The theorem `completed_inf_contradicts_P4`.
[^10]: The formal proof of the incompatibility is in the file `src/foundation/P4ProhibitsAC.v`.
[^11]: The formal check is in the file `src/foundation/P4ProhibitsImpredicative.v`, the theorem `P4_dissolves_russell`.
[^12]: The corresponding type `Observable` in the file `src/CoinductiveSystems.v` of the repository. A detailed discussion of coinductive systems is given in later parts of the present volume.
[^13]: `l5_res_rule`: for a nonempty list with a decidable total order, the function `l5_resolve_gen` returns a value of a definite form (`Some v`).
[^14]: The type `Level` and the relation `level_lt` in the file `src/TheoryOfSystems_Core_ERR.v`; the formal hierarchy of ToS is built on top of the universe hierarchy of CIC.
[^15]: The process nature of infinity is fixed in the file `src/foundation/ProcessP4Synthesis.v` of the repository—in the formulation “infinity is a process, not an object” and in the construction of a generating process.
[^16]: In particular, the file `src/foundation/UnistochasticFromGraph.v`: matrices over $ℚ$, orthogonality, the entrywise square (`gamma_of`), double stochasticity, unistochasticity, the concrete examples $2\times2$ and $3\times3$, and the theorem `unistochastic_implies_DS` are formalized.

---

Part: [[01 First Distinction and Laws of Logic|Part I. The First Distinction and the Laws of Logic]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Order]] · [[Paradox]] · [[Logic]] · [[Formalization]]

Navigation: ← [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/05 Co Definition of A and Not A|Chapter 5. The Co-Definition of A and ¬A]] · [[Library/Branches/Mathematics/Volume/01 First Distinction and Laws of Logic/07 Ontological Core Recurring Motifs|Chapter 7. The Ontological Core]] →
