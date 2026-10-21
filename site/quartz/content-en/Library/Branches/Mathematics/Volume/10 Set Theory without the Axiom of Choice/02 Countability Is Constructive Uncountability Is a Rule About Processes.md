---
title: "Chapter 2. Countability Is Constructive; Uncountability Is a Rule about Processes"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/02 Счётность конструктивна; несчётность — правило о процессах.md"
sourceBlob: 76ce20e9c8c3253ec4175095a309b0761a67ffe9
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Center of Part X

Chapter 10.1 rearranged the ontology: a set is a role-System, membership is a role. The present chapter applies this to two notions that the classical theory holds to be *sizes of completed sets*—countability and uncountability. The textbook picture is this: $ℕ$ and $ℚ$ have size $\aleph_0$, the continuum has size $2^{\aleph_0}$, and these are *properties* of ready objects, cardinal-numbers.

ToS reads both notions not as sizes but as *rules about processes*:

- *countability* is a rule-traversal: a procedure that assigns each item a number (and back). It is an *action* that can be run, not a size label;
- *uncountability* is a rule of distinction: a procedure that, from *any* enumeration, generates a process different from every enumerated one (the diagonal). It is a statement that processes *resist* enumeration, not the size of a ready set.

Neither is a cardinal-object. The diagnosis is the same as in Chapter 4.4 (“uncountability as a rule”), now at the level of set theory itself: $\aleph_0$ and $2^{\aleph_0}$ *as things* are a reified role of comparison.

### The Intellectual Centerpiece: The Asymmetry of the Axiom Price

The main observation of the chapter is an *asymmetry*: the countability of ℚ and the whole diagonal result over $2^{ℕ}$ are *constructive* (0 axioms; `Countability_Q.v` does not even load classical logic), whereas the uncountability of the *completed* continuum rests on classical logic (L3).[^1] The boundary where the constructive passes into the classical is exactly the boundary between a *finite stage of a process* and the *completed continuum*. L3 is not needed for the diagonal scheme $\forall f$ over binary processes itself—it is constructive; L3 enters only in the *real* trisection version, where the limit of nested intervals is actualized as a completed point of the continuum. The finitization boundary coincides with the boundary of constructivity—this will run through the whole chapter.

*Countability and uncountability are role-modes of comparison, not sizes of completed sets. The constructive core (the traversal of ℚ, the diagonal step) is free of axioms; classical logic enters exactly where the completed continuum appears.*

## Countability as a Rule-Traversal (Constructively)

That $ℚ$ is “countable” means in ToS: there is an *explicit traversal*—a bijection between $ℕ$ and the rationals. It is built by the Calkin–Wilf tree: every positive rational is obtained from $1/1$ by a unique finite path of left/right steps, and the numbering of the nodes $1,2,3,…$ lists all irreducible positive fractions *exactly once*.[^2] The sign is added trivially, and the traversal covers all of $ℚ$.

What matters is *how* this is understood. Countability is not the statement “$ℚ$ is a set of size $\aleph_0$” but a *rule*: a computable procedure that matches each rational with a unique number and each number with a rational. It is a process that can be *executed*: give me a number—I return a fraction; give me a fraction—I return a number. No completed collection of “all rationals as an object” is required for this; only a finite-step traversal is needed. Therefore the countability of ℚ costs not a single axiom: neither choice, nor infinity, nor even the excluded middle.

*Countability is the role “being enumerable,” realized by a constructive rule-traversal (`enum_QPos`); it is an executable procedure, not a size label of a ready set.*

## The Diagonal as a Rule of Distinction

Let us pass to binary processes—functions $ℕ \to \{0,1\}$ (or $ℕ\to\mathtt{bool}$). Let $f$ be any enumeration of such processes, $f : ℕ \to (ℕ\to\mathtt{bool})$. We build the *diagonal*: a process $d$ that at the point $n$ takes the value of $f(n)$ at the same point $n$ and *flips* it,

$$
d(n) \;=\; \mathrm{flip}\bigl(f(n)(n)\bigr).
$$

Then $d$ differs from every $f(n)$ at least at the point $n$: by construction $d(n)\neq
f(n)(n)$.[^3]

The diagonal is a *rule*, not a size. Give it an enumeration—it returns a *fresh* process that is not in the enumeration. It works as a *refuter*: it generates difference on demand, constructively, by one bit flip at each stage. Here there is as yet neither an “uncountable set” nor a cardinal—there is only a procedure that, for any $ℕ$-indexed enumeration, builds a process different from every row; at each finite front this is seen as a finite set of differences already presented.

*The diagonal is a role-refuter: a rule that constructively generates a process different from every enumerated one. At this level there are 0 axioms, a pure generating step.*

## Uncountability as a Rule about Processes

From `diagonal_differs` it follows at once: no enumeration *exhausts* the binary processes—for any $f$ the diagonal $d$ is equal to no $f(n)$. This is Cantor’s result over $2^{ℕ}$.[^4] Here $2^{ℕ}$ is the *space of binary processes*, not an already built power set $\mathcal{P}(ℕ)$ in the ZFC sense (10.3 will continue this motif). For the real numbers the same device works in continuous form—*trisection*: from any enumeration of the points of $[0,1]$ one builds a nested sequence of intervals that cuts off every enumerated point, and its limit lies in $[0,1]$ but outside the enumeration. This is how one proves that the interval is uncountable.[^5]

Here is where the honest boundary runs—and it lies not between “the step” and “the quantifier” but between *discrete binary processes* and the *completed real continuum*. Over $2^{ℕ}$ everything is constructive, including the quantifier $\forall f$: `binary_processes_not_enumerable` and `cantor_for_processes` are proved by a pure application of the 0-axiom `diagonal_differs`, without L3. Classical logic enters only in the *real* trisection version: the geometric idea of the step is constructive, but the formal theorem of the uncountability of $[0,1]$ uses L3—when the limit of nested intervals is actualized as a *ready* point of the continuum, and the equality/difference of limit real processes requires classical resolution. In other words, the whole discrete diagonal result over $2^{ℕ}$ is free of axioms; L3 measures out exactly the passage to the completed continuum.

Uncountability, then, is not the size $2^{\aleph_0}$ of some ready set but a *rule*: “processes resist every enumeration.” Over binary processes this rule is constructive in full; the law of excluded middle is needed only where the rule is formulated about the *completed real continuum*.

*Uncountability is the role “resisting enumeration”: for any traversal, the rule-diagonal generates a process outside it. Over $2^{ℕ}$ the rule is constructive in full (0 axioms); the completed statement about the real continuum is classical (L3). The finitization boundary is the boundary of constructivity.*

## E/R/R Analysis

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the rule-traversal (enumeration-bijection, Calkin–Wilf); the rule-distinction (the diagonal over bits, trisection over intervals) |
| *Roles* (L4) | countability ${}={}$ the role “enumerable”; uncountability ${}={}$ the role “resists enumeration”; the diagonal ${}={}$ the role-refuter |
| *Elements* (L1${}+{}$P4) | at each stage, a finite datum: a rational (a node of the tree), a finite bit/path, a nested interval; the “uncountable set” is not a completed Element |

**Well-formedness.** The traversal is well-formed as a bijection (injectivity ${}+{}$ surjectivity,
`Q_positive_countable`); the diagonal is well-formed as a total function different from every row (`diagonal_differs`).

**What it yields.** The countability of ℚ is an executable procedure (0 axioms); Cantor’s result over $2^{ℕ}$ is a consequence of the 0-axiom diagonal; the uncountability of the completed $[0,1]$ is a classical theorem (L3).

**Diagnosis.** In the P4 ontology of ToS, $\aleph_0$ and $2^{\aleph_0}$ *as cardinal-objects* are a reification of the role of comparison. The question “what is the size of the continuum as a thing” substitutes an Element (a cardinal-number) for a role (resistance to enumeration).

**Honest boundaries.** The asymmetry of the axioms is not cosmetic: the constructive core (the traversal, the diagonal/trisection step) and the classical superstructure (the completed continuum, the quantifier over all enumerations) are separated exactly by the boundary of P4. ToS does not build completed $\aleph$-cardinals; “the cardinality of the continuum as a number” is here not an object but a role-limit question.

*Countability is a constructive rule-traversal; uncountability is a rule-resistance with a constructive step and a classical completion. Cardinal-numbers are reified roles of comparison, not Elements.*

## Summary and Transition

Countability and uncountability have ceased to be sizes of ready sets. The countability of ℚ is a constructive traversal (`enum_QPos`, 0 axioms); uncountability is the rule-diagonal (`diagonal_differs`, 0 axioms at the step), carried to a completed statement about the continuum by classical logic (`unit_interval_uncountable_trisect_v2`, L3). The finitization boundary has coincided with the boundary of constructivity—an observation to which Part X will keep returning.

Chapter 10.3 will take the next step: *comparing* cardinalities without the Axiom of Choice. If countability and uncountability are roles, then their ordering (*injection* as “$\le$”) is a rule; Schröder–Bernstein makes this $\le$ antisymmetric up to bijection, and Cantor’s general theorem shows that there is no maximal cardinality—and all this without choice.

*Countability is an executable traversal, uncountability a resistance to enumeration; both are rules about processes, not sizes of completed sets. The constructive core is free of axioms; classical logic measures out exactly the completed continuum—not a step more.*

---

[^1]: Countability: `Countability_Q.v`, header “AXIOMS: NONE (not even classic!)”. The diagonal: `diagonal_differs` (`ProcessDiagonal.v`)—the file explicitly prints `Print Assumptions` and gets “Closed under the global context.” The uncountability of $[0,1]$: `unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`) uses `classic` (L3).
[^2]: `enum_QPos` (`Countability_Q.v`): $ℕ \to$ irreducible positive pairs; `enum_injective` and `enum_surjective` give a bijection, assembled in `Q_positive_countable`; the signed extension to all of $ℚ$ is `enum_Q`. Fully constructive, **0 axioms**.
[^3]: `diagonal` and `diagonal_differs` (`ProcessDiagonal.v`): $\forall f n,\ \lnot `bp_eq` (`diagonal`  f) (f n)$. Only the involutivity of `flip` (Boolean negation) is used; **0 axioms**—the file prints this.
[^4]: `binary_processes_not_enumerable` and `cantor_for_processes` (`ProcessDiagonal.v`)—both rest on the 0-axiom `diagonal_differs`.
[^5]: `unit_interval_uncountable_trisect_v2` (`ShrinkingIntervals_ERR.v`) is the main theorem of the file: $[0,1]$ is uncountable. Here `classic` (L3) is already used.

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/01 Set as a System Not an Object|Chapter 1. Set as a System, Not an Object]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/03 Comparing Cardinalities without Choice Schroeder Bernstein and Cantor|Chapter 3. Comparing Cardinalities without Choice: Schröder–Bernstein and Cantor’s Theorem]] →
