---
title: "Chapter 5. Ordinals as Processes; the Tower of Strong Axioms (ATR₀, Π¹₁) and Its Removal"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/10 Теория множеств без аксиомы выбора/05 Ординалы как процессы; башня сильных аксиом (ATR_0, ^1_1) и её снятие.md"
sourceBlob: 1ff2130ee331ff2de25e4186f7b080a4c6ccde05
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 10.4 split the Axiom of Choice in two: the rule-core (L5) is reinterpreted as a theorem, and the completed-object form (the choice graph) is excluded by P4. The same two-level diagnosis applies to the whole rest of the tower of foundations above choice—Infinity, impredicative comprehension, arithmetical transfinite recursion (ATR$_0$), and $\Pi^1_1$ comprehension. But first, the ordinals, for it is by them that the height of this tower is measured, and in ToS they are *processes*.

### A Warning about the Scope of the Claims

This chapter is the most delicate in Part X, and it must be read with an exact measure. When we say that P4 “removes” ATR$_0$ or $\Pi^1_1$, what is meant is a *P4 reinterpretation*: a reading that makes a strong principle *unnecessary within the P4 development*. This is *not* a metatheorem of reverse mathematics: ToS does *not* prove separations of the RM hierarchy, does *not* prove the unprovability of ATR$_0$/$\Pi^1_1$ in weaker systems, and does *not* redefine these principles as formal theorems. What is claimed is strictly the following: the admissible *work* of each principle is done by a concrete P4 device (structural recursion on ordinal notations; the identification of a function with program code), and its *completed-object* form (recursion on an arbitrary completed well-order; quantification over the completed uncountable space of all functions) is not invoked in the P4 development. This scope is maintained to the end of the chapter.

*An ordinal is a role-process; the tower of strong axioms receives the same two-level diagnosis as choice. The “removal” of ATR$_0$/$\Pi^1_1$ is a P4 reinterpretation (a device that makes a principle unnecessary), not a metatheorem of reverse mathematics.*

## Ordinals as Processes

In ToS an ordinal is given inductively: zero, successor, and the *limit of a process*—$\mathrm{OLim} 
f$ for $f:ℕ\to\mathrm{Ord}$. It is precisely the last constructor that makes the ordinal a process: $\mathrm{OLim} f$ carries the role “take the limit of the process $f$, stepping through the natural stages.” Thus $\omega = \mathrm{OLim}$ of the embedding $ℕ\hookrightarrow\mathrm{Ord}$, and $\varepsilon_0 =
\mathrm{OLim}$ of the *tower* $\omega,\ \omega^\omega,\ \omega^{\omega^{\omega}},…$—the limit of the process of exponentiation.[^1] At each stage $n$ only the finite is actual ($\mathrm{OSucc}^n(\mathrm{OZero})$); the ordinal itself is not a completed transfinite object but a position in a well-founded process.

This gives transfinite induction and recursion *on notations*—without axioms. The relation $\mathrm{ord\_lt}$ is well-founded, and from this follow the principles of induction up to $\omega$, the tower, and $\varepsilon_0$.[^2] Let us stress the domain: this is induction/recursion on *constructive ordinal notations* `Ord`, not on an arbitrary completed well-order.

*An ordinal is a role-process ($\mathrm{OLim}$ is the limit of a process; $\varepsilon_0$ is the limit of the tower); transfinite induction on constructive notations is structural and 0-axiom. A completed transfinite object lies outside the Elements.*

## ATR$_0$: Transfinite Recursion as Structural

Arithmetical transfinite recursion (ATR$_0$) is one of the “Big Five” of reverse mathematics: it postulates the possibility of iterating an arithmetical operation along a well-order. In ToS the corresponding *work*—iterating an operation along a *constructive ordinal notation*—is simply a `Fixpoint` on the inductive type `Ord`: Rocq’s termination checker accepts recursion on the structure of $\alpha$, and no axiom is needed.[^3]

The exact measure (see §10.5.1). What has been said applies to recursion along the *notations* `Ord`: for them ATR$_0$-as-an-axiom is not required; structural recursion replaces it. This is *not* a statement about full ATR$_0$ over all completed well-orders and *not* an RM separation. In the terms of the chapter: the admissible core (recursion along constructive notations) is structural recursion (a Rule); the completed-object form (recursion on an arbitrary completed well-order as a ready object) is not invoked in the P4 development.

*ATR$_0$ is a role-confusion: legitimate iteration along notations (a structural `Fixpoint`, 0 axioms) glued to completed recursion on an arbitrary well-order. ToS reinterprets the first and does not invoke the second—without proving RM metatheorems.*

## $\Pi^1_1$: Second Order as First Order over Codes

$\Pi^1_1$ comprehension is the summit of the “Big Five”: it asserts that $\{n \mid \forall f,\ \varphi(n,f)\}$ is a set when $\varphi$ is arithmetical. The catch is the quantifier $\forall f$ over *all* functions $ℕ\toℕ$, which classically means ranging over an uncountable completed space. In ToS the move is different: under P4 every function is a *process* given by *program code*; then “$\forall f$” reduces to “$\forall
c:ℕ$” over codes—second order is read as first.[^4]

Here special care is needed—this is the most delicate point. The “removal” of $\Pi^1_1$ goes through the *identification of a function with program code* ($\forall f \mapsto \forall c:ℕ$). This is a *concrete P4 choice of ontology* (function ${}={}$ process ${}={}$ code), reinterpreting second-order quantification as first-order quantification over codes. This is *not* a metatheorem about
$\Pi^1_1$-CA$_0$ and *not* an RM separation. The admissible reading (a quantifier over functions *given by codes*) is first-order; the completed-object form (a quantifier over the completed uncountable totality of *all* functions) is not invoked in the P4 development—it is exactly the completed object that P4 does not actualize.

*$\Pi^1_1$ is a role-confusion: a quantifier over code-functions (first order) glued to a quantifier over the completed uncountable space of all functions. The P4 reinterpretation takes the first (function ${}={}$ code) and does not invoke the second; this is an ontological choice, not an RM metatheorem.*

## Infinity, Impredicativity; the Tower as One Structure

The same two levels are visible on the two lower storeys of the tower. *Infinity*: ToS does not take a completed infinite set as an Element but keeps infinity as a *scheme of a process*—potential, in the spirit of converging approximations.[^5] *Impredicativity*: the definition $R=\{x \mid x\notin x\}$ quantifies over a totality that includes it; under P1 (hierarchy) and P4 (finiteness) it does not form—this is the Russell case of Chapter 10.1, now as impredicative comprehension.[^6]

Thus the whole tower—choice, infinity, impredicativity, ATR$_0$, $\Pi^1_1$—receives *one* diagnosis. Each strong principle *glues together* a legitimate reading (the rule of L5; a process; structural recursion; a quantifier over codes) with an illegitimate completed-object form (the choice graph; completed infinity; a totality-in-itself; recursion on a ready well-order; the uncountable space of all functions). P4 keeps the first and does not invoke the second. This is the unified structure of Part X.

*Infinity is a process, not a completed object; impredicativity does not form under
P1${}+{}$P4. The whole tower is one role-confusion of a legitimate reading and a completed object; P4 holds the first and sets aside the second.*

## E/R/R Analysis and the Honest Map

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | structural recursion on `Ord`; the identification function ${}={}$ code ($\forall f\mapsto\forall c$); the process scheme for infinity; the level order P1 |
| *Roles* (L4) | ordinal ${}={}$ role-process; $\varepsilon_0={}$ the limit of the tower; “removal of a principle” ${}={}$ the role of P4 reinterpretation (not an RM metatheorem) |
| *Elements* (L1${}+{}$P4) | a finite notation/code/stage at each step; the completed transfinite, a completed well-order, and the uncountable space of all functions are *not* Elements |

**What it yields.** Transfinite induction/recursion on notations—`wf_ord_lt`,
`transfinite_ind` (0 axioms). ATR$_0$/$\Pi^1_1$/Infinity/impredicativity are
reinterpreted (`P4_eliminates_ATR0`, `P4_eliminates_Pi11`,
`P4_eliminates_Infinity`, `P4ProhibitsImpredicative`; ATR/Infinity/impredicativity 0 axioms, $\Pi^1_1$—0 logical axioms with the primitive `eval_program`).

**Diagnosis.** In the P4 ontology of ToS, a strong principle is a gluing of a legitimate reading and a completed-object form; P4 unglues them.

**Honest boundaries (the main point).** The “removal” of ATR$_0$/$\Pi^1_1$ is a *P4 reinterpretation*, not a metatheorem of reverse mathematics: there are neither RM separations nor a proof of unprovability in weak systems. Recursion is on *constructive notations* `Ord`, not on all well-orders. $\Pi^1_1$ is removed by *identifying a function with a code*—an ontological choice, not a theorem about $\Pi^1_1$-CA$_0$. For ATR$_0$ and $\Pi^1_1$ the completed forms (an arbitrary well-order, the uncountable space of functions) are not refuted as RM principles but are *not invoked* in the P4 development; for completed infinity and the impredicative totality the stronger P4/P1 exclusion of the object form applies (Chapters 10.4, 10.1).

*Ordinals are processes; the tower of strong axioms receives a unified two-level diagnosis. Each “removal” is a P4 reinterpretation of a legitimate core (structural recursion, function ${}={}$ code, process), not a metatheorem of reverse mathematics; the completed forms are not invoked—not refuted.*

## Summary and Transition

Ordinals have turned out to be processes: $\mathrm{OLim}$ is the limit of a process, $\varepsilon_0$ the limit of the tower, and transfinite induction on constructive notations is structural and 0-axiom (`wf_ord_lt`, `transfinite_ind`). The tower of strong axioms above choice has received the same two-level analysis as choice itself in 10.4: ATR$_0$ is structural recursion on notations (`P4_eliminates_ATR0`); $\Pi^1_1$ is second order as first order over codes (`P4_eliminates_Pi11`); Infinity is the scheme of a process (`P4_eliminates_Infinity`); impredicativity is shown not to form by P1${}+{}$P4. And all of these—honestly—are P4 reinterpretations, not metatheorems of reverse mathematics.

Chapter 10.6 will assemble Part X: what is provable without choice (including the WQO results of Higman and Kruskal for concrete families and the determinacy of finite games), the full map of axiom prices, and the honest “wall”—the full Kruskal theorem, Borel determinacy, metatheoretical independence—beyond which ToS does not go.

*An ordinal is a role-process, not a completed transfinite; the whole tower of foundations above choice is read by a unified two-level diagnosis—the legitimate core is reinterpreted, the completed object is not invoked. With an exact measure: this is a P4 reading, not theorems of reverse mathematics.*

---

[^1]: `Ordinal.v`: `Ord` (with `OZero`/`OSucc`/`OLim`), `omega` ${}=\mathrm{OLim} \texttt{nat\_to\_ord}$, `epsilon_0` ${}=\mathrm{OLim} \texttt{omega\_tower}$—checked by `Print Assumptions`: Closed, 0 axioms. The arithmetic ($+,\cdot,{}^\wedge$) is by structural recursion, but some of its lemmas rely on functional extensionality.
[^2]: `TransfiniteInduction.v`: `wf_ord_lt` (`well_founded ord_lt`), `transfinite_ind`, `transfinite_rec`; `omega_tower_induction`. **0 axioms** (checked by `Print Assumptions`: `wf_ord_lt` and `transfinite_ind` are closed—*contrary to* the outdated comment in the file header, which wrongly names `classic`; the file does not even import the source of these axioms). In addition, induction on the *level* hierarchy is `level_strong_induction` in `TransfiniteInductionLevel.v` (this work).
[^3]: `P4_Eliminates_ATR.v`: `CB_transfinite`—transfinite iteration (the Cantor–Bendixson derivative) as a `Fixpoint` on `Ord`; `P4_eliminates_ATR0` records the zero/successor equations of the recursion (the limit stage is given by the `Fixpoint` itself). 15 Qed, 0 axioms (checked by `Print Assumptions`: Closed).
[^4]: `P4_Eliminates_Pi11.v`: `Program := nat`, `P4_forall_functions` (a quantifier over functions via codes), with the outcome `P4_eliminates_Pi11`. By `Print Assumptions`, 0 logical axioms, but it depends on `eval_program` (a `Parameter`—a computational primitive of the universal machine); this is the P4 code reinterpretation, not a construction of the space of programs from within.
[^5]: `P4_Eliminates_Infinity.v`: `converges` (convergence of approximations), with the outcome `P4_eliminates_Infinity`. 12 Qed, 0 axioms. Cf. 10.4: potential infinity is compatible with P4, completed infinity is not.
[^6]: `P4ProhibitsImpredicative.v`: P1${}+{}$P4 exclude the completed totality over which the impredicative definition ranges. 10 Qed, 0 axioms.

---

Part: [[10 Set Theory without the Axiom of Choice|Part X. Set Theory without the Axiom of Choice]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/04 Axiom of Choice Prohibition and Reinterpretation|Chapter 4. The Axiom of Choice: Exclusion and Reinterpretation]] · [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/06 Synthesis What Is Provable without Choice and Map of Boundaries|Chapter 6. Synthesis of Part X: What Is Provable without Choice, and the Map of Boundaries]] →
