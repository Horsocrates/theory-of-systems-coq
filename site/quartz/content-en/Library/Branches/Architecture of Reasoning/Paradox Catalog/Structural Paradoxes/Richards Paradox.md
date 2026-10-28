---
title: "Richard’s Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Парадокс Ришара.md"
sourceBlob: 494766069ebaeb4709c3acb3da2179717bfdd165
translated: 2026-10-20
status: draft
description: "Definition through all definitions"
---

**S.5** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** Definition through all definitions

## Exact Formulation

Let us list in alphabetical order all finite English phrases that define real numbers in [0, 1]; we obtain a list of definable numbers: r₁, r₂, r₃, … Let us build the diagonal number d: its n-th digit differs from the n-th digit of the number rₙ (say, add one, and change 9 to 0). Then d differs from every number on the list—d is *undefinable*. But the paragraph you have just read is a finite phrase defining d: d is *definable*. The number is at once on the list and off it.

## Origin

Jules Richard, 1905—a letter written at the height of the crisis of foundations: Cantor’s diagonal move applied not to numbers but to *definitions* of numbers. It immediately became material for the main methodological dispute of the epoch: Poincaré saw in it a model of an “impredicative definition”—a definition through a totality to which the defined itself belongs—and declared such definitions the source of all paradoxes; Russell answered with the vicious-circle principle and the ramified theory of types. Gödel later noted that his incompleteness proof is a relative of Richard’s paradox, carried out legitimately (about provability instead of definability).

## Consequence

Richard gave logic the word **predicativity**—a watershed alive to this day: a definition is legitimate if it does not appeal to a totality that includes what is defined. Hence Russell’s ramified types, Weyl’s predicative analysis (*The Continuum*), Feferman’s predicative systems; in computer science, the exclusion of cyclic definitions. And a mirror lesson about the diagonal: in Cantor it is legitimate—it works over a *given* list and builds something new outside it; in Richard the list claims to include *all* definitions, the diagonal one among them—the same technique drawn into its own domain.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: phrases-definitions; the list of all definable numbers; the diagonal construction; the predicate “definable.” Structure: a definition built from the totality of all definitions. No signal yet.

**Domain 2—Clarification: what do the terms mean?** “Definable” is a semantic predicate: a relation of phrases to numbers, a storey above both ([[Berry Paradox|Berry]]). First signal: “*all* defining phrases”—in which language? If in the very one we are working in, the totality must include phrases about the totality itself.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect. The diagonal is an operation *over* the list (level 2 over level 1); the diagonal definition of d refers to the whole list of definitions—and at the same time claims to be a member of it (it is, after all, a phrase that defines a number). A definition through a totality to which it itself belongs is an impredicative circle: [[Identity]]—what defines is not what is defined; [[Order]]—an operation over a list is not a line of the list. Signal: the diagonal is drawn into its own domain.

**Domain 4—Comparison:** correct within (digit-by-digit difference is an honest comparison). The defect is not here.

**Domain 5—Inference:** both lines are flawless under the premise “the list contains all definitions, including the diagonal one.” The problem is not in the inference.

**Domain 6—Reflection:** a contradiction—a return to domain 3: the premise of a self-including totality.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion. **Violated laws:** Identity · Non-Contradiction (a phrase that is a member of the list and an operation over the whole list in one act) · Order (a line and an operation over lines are different storeys). **Essence of the defect:** impredicativity: a definition through the totality of all definitions, which includes the definition itself. On the E/R/R triad: a Rule (the diagonal over the list) is written down as an Element (a line of the list).

## Why There Is No Paradox

Stratification puts everything back in its place: “definable in the language L₀” is a predicate of the language L₁; the list exhausts the definitions of *L₀*, and the diagonal phrase is a definition *in L₁*: it legitimately builds a number outside the list of L₀ and need not be counted in it. The contradiction lived only in the claim of one language to contain its own semantics. The remainder is honest and famous: carry out the same move legitimately, and you get not a paradox but theorems (the undefinability of truth by Tarski, incompleteness by Gödel: a diagonal over provability instead of definability). Richard is the illegitimate version of a great move; the whole difference lies in keeping account of the storeys.

## Lesson

**On predicativity.** A definition through a totality that includes what is defined defines nothing: the circle is not depth but emptiness. **On technique and domain.** One and the same diagonal is a theorem over a given list and a paradox over “all definitions”: the legitimacy of an operation is decided by its domain, not by its form. **On legitimization.** The paradoxes of this family are drafts of theorems: Richard → Tarski/Gödel; keeping account of levels turns trouble into a result.

## Kin by Mechanism

[[Berry Paradox|Berry]] (the same semantics of definability, without the diagonal), [[Cantors Paradox|Cantor]] (the diagonal, legitimate over a given set—illegitimate over “everything”), [[Grelling Nelson|Grelling]] (a predicate in its own domain), [[Liar Paradox|the Liar]] (semantics in the object language).

**Machine check.** Impredicativity is formalized and constructively not admitted: P4 rejects definitions through a self-including totality—src/foundation/P4ProhibitsImpredicative.v (`russell_contradiction_without_P1`, `P4_dissolves_russell`, `p4_impredicative_synthesis`); the legitimate diagonal as a rule about processes—src/process/ProcessDiagonal.v (`binary_processes_not_enumerable`); in the registry of 46 it is structural, with the paradox shown not to form (`all_46_dissolvable`). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
