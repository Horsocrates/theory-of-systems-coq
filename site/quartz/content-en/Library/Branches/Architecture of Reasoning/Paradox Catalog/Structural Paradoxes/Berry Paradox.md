---
title: "Berry Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Парадокс Берри.md"
sourceBlob: 3f70b27db1616be93be403918364e8fa89aa100a
translated: 2026-10-20
status: draft
description: "Definition through undefinability (the meta-level in the object level)"
---

**S.4** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** Definition through undefinability (the meta-level in the object level)

## Exact Formulation

There are finitely many English phrases shorter than a hundred letters, while there are infinitely many natural numbers; hence there are numbers not definable by any phrase shorter than a hundred letters, and among them a smallest one. Consider: “the smallest natural number that cannot be defined by a phrase shorter than a hundred letters.” This phrase is shorter than a hundred letters—and it defines that very number. A number not definable by a short phrase is defined by a short phrase.

## Origin

G. G. Berry, a modest librarian at Oxford’s Bodleian Library, proposed the knot to Russell; Russell published it in 1906, honestly keeping the author’s name—a rare case in which a paradox bears the name of a librarian rather than a logician. In Russell it took its place beside [[Richards Paradox|Richard]] and the [[Liar Paradox|liar]] as a semantic one: the trouble lives not in numbers but in the word “define.”

## Consequence

Of all paradoxes, Berry’s has the most unexpected offspring. Formalizing “definability” as *the length of the shortest description* gave Kolmogorov complexity—a central concept of information theory; Chaitin turned Berry himself into a theorem: complexity is uncomputable, and there is a bound beyond which a system cannot prove “this number is complex”—whence his version of the proof of Gödel’s theorem. The paradox-curiosity turned out to be a folded-up theorem about the limits of description. The second consequence is Tarskian: “definable” is a predicate about a language, and within the language itself it is inexpressible without stratification.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: numbers; the phrases of a language; the predicate “definable by a phrase shorter than N letters”; the choice of the smallest. Structure: the definition of a number through a property of *all definitions*. No signal yet.

**Domain 2—Clarification: what do the terms mean?** The first signal is “define”: it is not a property of a number (like evenness) but *a relation of the expressions of a language to numbers*—a semantic predicate that lives a storey above both the numbers and the phrases. The counting arithmetic of phrases (“there are finitely many of them”) is flawless; the fog lies in which language and which level “definable” belongs to.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect. Berry’s phrase *uses* the predicate of definability—an operation of level 2 over the pair “language ↔ numbers”—as building material for a definition of level 1. The totality “all phrases shorter than a hundred letters” tacitly includes the phrases that speak about this totality—among them Berry’s phrase itself. [[Identity]]: what defines is not what is defined; [[Order]]: a predicate about a language stands a storey above the language. Signal: the meta-level is drawn into the object level.

**Domain 4—Comparison:** correct within (the counting of phrases, the choice of the smallest—by well-ordering)—the defect is not here.

**Domain 5—Inference:** both lines are flawless under the accepted premise that “definable” is a predicate of the same level as the phrases. The problem is not in the inference.

**Domain 6—Reflection:** the contradiction is a return to domain 3: the trouble lies in the status of the word “define.”

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion. **Violated laws:** Identity · Non-Contradiction (the phrase at once defines a number and speaks about all definitions, including itself) · Order (a semantic predicate placed in the object language). **Essence of the defect:** definition through undefinability: the operation “to define” is drawn into what is defined. On the E/R/R triad: a Rule (the relation language↔numbers) is used as an Element.

## Why There Is No Paradox

“Definable” without an indication of language and level is not a predicate but a gesture. Stratify: “definable in the language L₀” is a predicate of the language L₁. Then “the smallest number not definable in L₀ by a phrase shorter than a hundred letters” is a legitimate phrase *of the language L₁*, and it defines a number in L₁, not in L₀: there is no contradiction, since the phrase does not belong to the totality it speaks about. The knot is tied only when the storeys are confused—when a language is declared to speak about its own definability. The formal remainder is honest and deep: the uncomputability of Kolmogorov complexity is the same boundary, taken by a theorem rather than by a paradox; the limit of description is real—what is illegitimate is only a phrase that pretends to be on both sides of the limit at once.

## Lesson

**On semantic predicates.** “Definable,” “expressible,” “nameable” are words about a language; within the language, without an index of level, they mean nothing. **On the fate of paradoxes.** A paradox rightly read becomes a theorem: Berry → Kolmogorov complexity → uncomputability; the curiosity is a folded-up discovery. **On the fog of quantifiers.** “All phrases”—check whether the speaking phrase itself belongs to the totality.

## Kin by Mechanism

[[Richards Paradox|Richard]] (the same trouble through a diagonal over all definitions), [[Grelling Nelson|Grelling]] (a predicate about words is applied to itself), [[Liar Paradox|the Liar]] (a semantic predicate—truth—in the object language), [[Cantors Paradox|Cantor]] (a totality that includes what speaks about it).

**Machine check.** The Berry–Chaitin diagonal is formalized as a boundary: Kolmogorov complexity is a role-limit, uncomputable by the same self-negating diagonal as halting—src/cs/KolmogorovRoleLimit.v (Berry/Chaitin diagonal); in the registry of 46 the knot is classified as structural, with a guarantee that the paradox does not form (`all_46_dissolvable`, `structural_46_dissolves`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
