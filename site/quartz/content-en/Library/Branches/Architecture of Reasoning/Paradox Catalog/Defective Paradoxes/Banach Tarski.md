---
title: "Banach–Tarski Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс Банаха-Тарского.md"
sourceBlob: c60413d5d771f3f8d1d594913c424f82699cffff
translated: 2026-10-20
status: draft
description: "The “parts” are non-measurable sets, not physical objects"
---

**D.23** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** The “parts” are non-measurable sets, not physical objects

## Exact Formulation

The theorem (Banach and Tarski, 1924): a ball in three-dimensional space can be partitioned into a finite number of parts—five are enough—and, moving them only by rotations and translations, one can assemble two balls, each equal to the original. Without gaps and without stretching: the motions preserve distances. The theorem is rigorously proved—it follows from the axioms of ZFC set theory, including the Axiom of Choice. From one ball—two just like it.

## Origin

Forerunners: Vitali (1905) constructed the first non-measurable set—already then the Axiom of Choice presented products to which no length can be assigned; Hausdorff (1914) gave a paradoxical decomposition of the sphere. Banach and Tarski carried the line through to the doubling of the ball. Von Neumann (1929) laid bare the mechanism: the culprit is not “infinity in general” but the richness of the group of rotations of three-dimensional space—it contains a free subgroup; on the line and the plane there are no such subgroups, an invariant measure exists (Banach), and doubling is impossible. The standard interpretation has settled in: the theorem shows that “volume” is not defined for all sets of points—the “parts” of the partition are non-measurable, and the paradox arises only when one tries to apply the intuition of a piece to them. The catalog—following the canon of the volume “Mathematics”—holds a deeper diagnosis: this is true, but not enough; the real question is *why* the theory produces “objects” that have no geometric meaning.

## Consequence

The knot became the main exhibit in the dispute over the Axiom of Choice: for some, an acceptable price for a powerful instrument; for others, evidence that the instrument is coming loose from its subject. It led to the theory of amenable groups (von Neumann), to a refinement of the status of non-measurable sets, and to the count of the minimal number of parts (five—Robinson, 1947). And it is also the standard case of the difference between a theorem and its interpretation: as a theorem about group actions on sets it is flawless; what makes it a “paradox” is reading the words “cut,” “part,” and “assemble” in the language of physical pieces. Its defenders reply: there are no physical consequences—bodies consist of atoms, not of points. The volume’s answer: this is an admission—the theory does not describe physical reality; the question remains which reality it does describe—if any at all.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the ball as a set of points, a partition into five “parts,” motions, assembly, two balls. Signal: household words—“cut,” “piece,” “assemble”—about objects that can be neither presented nor imagined.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “Part” splits in two: a physical piece—connected, with a volume, presentable; and an arbitrary set of points—a cloud without definition or measure. The AC-“parts” of the partition are of the second kind: they cannot be described, constructed, or pointed to; they “exist” only as a consequence of an axiom that permits choice without a rule of choice. “Cutting” is not the operation of a knife but a set-theoretic stratification. Signal: words of finite experience have been put on objects without a referent.

**Domain 3—Framework Selection:** the second layer of the defect: the concept of volume is applied to sets outside its domain of definition; deeper still—the very framework “a ball is an actually completed set of points,” plus the postulation of choice: existence without presentation. Signal: the instrument and the object do not meet.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** flawless—the theorem is rigorously proved, and that is the whole point: the problem is not in the inference but in the premises and in the reading of the result.

**Domain 6—Reflection:** “one ball equals two” under motions that preserve volume—signal: the “parts” have no volume; return to domain 2.

## Diagnosis

**Domain of the error:** Domains 2 and 3 (clarification and framework). **Type:** defective—indeterminacy of a concept: “parts” without measure, “cutting” without a knife. **Violated laws:** [[Identity]]—the word “part” serves a piece and a cloud of points at once; [[Non-Contradiction]]—for any nonzero measure, doubling gives μ = μ + μ. **Essence of the defect:** a theorem about the action of a group on sets is read as a claim about pieces of a ball. On the E/R/R triad: a Role (“a part of the ball with a volume”) is assigned where there is no Element to bear it—and this is recorded by machine: in the registry of constructions the verdict on Banach–Tarski is Illusory, an AC phantom without an Element referent.

## Why There Is No Paradox

Three layers, from reckoning to ground. The first is three lines long and machine-checked: if the “parts” had a measure, then from additivity μ = p₁ + p₂ and motion-invariance p₁ = μ, p₂ = μ it follows that μ = 0—doubling is incompatible with any nonzero measure; hence the “parts” are non-measurable, and “motions that preserve volume” preserve what the parts do not have. This closes the contradiction—but not the question. The second layer is the volume’s question: where do objects without geometric meaning come from in the theory? From the combination “an actually infinite set of points + choice without a rule”: the Axiom of Choice postulates existence without presenting it, and its products are sets found in no construction. Read honestly, the Banach–Tarski theorem is a reductio ad absurdum of this combination: when premises give “one equals two” in geometry, it is the premises one should doubt, rather than renaming the absurdity a “counterintuitive property.” The third layer is the boundary that mathematics itself has pointed out: on the line and the plane there is no doubling—a measure exists; in three dimensions the culprit is the free subgroup of the rotation group: doubling is a fact about the structure of the Rules (the motions), not about the “strangeness” of the ball. And the structural result of the base: on the finite, choice is a theorem, not an axiom (choosing the least element is L5 ordering); the postulate is needed only by the infinite without a rule—and the whole formal base of this project does without it.

## Lesson

**On the words of experience.** “Cut,” “part,” “assemble” smuggle the intuition of a piece into a place where its subject is absent; check the referent of a word when the domain changes. **On theorem and interpretation.** The rigor of a proof does not sanctify a reading: a flawless theorem about sets—and a “paradox” only in the language of pieces. **On postulating existence.** An object declared to exist without being presented is a Role without an Element; sooner or later it will present its bill—here the bill comes to “1 = 2.” **On the signal.** The doubling of the ball is not a miracle of infinity but a diagnostic of the premises.

## Kin by Mechanism

[[Galileos Paradox|Galileo]] and [[Hilberts Hotel|Hilbert’s Hotel]] (the same ladder: finite concepts on the unbounded), [[Cantors Paradox|Cantor]] (the top of the ladder; there too—the honest boundary about the diagonal as a technique), the Vitali set (the first non-measurable set—a forerunner), Hausdorff’s paradoxical decomposition (the sphere, 1914).

**Machine check.** There is a named analysis—the flagship of the registry of constructions: `banach_tarski_contradicts_measure` (μ = p₁ + p₂, p₁ = μ, p₂ = μ ⟹ μ = 0: doubling is incompatible with a nonzero Element measure), `verdict BanachTarski = Illusory` and the summary `illusory_constructions_summary` (an AC phantom: choice is needed, there is no witness—src/nonstandard/IllusoryConstructions.v, 0 axioms). Choice on the finite is a theorem: `finite_choice`, `AC_is_L5` (src/foundation/P4_Eliminates_AC.v). In the registry of 46 it is `D23_BanachTarski`: the field `ConceptualAmbiguity`, the level `L3_MetaOperations` (`defective_46_requires_rejection`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
