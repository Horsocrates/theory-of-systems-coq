---
title: "Grelling–Nelson Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Структурные парадоксы/Парадокс Греллинга-Нельсона.md"
sourceBlob: 0e1500085c5978eb3e79336236db5f2e9e2a808c
translated: 2026-10-20
status: draft
description: "A second-order property is applied to itself"
---

**S.3** · [[Structural Paradoxes|structural paradox]] · subtype: Semantic

**Essence of the error.** A second-order property is applied to itself

## Exact Formulation

Let us call a word **autological** if it describes itself: “short” is a short word, “English” is English, “pentasyllabic” is pentasyllabic. Let us call a word **heterological** if it does not describe itself: “long” is not a long word, “French” is not French. The question: is the word “heterological” heterological? If yes—it describes itself (it really is heterological), hence it is autological, not heterological. If no—it is autological, that is, it describes itself; but what it says of itself is “heterological”—so it is heterological. Both paths lead to contradiction.

## Origin

Kurt Grelling and Leonard Nelson, 1908, a paper on the paradoxes of Russell and Burali-Forti—the knot was built on purpose, as a *semantic* replica of the set-theoretic paradox: what Russell did with sets, Grelling and Nelson did with words. The paradox was sometimes attributed to Weyl—Ramsey in 1926 already analyzed it as “Weyl’s contradiction,” and Grelling himself later restored the authorship. In Ramsey’s classification the knot fell into the “second class”—semantic paradoxes, which require the concepts of meaning and denotation—beside the [[Liar Paradox|liar]], as distinct from the “logical” ones (Russell, Burali-Forti); our analysis shows that Ramsey’s division concerns the arena, not the mechanism: the figure is one.

## Consequence

The paradox fixed the lesson: Russell’s trouble is not a particular illness of set theory—the same knot is tied from pure semantics, without a single set. Therefore the treatment must be general: a stratification of types for predicates (a predicate about words stands a storey above the words to which it is applied)—the same remedy as type theory for sets and the hierarchy of metalanguages for truth. For our catalog, Grelling is the most vivid mirror: it shows the substitution from *both* sides—in Russell an element strains to become its own rule, in Grelling a rule is fed to itself as an element.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: words as objects; a classification of words into two classes (autological/heterological); the criterion of the classification—“does the word describe itself”; the question of how to classify the word “heterological.” No signal yet.

**Domain 2—Clarification: what do the terms mean?** “Describes itself”—a property of the word as an object (length, language, number of syllables) coincides with its meaning. For ordinary words the check is innocent: the word-as-object is compared with the word-as-meaning. First signal: “heterological” is not an ordinary word; its meaning is not a property of an object like length but the *classification* itself: it means “not describing itself.” The meaning of this word is an operation of sorting words.

**Domain 3—Framework Selection: is the instrument adequate to the object?** Here lies the defect. Classification is an operation on words: it stands a storey above what it sorts (level 2 over level 1). The question “is ‘heterological’ heterological?” requires the classification to sort *itself*: the predicate that assigns classes to words is fed to itself as a word. [[Identity]]: what sorts is what sorts, what is sorted is what is sorted—different functions; [[Non-Contradiction]]: one cannot be both in one act. Signal: level confusion.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** given the confusion admitted, both branches are flawless. The problem is not in the inference.

**Domain 6—Reflection:** a contradiction on both paths—a return to domain 3.

## Diagnosis

**Domain of the error:** Domain 3 (framework selection). **Type:** structural—vertical level confusion. **Violated laws:** Identity (the construction requires the identity of what classifies and what is classified) · Non-Contradiction (to be the operation of sorting and the sorted word in one act). **Essence of the defect:** Russell’s mirror: there an Element strains to be its own Rule—here a Rule is fed to itself as an Element. On the E/R/R triad: Rule = Element.

## Why There Is No Paradox

“Heterological” as an object-word (13 letters, English, six syllables) is a legitimate object: by these properties it describes or does not describe itself without any trouble. But the question of the paradox asks about something else: whether sorting applies to the sorting itself. The answer is no—and not by decree but by the nature of the operation: a classification has no class—as a sieve does not sift itself and a catalog does not catalog itself. The question is not hard—it is ill-formed; the word “heterological” is neither autological nor heterological: it stands outside the domain of its own sorting. Separate the storeys—predicates about words live a level above the words—and the knot does not tie; the stratification of types only formalizes this separation, by the same vertical of the [[Order|Law of Order]].

## Lesson

**On predicates.** A predicate has a domain of application, and it does not itself belong to that domain: a property of the second order is not an object of the first. **On the mirroring of substitutions.** Categorial substitution goes both ways—an element as a rule (Russell) and a rule as an element (Grelling); diagnosis by the triad must check both. **On innocent self-reference.** “Short” is short: self-description by object-properties is safe; the paradox begins where the operation of classification itself is applied to itself—the same criterion as for the [[Liar Paradox|liar]]: self-description is safe, self-evaluation is dangerous.

## Kin by Mechanism

[[Liar Paradox|The Liar]] (evaluation evaluates itself—the same figure on truth-value), [[Russells Paradox|Russell]] (the direct, not the mirror form: an element as a rule), [[Berry Paradox|Berry]] and [[Richards Paradox|Richard]] (semantic neighbors: definability speaking about itself), [[Barber Paradox|the barber]] (the executor of a rule under his own rule).

**Machine check.** Diagnosis by the triad—Rule = Element; solution—stratification of types: `grelling_is_ill_formed`, `grelling_violation` (src/foundation/ParadoxDiagnosis.v); the self-reference of the construction in the catalog of 46: `S3_grelling_self_ref` (Architecture_of_Reasoning/ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Structural Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
