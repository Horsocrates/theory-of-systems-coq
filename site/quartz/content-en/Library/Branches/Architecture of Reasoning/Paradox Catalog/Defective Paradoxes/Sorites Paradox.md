---
title: "Sorites Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс кучи (сорит).md"
sourceBlob: 78fa90115e9f3300463a2266cf538c394e27a358
translated: 2026-10-20
status: draft
description: "“Heap” is not clarified as a graded concept"
---

**D.1** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** “Heap” is not clarified as a graded concept

## Exact Formulation

A heap of 10,000 grains is undoubtedly a heap. Remove one—still a heap. If removing one grain never turns a heap into a non-heap, then by repeating the step even a single grain turns out to be a heap. The reverse move: one grain is not a heap; adding one grain does not create a heap; so 10,000 is not a heap either. The form is mathematical induction: the base (10,000 is a heap) and the step (minus one—the status is the same) are accepted, and the induction leads to absurdity.

## Origin

One of the oldest knots in philosophy. Its author is Eubulides of Miletus (fourth century BCE, the Megarian school), to whom the [[Liar Paradox|liar]], the [[Bald Man Paradox|bald man]], and the [[Horned Man|horned man]] also belong. The Greek σωρίτης (sōritēs) comes from σωρός (sōros), “heap”; the Latin form sorites took hold in the tradition; a second name is “the argument from small differences.” Sextus Empiricus (*Adversus Mathematicos* VII.416) and Cicero (*Academica* II.93) preserved the answer of Chrysippus, the greatest logician of the Stoa: on approaching the boundary, he simply fell silent—ἡσυχάζειν (hēsychazein), “to keep still.” The Middle Ages dealt with insolubilia and considered vagueness an imprecision of language; the modern age tacitly expected that refining the terms would remove it. The turning point came in the twentieth century: Russell (“Vagueness,” 1923—“all language is more or less vague”), Black (1937, membership functions), Zadeh (1965, fuzzy sets), Williamson (1994, epistemicism), Fine’s supervaluationism. There is no consensus to this day—and this is a symptom: the problem lies deeper than the participants supposed.

## Consequence

Vagueness is ineliminable and ubiquitous. Law: “the age of majority,” “reasonable force,” “substantial harm”—courts draw lines where nature has not drawn them. Science: the FAO counts as forest a canopy cover from 10%, Indonesia from 30%, Côte d’Ivoire a plot five times smaller than the UN standard; the difference between the definitions amounts to 6–13% of the earth’s surface, a territory the size of China. Ethics: when an embryo becomes a person, when pain becomes unbearable. Politics: by shifting the boundaries of “poverty” and “extremism,” people change the conclusions without changing the facts. A family of one structure: the [[Bald Man Paradox|bald man]], the [[Color Spectrum|color spectrum]], wealth and poverty. The general form is the same everywhere: a binary classification is applied to a continuous reality.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the heap, the grains, a number, the operation of removing them one at a time, the inductive step. Structure: mathematical induction over the concept “heap.” No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the first defect. What is a “heap”? “Many grains”—but “many” is vague; “enough to make a mound”—circular; “from 500 on”—arbitrary, and then a single grain separates a heap from a non-heap. This is not our ignorance—it is a property of the concept: “heap” was created for practical communication and contains no threshold. The grammar betrays its nature: “a little heap,” “an enormous heap”—the concept is comparative and admits degrees. To demand an absolute boundary of a comparative concept is to demand that A be not-A ([[Identity]]). [[Excluded Middle]] is not touched: the law speaks of statements, and a statement with a vague term is undefined in a borderline case—things never get as far as the law. Signal: a binary question has been put to a graded concept.

**Domain 3—Framework Selection: is the instrument adequate to the object?** The second defect. Induction requires a strict step without exceptions and an invariant property. The step “n is a heap, so n−1 is a heap” is an approximate generalization, not a strict truth; and heap₁₀₀₀ ≠ heap₉₉₉—at each step a new object arises, whose status is relative to the context of comparison (heap₅₀₀ is a heap next to heap₁₀ and a little heap next to heap₁₀₀₀). Induction masks the substitution by calling different accumulations by one word. Signal: a precise instrument on a vague concept.

**Domain 4—Comparison:** the native element of “heap”—“more like a heap,” “less like one”—works properly; only the binary question breaks.

**Domain 5—Inference:** flawless, given the accepted premises. The problem is not in the inference.

**Domain 6—Reflection:** the absurdity of the conclusion—signal: check the concept and the instrument; return to domains 2 and 3.

## Diagnosis

**Domain of the error:** Domain 2 (clarification)—primary; Domain 3 (framework selection)—secondary. **Type:** defective—indeterminacy of a concept, vagueness. **Violated laws:** Identity—twice: in the posing of the question (an absolute boundary is demanded of a comparative concept—A is obliged to become not-A) and in the inductive step (different objects are declared “the same, only slightly smaller”). **Essence of the defect:** binary logic and precise induction are applied to a concept created as graded. On the E/R/R triad: “heap” is a Role relative to a context of comparison, not a property of an Element; the induction requires an invariant property—and receives a role.

## Why There Is No Paradox

The inductive step does not apply—it is not false but insufficiently strict: for practice it is true, for a mathematical proof it is not, and induction accepts only strict truth. The question “when exactly does a heap stop being a heap?” demands a boundary from a concept created without one—like the question “where exactly does a river become the sea?” And this is not a flaw of the concept: vagueness is a working property. A “heap” for an ant is hundreds of grains, for a human thousands, for a bulldozer tons; a “crowd” in a village is twenty people, in a megalopolis thousands: one word is calibrated by context, and a precise boundary would destroy this adaptability. Institutions confirm it: the definitions of forest differ—and each works for its own purpose; a precise boundary for a vague concept is an instrument of coordination, assigned by convention and honestly declared to be a convention.

## Objections and Replies

**Epistemicism.** “The boundary exists—we merely do not know where it is.” Reply: the concept was created without a boundary; no analysis and no consensus of speakers determines one—not from any weakness of mind, but from the way the concept is built. To ascribe a hidden threshold to “heap” is to confuse a conceptual instrument with the object it describes.

**“Classical logic does not work.”** Reply: it works—on precise concepts. The sorites shows the boundary of logic’s application, not a defect in it: a hammer is good, but it will not drive in a screw. “A number is even or odd” is true without exceptions; “a heap or not a heap” first requires the concept to be made precise.

## Lesson

**On types of concepts.** Binary concepts (“even”) and comparative ones (“heap,” “tall”) are built differently—this is a difference of functions, not a hierarchy of quality. **On the limits of formalization.** A precise definition of “heap” would not improve the concept—it would destroy its usefulness; formal logic is a powerful instrument, but not a universal one. **On “precision envy.”** Vagueness is not a failure but an adaptation: language was created for coordination in a continuous world, and vague concepts are its strong side. **On practice.** Recognize the type of a concept: do not present a vague one with a demand for precision; if precision is needed, create a technical term with a definition, and do not confuse the one with the other.

## Kin by Mechanism

[[Bald Man Paradox|The Bald Man]] (Eubulides’ second sorites—by decrease instead of accumulation), [[Color Spectrum|the Color Spectrum]] (a sorites in perception), wealth and poverty (the same scheme with money), [[Ship of Theseus]] (a neighbor by type—ambiguity instead of vagueness).

**Machine check.** In the registry of 46 the knot is recorded as `D1_Sorites`, and the diagnosis is fixed in the entry itself: the mismatch field is `InstrumentObjectMismatch`, “the instrument does not fit the object”; the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`, the count `defective_count_25`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
