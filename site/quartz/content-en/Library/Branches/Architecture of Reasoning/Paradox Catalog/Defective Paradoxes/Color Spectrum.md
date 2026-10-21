---
title: "Color Spectrum Paradox"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс цветового спектра.md"
sourceBlob: b80fb9b5e8cad3b3a924168fff70f3f7d8744b44
translated: 2026-10-20
status: draft
description: "Color categories are conventions, not discrete entities"
---

**D.3** · [[Defective Paradoxes|defective paradox]] · subtype: Indeterminacy of a Concept

**Essence of the error.** Color categories are conventions, not discrete entities

## Exact Formulation

The spectrum is continuous: from red to orange runs a smooth series of shades in which neighbors are indistinguishable to the eye. If shade n is red, and shade n+1 is indistinguishable from it, then it too is red. Step by step, orange turns out to be red, then yellow. Where did red stop being red? Every answer names a boundary that is not in the spectrum.

## Origin

Eubulides’ sorites family in new material: instead of a count of grains, the continuity of perception. The modern form grew up in twentieth-century philosophy of perception as the “phenomenal sorites”: Crispin Wright called the key property tolerance—“red” tolerates an imperceptible change, and this tolerance is incompatible with the precise logic of a label. The second root is the linguistics of color: Berlin and Kay (*Basic Color Terms*, 1969) showed that languages cut the single spectrum differently—from two to eleven or more basic color words; Russian keeps *goluboy* (light blue) and *siniy* (dark blue) as separate basic categories where English makes do with one *blue*. Color categories are conventions of culture laid over a continuous physics.

## Consequence

The knot lays bare two layers that the sorites on sand leaves fused. Physics is continuous: wavelength is a continuum without seams. Categories are discrete: the names of colors are a finite set of labels, and their boundaries are assigned by language, not by the spectrum. Beyond that, the spectrum makes its own contribution to logic: pairwise indistinguishability is not transitive—a chain of pairwise indistinguishable steps connects clearly distinguishable ends; the relation “indistinguishable” behaves differently from the relation “the same.” The practical progeny: tolerances in the production and printing of color, disputes over color trademarks, the calibration of instruments—everywhere the boundary is assigned by convention and fixed in a document.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: a continuous spectrum, a series of shades, the pairwise indistinguishability of neighbors, the names of colors. No signal yet.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “Red” is a category of perception and language: a convention with a vague edge, laid over a continuum. Languages have different boundaries (*goluboy*/*siniy* versus *blue*)—so the boundary is not discovered in the spectrum but assigned by the speakers. Signal: a discrete label on a continuous quantity.

**Domain 3—Framework Selection:** the second defect. The step “indistinguishable—therefore the same color” promotes indistinguishability to identity: indistinguishability is pairwise and not transitive, identity is transitive ([[Identity]])—the step substitutes one relation for another. Precise logic is applied to a tolerant predicate.

**Domain 4—Comparison:** the pairwise comparison of neighbors is honest (“indistinguishable”); what breaks is the transfer of the conclusion along the chain.

**Domain 5—Inference:** flawless, given the accepted step. The problem is not in the inference.

**Domain 6—Reflection:** yellow “turned out” to be red—return to domains 2 and 3.

## Diagnosis

**Domain of the error:** Domain 2 (clarification); Domain 3—secondary. **Type:** defective—indeterminacy of a concept, the vagueness of a category. **Violated laws:** Identity—indistinguishability (not transitive) is passed off as identity (transitive); a boundary is demanded of a conventional category as if it were a fact of the world. **Essence of the defect:** a discrete label on a continuum, plus a substitution of the relation in the step. On the E/R/R triad: the name of a color is a Role assigned by convention over a continuous Element (wavelength); the Rule of transfer “indistinguishable → the same” is wrongly declared transitive.

## Why There Is No Paradox

Two moves, and both are honest. The first is to acknowledge the convention: the boundary of “red” is assigned by language and purpose, and languages assign it differently; the question “where does red end?” is answered by pointing to a convention (a standard, a scale, a dictionary), not by discovering a hidden fact. The second is to expose the step: from “a is indistinguishable from b” and “b is indistinguishable from c” it does not follow that “a is indistinguishable from c”—indistinguishability is held by a threshold of sensitivity, and the threshold accumulates what each step hides; a chain of legitimate pairwise comparisons does not carry a label along the spectrum. Physics needs no boundaries; labels do—and mature practice assigns them explicitly: coordinates in a color space, a number in a catalog, a tolerance in a contract.

## Lesson

**On the two layers.** A continuous quantity and a discrete name are different layers; do not confuse the discovery of a fact with the assignment of a convention. **On non-transitivity.** Indistinguishability is not identity: a threshold of sensitivity is a property of the observer and the instrument, not a seam in the world. **On the relativity of categories.** Languages cut the spectrum differently, and each cut works: the category is conventional, reality is one—the dispute about the “real” boundary of red has no subject.

## Kin by Mechanism

[[Sorites Paradox|Sorites]] (the canonical form—the full analysis is there), [[Bald Man Paradox|the Bald Man]] (a sorites by decrease), [[Ship of Theseus]] (the category “the same” without a criterion—ambiguity next to vagueness).

**Machine check.** In the registry of 46 it is `D3_ColorSpectrum`, with the diagnosis field `InstrumentObjectMismatch` (“the instrument does not fit the object”); the category “defective,” resolution by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
