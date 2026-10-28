---
title: "Masked Man"
lang: en
translationOf: "Библиотека/Направления/Архитектура Рассуждения/Каталог парадоксов/Дефектные парадоксы/Парадокс замаскированного.md"
sourceBlob: 6582d37a369dbc177054d80495038e4de795d438
translated: 2026-10-20
status: draft
description: "“To know” is an intensional context"
---

**D.19** · [[Defective Paradoxes|defective paradox]] · subtype: Error in Reasoning

**Essence of the error.** “To know” is an intensional context

## Exact Formulation

“Do you know this man under the veil?” “No.” “But he is your father. So you do not know your own father.” The general form: you know A; A is B; you do not know B—so you both know and do not know one and the same person. The ancient version is the “Electra”: she knows her brother Orestes and does not know the veiled stranger, who is Orestes himself.

## Origin

Eubulides of Miletus—the “Electra” and the “Veiled Figure” in Diogenes Laertius’ list of seven tricks, beside the [[Liar Paradox|liar]] and the [[Horned Man|horned man]]. Of all Eubulides’ knots, this one has the most theoretical progeny. Frege (“On Sense and Reference,” 1892) built a semantics on the same mechanics: “the morning star” and “the evening star” name one Venus, but their identity is an astronomical discovery, not a truism—so names carry, over and above the object, also a *sense*, a mode of presentation. Quine gave the phenomenon a name—referential opacity: the contexts “knows,” “believes,” “seeks” do not let through the substitution of coreferential names. Epistemic logic formalized the separation strictly (knowledge de dicto and de re). Metaphysics got its share too: the classic objection to Descartes’ argument “I can doubt the body, I cannot doubt thought—therefore thought is not the body” consists precisely in this: it is the masked man in philosophical dress.

## Consequence

The knot bequeathed to logic the boundary of the law of substitution. Identical things are indiscernible—but “knows,” “believes,” “wants,” “seeks” speak not of the bare thing but of the thing *under a description*: from “I know A” and “A = B” it does not follow that “I know B” as long as the identity A = B itself is not known to the knower. The practical field is boundless: a witness identifies “the man in the hood” without identifying his neighbor; a debtor “seeks his creditor” without seeking the man standing next to him; half a century of disputes over whether a subject “knew”—in law, in intelligence, in epistemology—comes up against the index of description. And the main lesson for metaphysics: a difference in *how* something is given to thought does not prove a difference in *what* is given—an antidote to a whole class of quick proofs of non-identity.

## Domain Analysis

**Domain 1—Recognition: what is given?** Components: the knower, one person under two descriptions (“father,” “the man under the veil”), the predicate “to know,” the identity of the descriptions. Signal: one predicate runs between different givens.

**Domain 2—Clarification: what do the terms mean?** Here is the defect. “To know” splits in two: to be acquainted with a person—and to recognize him under a given guise. “I do not know the veiled man” means “I do not recognize who is under the veil,” not “I am not acquainted with the one under it.” Moreover, the inference tacitly uses the substitution of B for A inside “knows”—and this is legitimate only under the premise “the knower knows that A = B,” which is absent: ignorance of this identity is the whole scene. Signal: an intensional context is taken as transparent.

**Domain 3—Framework Selection:** a second layer: extensional logic is an instrument for contexts where only the object matters; here we have a context of attitude, where the mode of presentation matters. The instrument does not fit the object.

**Domain 4—Comparison:** not engaged.

**Domain 5—Inference:** the form of substitution is flawless—in extensional contexts; here it has been carried over without warrant. The problem is in the transfer, not in the form.

**Domain 6—Reflection:** “knows and does not know”—signal: index by description; return to domain 2.

## Diagnosis

**Domain of the error:** Domain 2 (clarification). **Type:** defective—error in reasoning: the substitution of identicals in an intensional context. **Violated laws:** [[Identity]]—subtly: the law about things is intact; what is broken is the handling of it—the identity of things is passed off as the identity of representations, whereas “to know” concerns the representation; [[Non-Contradiction]] is not touched at all: “knows under one description” and “does not know under another” are different relations, and there is no contradiction. **Essence of the defect:** knowledge takes an object under a Role (a description), while the inference substitutes the Role, keeping the Element—and passes off the change of role as a contradiction in knowledge. On the E/R/R triad, exactly this.

## Why There Is No Paradox

Indexing by description does all the work. Electra is acquainted with Orestes—and does not recognize Orestes under the veil: “knows(the brother)” and “does not know(the veiled man)” are two relations to two givens of one person; they can be added up into a contradiction only by erasing the indices. The strict form of the separation: inside “knows,” substitution by A = B requires the premise “knows that A = B”—here it is not merely absent; its absence constitutes the plot: recognizing the father under the veil would be a *discovery*, like Hesperus = Phosphorus for the astronomer. For the same reason the metaphysical version falls too: “I can doubt X, I cannot doubt Y” describes givens to thought, not things—a difference of descriptions does not prove a difference of things. Our own epistemology fixes the ground formally: knowledge is defined on representations, not on bare objects (the type Representation and the knowledge link in src/foundation/KnowledgeTruthLadder.v—knowledge lives on the attunement of a representation, and that is why it is indexed by it).

## Lesson

**On attitudes.** “To know,” “to believe,” “to seek” are relations to a representation; substituting names inside them is legitimate only when the identity is known. **On apparent contradictions.** “Knows and does not know”—check the indices: most often these are two relations, not one contradictory one. **On quick proofs of non-identity.** A difference of givens does not entail a difference of things: before separating entities, check whether you are not separating descriptions.

## Kin by Mechanism

[[Horned Man|The Horned Man]] (a neighbor in Eubulides’ arsenal: there the contraband is in the presupposition, here in the substitution), [[Teleportation Paradox]] (the criterion for recognizing a person—the ontological side of the same question), the pair “morning star / evening star” (the descendant theory in Frege), the objection to Cartesian dualism (the metaphysical dress of the knot), [[Liar Paradox|the Liar]] (Eubulides’ family—but there it is a genuine structural knot).

**Machine check.** In the registry of 46 it is `D19_MaskedMan`: the field `ConceptualAmbiguity`, the level `L2_Operations`, the category “defective,” laying open by rejecting the premise (`defective_46_requires_rejection`, `all_46_dissolvable`—ParadoxDissolution.v). The support of the ground is knowledge as a relation to a representation: src/foundation/KnowledgeTruthLadder.v. Map: [[Formalization]].

---

Category: [[Defective Paradoxes]] · Catalog: [[Paradox Catalog]] · Concept: [[Paradox]]
