---
title: "Chapter 4. Well-Quasi-Ordering as a Process over the Decidable"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/18 Процессная иерархия/04 Вполне-упорядоченность как процесс над разрешимым.md"
sourceBlob: 1310b28b4e4898c85360e08425e85947f8f7d55c
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapter 3 rolled back one “wall”—determinacy. The same technique applies to the second: to the *minimal bad sequence*, the engine of Kruskal’s tree embedding theorem.

Recall the classical construction of Nash-Williams. To prove that a certain quasi-ordering is a *well-quasi-ordering* (wqo)—that is, that every infinite sequence contains a “good pair” $i<j$ with $f(i)\preceq f(j)$—one assumes the contrary (there is a “bad” sequence without good pairs) and builds a *minimal* bad sequence, choosing at each step the least bad continuation. This choice is *dependent*, and for it classical mathematics needs the axiom of Dependent Choice, stretching along a completed tower; the full Kruskal theorem has real proof-theoretic strength. Again a “wall.”

The thesis of the chapter is the same rollback: over a *decidable* space both well-quasi-ordering itself and its method are *axiom-free processes*.

*Over the decidable, the choice of a minimal bad sequence is not an axiom but a deterministic least-successor process; and the wqo $ℕ$ itself is a well-founded descent, already a process.*

## What the Chapter Establishes and What It Does Not

*Proved exactly and without axioms*: over ℕ there is no bad sequence; every structure with a monotone ℕ-measure that reflects the order is a wqo; and the choice of a minimal bad sequence over a *decidable* order is a deterministic least-successor process, without Dependent Choice[^1].

*Not proved here (the horizon)*: the *full* Kruskal theorem for arbitrary trees—it requires Higman’s lemma over arbitrary wqo alphabets and a general minimal bad sequence along the structure of the tree, and it has real proof-theoretic strength. What is closed is the *decidable, ℕ-measurable subpart* (including trees of bounded depth via the number of descendants); the general case remains a *horizon-ascent*, graded by how decidable the space is. The least-successor device itself is standard; our contribution is to package “wqo and its method as a process over the decidable” and to localize the frontier exactly.

## The Base Rung: Over $ℕ$ There Is No Bad Sequence

The purest case is $ℕ$ with the usual order. Here well-quasi-ordering needs no choice and no tower whatsoever: it *is* well-foundedness.

Suppose a sequence $f:ℕ\toℕ$ is “bad”—not a single good pair, that is, for all $i<j$ we have $f(i)>f(j)$. Then $f$ strictly decreases: $f(0)>f(1)>\cdots$. But a strictly decreasing process on $ℕ$ must *terminate*—it cannot descend below zero. Hence there *is no* bad sequence[^2].

*“A minimal bad sequence is impossible over $ℕ$” is not an appeal to a completed tower but a **terminating descent**: that very P4 process.*

What classical mathematics sees as a subtle set-theoretic theorem is, on the base rung, simply the absence of an infinite descent—the Element side of the finitization boundary.

## Closure: An $ℕ$-Measure Gives wqo as a Process

From the base rung we climb higher—but as a process, not as an object. *Measurability in $ℕ$* suffices: if a structure has a monotone measure $h$ with values in $ℕ$ that *reflects* the order ($h(a)\le h(b)$ implies $a\preceq b$), then the structure is automatically well-quasi-ordered. The good pair is found by the same descent in $ℕ$: we apply the well-quasi-ordering of $ℕ$ to the measured sequence $h\circ f$ and carry the pair back[^3].

This is exactly the device by which the foundations obtain wqo for trees of bounded depth: the number of descendants serves as their measure, and the descent in $ℕ$ does the rest. The decidable, $ℕ$-measurable part of the “high” theorem *is reached—and reached as a process*, not as a completed object.

## The Method: Minimal Bad Choice Is a Process over the Decidable

What remains is the main thing—the Nash-Williams *method* itself, that very dependent choice for which classical mathematics needs an axiom. Let us show that over a *decidable* order it is a process.

Let the admissible continuation at each step be determined by a *decidable* condition, and let at least one continuation always exist. Then a *deterministic step* is defined: take the *least* admissible continuation. Its trajectory is the required chain—and it is built *without* Dependent Choice: the rule “the least admissible” makes each step unambiguous, and the chain *canonical* and *unique*[^4].

*The choice for which classical mathematics needs an axiom is, over a decidable order, *not* a choice but a rule: “the least admissible successor.” The chain is one, and it is a process.*

The boundary is honest: *drop* the decidability or the witnessability of the continuations, and the step ceases to be unambiguous, and then genuine Dependent Choice (or the Law of Excluded Middle) is needed. Over the decidable lies the Element side; over the undecidable, the role-limit. It is the same finitization boundary, now running through the *method*.

## E/R/R Analysis: The wqo Ascent as a System

The analysis by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is *well-founded descent*: on $ℕ$ a strictly decreasing process terminates, so there is no bad sequence. Adjoining it are the rule of transfer (a monotone $ℕ$-measure transfers wqo to a measurable structure) and the rule of choice-as-step (the *least admissible successor* over a decidable order—in place of Dependent Choice).

**Roles (L4).** The good pair plays the role of the *witness of wqo*. The least successor is a role *assigned by a rule*, not by free choice. The $ℕ$-measure has the role of the spine of the rung, along which the descent runs.

**Elements (L1 + P4).** The bearers are the terms of the sequence $f:ℕ\to(\cdots)$ and the values of the measure in $ℕ$. Under P4 the finite segments of the descent are actual; the good pair is a finitely actual witness, not the limit of a ready tower.

**Well-formedness check.** Descent, transfer, and choice-as-step are Rules; the witness-pair, the least successor, and the $ℕ$-measure are Roles; the terms and values are Elements; there are no overlaps. There is no self-application: the rule of choice stands above the chain and is not a term of it.

**What the analysis yields.** It shows that “is the axiom of Choice needed for wqo?” is formulated too coarsely. Over the decidable it is not: both the theorem (wqo is transferred by an $ℕ$-measure) and the method (minimal bad choice) are processes. The completed tower and Dependent Choice were packaging; what remains necessary is only what lies over the *undecidable*—an honest horizon.

Two “walls”—determinacy and wqo—have been rolled back by one device: the bottom is reached as a process, nonconstructivity is localized, the height is declared a horizon. In the concluding chapter we will tie all the stages into one hierarchy and see what stitches them into a single process ascent.

---

[^1]: The file `WqoProcessDecidable`; machine-checked, 0 axioms. It relies on the basic `wqo_nat_le` (the well-quasi-ordering of ℕ) and on the axiom-free dependent choice over the decidable, `CountableDependentChoiceFree`.
[^2]: `no_bad_seq_nat`: over ℕ there exists no bad sequence. A direct consequence of `wqo_nat_le`, proved by well-founded descent on $f(0)$. 0 axioms.
[^3]: `wqo_pullback_nat`: a monotone ℕ-measure that reflects the order implies wqo. The good pair is the image of the pair found by the descent `wqo_nat_le`. 0 axioms.
[^4]: `minimal_selection_is_process`: over a decidable total relation the least-successor trajectory is a chain, and each step is minimal—deterministically, without Dependent Choice. It relies on `CountableDependentChoiceFree`. 0 axioms.

---

Part: [[18 Process Hierarchy|Part XVIII. The Process Hierarchy]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/03 Determinacy Up the Hierarchy|Chapter 3. Determinacy Up the Hierarchy]] · [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/05 Synthesis the Hierarchy Is a Process|Chapter 5. Synthesis: The Hierarchy Is a Process]] →
