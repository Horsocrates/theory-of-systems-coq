---
title: "Chapter 4. Construct or Name"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/20 Заключительный синтез/04 Построить или назвать.md"
sourceBlob: 4fdad872847951cb5e5e2b497091d0a13a8db5d0
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Three chapters have drawn the finitization boundary and settled into it. The first fixed the line and its coincidence with the boundary of constructivity; the second refined the far side as an unbounded process, not a cutoff; the third compressed the near side into one $2\times2$ matrix with one gate. The boundary *sorts* objects.

But the whole volume poses the question more sharply—*ontologically*. Of everything that mathematics produces, what does the theory genuinely **construct**—with a process witness—and what does it merely **name**: a consistent object of the chosen set theory that has no Element referent? The boundary of Chapters 1–3 spoke of objects *given by a rule of generation*; here we sort by what the theory *does* with them.

{
*The flagship: the three-valued verdict—at the level of the whole book. The **Element core** (constructs: there is a process witness, 0 choice); the **role-limit instrument** (holds as removable scaffolding: nonconstructive but conservative—hence removable, and it delivers something); the **illusory** (merely names: consistent in ZFC, but without an Element referent and without the role of scaffolding). There is one anchor theorem—Banach–Tarski.*}

And the frame at once: we **postulate nothing illusory as an Element**; we sort the book, and for the flagship we prove incompatibility with an Element measure.

## What the Chapter Establishes and What It Does Not

{
Honesty is especially needed here. The verdict is a *registry-synthesis* over the whole book plus *one* anchor theorem (Banach–Tarski). It does **not** reprove the classical AC-dependence of the Hamel basis, the Vitali set, a well-ordering of $ℝ$—it is *cited*. And “illusory” here is a *technical term* of ToS: an object can be a theorem of ZFC and yet have no Element referent in the process ontology; this is **not** a statement about inconsistency or falsity inside ZFC.}

As for the side “constructs”: the survey below *cites* the flagship of each part, and the thesis “most of the volume is Element core” is an *observation* over machine-checked instances, not a metatheorem[^1]. The level of the chapter is an honest sorting backed by a checked registry, not a new claim.

## Three Classes: To Construct, to Hold as Scaffolding, to Name

Every construction *in the chapter’s registry* receives exactly one of three statuses[^2].

**Element core (constructs).** There is a process witness, 0 choice. The theory *constructs* the object; it is actualized at each finite stage. This is a terminating process or a directly presentable construction.

**role-limit instrument (holds as scaffolding).** A classical principle is needed—choice, an ultrafilter, or the Law of Excluded Middle (these are *different* levels of price), but the construction is *conservative*—in the corresponding metatheoretical sense: for standard statements of the language under consideration, a standard consequence obtained through it has a standard proof (Nelson). Hence the scaffolding is *removable* and at the same time *delivers* an Element consequence. The free ultrafilter, the field $^{*}ℝ$ (Part XIX).

**illusory (names).** Choice is needed, there is *no* witness, and it is *not* removable scaffolding—it delivers neither an Element witness nor removable formwork for the class of Element results under consideration (although in ZFC itself it may have consequences). The Hamel basis, the Vitali set, a well-ordering of $ℝ$, Banach–Tarski.

*The key distinction constructing $/$ naming: scaffolding is **removable and delivers something**; a phantom delivers neither an Element witness nor removable formwork—although in ZFC itself it may have consequences.*

In the registry of set-theoretic assumptions, the power set and choice are assigned to the same role-limit side[^3]—that is, the very ladder on which the phantoms live is marked as the side of scaffolding, not of the Element.

## What Volume II Constructs

The main thing is positive: most of the volume is *Element core*, built with a process witness. Let us go through the book.

- A number is a position-role, $\sqrt2$ is a process of approximations, not a ready point (Part III)[^4];
- $ℝ$ is a Cauchy process, not a completed object (Part IV and beyond);
- the Galois group of $ℚ[\sqrt2,\sqrt3]$ is a process-tower of extensions with four distinct automorphisms (Part XI)[^5];
- a manifold is a process of charts (Part XII);
- the Riemann hypothesis is a fixed point of the reflection of the critical strip (Part XIII), *structurally*: the reflection itself is an isometry, not a contraction[^6];
- computation is finitization; halting is a role-limit (the part on computation)[^7];
- a function is a process, not a ready graph (Part XVI);
- the calculus of the nonstandard is the shadow $\mathrm{st}$ over germs (Part XIX)[^8].

Each item has a checked Element fragment or a structural anchor in its part—but not each is a full classical theorem in the traditional sense (for the Riemann hypothesis this is a *structural* fragment, not a proof of RH). This is the main body of the volume: not *named* but **constructed**.

## What Volume II Merely Names; the Flagship Banach–Tarski

{
Now the side “names.” The Hamel basis, the Vitali set, a well-ordering of $ℝ$—each requires full choice, has no definable witness (the classical AC-dependence is *cited*, not reproved), and does not serve as removable formwork: it delivers no Element witness. Their phantomness, moreover, is *of different types*: Vitali and Banach–Tarski break the measuring referent; the Hamel basis has no canonical process witness; a well-ordering of $ℝ$ sets an order made by choice, without an Element procedure. The theory *places* them as artifacts of the chosen set theory—it removes the claim to an Element referent, which means “there is no describable, Element-measurable witness,” not “false in ZFC.”}

The flagship is the only illusory construction with a proved theorem. The Banach–Tarski paradox *claims*: a ball is cut into finitely many pieces and reassembled by rigid motions into *two* balls. If a nonzero, motion-invariant, finitely additive Element measure were defined *on all the pieces of the decomposition*, the doubling would give $\mu=\mu+\mu$, whence $\mu=0$—a contradiction[^9]. Hence the pieces have no Element referent *as measurable geometric pieces*—that is *why* the paradox is illusory on the Element side. Honestly: we do **not** claim “Banach–Tarski is false in ZFC” (in ZFC$+$AC it is a theorem); the dispelling takes place at the level of the referent.

*This verdict was already at work in the nonstandard part (Chapter 6 of Part XIX, the registry of constructions “beyond the boundary”); here it is a **book-wide** sorting: removable scaffolding versus phantom, over everything the volume has produced.*

## E/R/R Analysis: The Verdict as a System

The verdict itself is a *system* in the sense of ToS; let us analyze it by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the three-valued verdict {Element core / role-limit / illusory} by the criterion “construct or name”: is there a process witness; is the scaffolding removable, and does it deliver; neither the one nor the other. The flagship rule: $\mu=2\mu\Rightarrow\mu=0$.

**Roles (L4).** Status-of-construction, status-of-scaffolding, status-of-name—three roles of each construction; the role-diagnostics are whether choice is needed, whether there is a witness, and removability; the Element measure is the role-preservation that cuts off the phantom.

**Elements (L1 + P4).** The bearers are the concrete constructions of the book and the $ℚ$-measure of the flagship. Under P4 the Element core (processes) and the diagnostics are actual; the illusory “objects” (the Banach–Tarski pieces, the non-measurable Vitali set) are exactly what P4 does not actualize.

**Well-formedness check.** In the chapter’s finite registry the statuses are given as disjoint—each construction receives exactly one; there are no overlaps. The verdict as a system: the “pieces” (Elements) are declared measure-preserving (Roles), but Element preservation rules this out (Rules) $\Rightarrow$ pieces without a referent $\Rightarrow$ a phantom system.

**What the analysis yields.** It separates the constructed (process) from removable scaffolding (role-limit, conservativity) and from the named phantom (the illusory)—over the whole book, with one anchor theorem. And it shows where the ontological seam of the volume runs: not between the “useful” and the “useless” but between what the theory *constructs* and what it merely *names*.

The sorting is done. It remains to show the positive side as a whole: the next chapter draws a single map—every object of the volume, relocated onto processes, from number to nonstandard analysis.

---

[^1]: Each cited result is checked in its own part; the Element side is 0-axiom, as Chapter 1 showed (the contrast between the constructive core and the classically loaded role-limit side). The universality of the form of the verdict is a matter of interpretation, not a proved universal theorem.
[^2]: The three-valued verdict is a function on the enumeration of constructions (`illusory_constructions_summary`, 8 Qed): illusory $\Rightarrow$ choice needed, no witness, not scaffolding; Element core $\Rightarrow$ 0 choice, a witness exists; role-limit $\Rightarrow$ conservative scaffolding. Machine-checked, 0 axioms.
[^3]: `zfc_axiom_ledger` (in `ZFCAxiomLedger`, 10 Qed): the power set and choice are placed as role-limit steps. Machine-checked, 0 axioms.
[^4]: $\sqrt2$ does not reach a rational value—`no_rational_sqrt2` (`analysis/Sqrt2Irrational`). This is a proof of *non-termination*, constructive; the Element side is 0-axiom.
[^5]: `galois_group_four_distinct` (`algebra/`): $V_4$ as four distinct automorphisms; $\overline{ℚ}$ is given as an ascending process, not as a ready wall.
[^6]: `RH_critical_strip_symmetric`, `reflect_zero_nontrivial` (`zeta/ContractionZeros`). This is a *structural* reading (a zero formally $=$ Cauchy $\wedge$ critical strip); the analytic functional equation is the horizon (Chapter 6).
[^7]: The file `cs/HaltingRoleLimit` (13 Qed, 0 axioms): the same diagonal as in uncountability.
[^8]: `nonstandard_synthesis` (`nonstandard/`, 10 Qed): one root $\to$ three forms of the gap. Machine-checked, 0 axioms.
[^9]: `banach_tarski_contradicts_measure` (the summary theorem `illusory_constructions_summary`): $\mu=p_1+p_2$, $p_1=\mu$, $p_2=\mu$ imply $\mu=0$. Machine-checked, 0 axioms.

---

Part: [[20 Final Synthesis|Part XX. The Final Synthesis]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/20 Final Synthesis/03 Reduction Atlas|Chapter 3. The Reduction Atlas]] · [[Library/Branches/Mathematics/Volume/20 Final Synthesis/05 Map of Volume II Everything Is a Process|Chapter 5. The Map of Volume II: Everything Is a Process]] →
