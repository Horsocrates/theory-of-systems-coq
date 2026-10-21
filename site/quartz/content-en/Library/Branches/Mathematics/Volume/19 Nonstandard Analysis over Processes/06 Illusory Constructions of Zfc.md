---
title: "Chapter 6. Illusory Constructions of ZFC"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/19 Нестандартный анализ над процессами/06 Иллюзорные конструкции ZFC.md"
sourceBlob: 485d102d9fce5f5b7bfb665773d0d70084e4d285
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapters 1–5 went through the real content of nonstandard analysis: process infinitesimals, the shadow, the ring, the ultrafilter, the boundary as invertibility. But “beyond the boundary” there also live constructions of ZFC of another kind—those that exist only inside the formalism, through the Axiom of Choice, without a computable referent. Since ToS is ontological, it must deliver an honest verdict on them.

{
*The flagship: a three-valued machine verdict—**Element core / role-limit instrument / illusory**. The Element core is expressible by processes (0 choice, there is a witness); the role-limit instrument is nonconstructive but *removable* scaffolding that delivers something (conservativity); the illusory is a ZFC phantom without an Element referent, delivering neither a witness nor removable formwork. The flagship anchor is Banach–Tarski: the doubling of the ball is incompatible with any nonzero Element measure ($\mu=2\mu\Rightarrow\mu=0$).*}

And two clarifications at once. The first is terminological: “illusory” here is a *technical term* of ToS, not the everyday “does not exist.” A construction can be a theorem of ZFC and yet have no Element referent in the process ontology; this does **not** mean inconsistency or falsity inside ZFC. The second: we **do not assert** anything illusory (we do not postulate the existence of a Banach–Tarski decomposition)—we only classify, and for the flagship we prove incompatibility with Element preservation.

## Three Classes

Every construction “beyond the boundary” receives exactly one of three statuses[^1]:

{

- **Element core** ($\neg$AC, there is a witness): the $\delta$-process, the shadow of a convergent process, the derivative of a polynomial—all built in Chapters 1–2, 0 axioms[^2];
- **role-limit instrument** (AC, but removable scaffolding): the free ultrafilter, $^{*}ℝ$-as-a-field—nonconstructive but *conservative* (in the metatheoretical sense of Nelson: a standard consequence obtained through NSA scaffolding has a standard proof), hence removable, and they *deliver* something[^3];
- **illusory** (AC, no witness, not scaffolding): the Hamel basis, the Vitali set, a well-ordering of $ℝ$, Banach–Tarski—pure ZFC phantoms[^4].

}

*The key distinction is the illusory versus the role-limit instrument: scaffolding is **removable and delivers something** (an Element consequence through conservativity); a phantom delivers **neither an Element witness nor removable formwork** for a process result—it is only an “object” that does not exist on the Element side (which does not prevent it from having consequences *inside* ZFC). The ultrafilter (Chapter 4) is scaffolding; Banach–Tarski is a phantom.*

## The Flagship: Banach–Tarski Is Incompatible with an Element Measure

Among the illusory there is one with a proved theorem. The Banach–Tarski paradox *claims*: the unit ball (measure $\mu$) is cut into finitely many pieces that are reassembled by rigid motions into *two* unit balls (measure $2\mu$). Any nonzero, motion-invariant, finitely additive Element measure **rules this out**: $\mu=\mu+\mu$ implies $\mu=0$[^5].

Hence the pieces cannot be at the same time Element-describable, measurable by this measure, and preserving of a nonzero motion-invariant finitely additive measure—they have no Element referent *as measurable geometric pieces*. This is *why* Banach–Tarski is illusory on the Element side: it is incompatible with the very preservation that an Element measure carries.

*Honestly about what is proved. We do **not** claim “Banach–Tarski is false in ZFC”—in ZFC$+$AC it is a theorem. We do **not** postulate the decomposition. What is proved is something else: *there is no describable, Element-measurable decomposition*—the doubling is incompatible with a nonzero Element measure. The dispelling takes place at the level of the referent, not of truth-value in ZFC.*

## What It Means to “Dispel”

The Vitali set (non-measurable), the Hamel basis, a well-ordering of $ℝ$—the same story: each requires full choice and has no definable witness (the classical AC-dependence is cited, not reproved). But their phantomness is *of different types*: for Vitali and Banach–Tarski, through a break with measure; for the Hamel basis, through the absence of a canonical process witness; for a well-ordering of $ℝ$, through the absence of an Element order of this type. ToS names them phantoms and dispels them—but carefully.

To dispel is not to “refute an axiom.” Free choice is consistent and independent. To dispel means this: the Element-describable sets of this block have a constructive measurability status, while non-measurability is *optional*—it arises only where an object is introduced by pure choice without such a process. In the Solovay model (ZF$+$DC), under the metatheoretic assumption that an inaccessible cardinal exists, all sets of *real numbers* are Lebesgue measurable—hence non-measurability is not an Element necessity but a consequence of added choice. A phantom is exactly what choice alone adds, without an Element referent; ToS holds to the Element side and honestly marks the rest as an artifact of the formal system.

*The registry is a synthesis, not new theorems (except for the Banach–Tarski anchor). Its value is honesty: every construction “beyond the boundary” receives an explicit status, and the boundary “real / removable scaffolding / phantom” is drawn by machine.*

## E/R/R Analysis: The Verdict Registry as a System

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the three-valued verdict: illusory $=$ AC $\wedge$ no witness $\wedge$ not scaffolding; role-limit instrument $=$ AC $\wedge$ removable scaffolding; Element core $=$ $\neg$AC $\wedge$ a witness. The flagship rule: $\mu=2\mu\Rightarrow\mu=0$.

**Roles (L4).** A construction is a role-candidate; the verdict is a role-status; needs-AC, the witness, and removability are role-diagnostics; the Element measure is the role-preservation that cuts off the phantom.

{
**Elements (L1 + P4).** The bearers are the enumeration of concrete constructions, Boolean diagnostics, the $ℚ$-measure. Under P4 the Element core (processes) and the diagnostics themselves are actual; the illusory “objects” (the Banach–Tarski pieces, the non-measurable Vitali set) are exactly what P4 does not actualize.}

**Well-formedness check.** The rule is the verdict; the roles are the status and the diagnostics; the elements are the constructions and the measure; there are no overlaps. Banach–Tarski as a system: the “pieces” (Elements) are declared measure-preserving (Roles), but Element preservation rules this out (Rules) $\Rightarrow$ pieces without a referent $\Rightarrow$ a phantom system.

**What the analysis yields.** It separates the real (expressible by processes) from removable scaffolding and from phantoms—and does so by machine, with one anchor theorem (Banach–Tarski). The illusory is named honestly: consistent, but without an Element referent. It remains to bring the whole part into one map.

All the constructions “beyond the boundary” have received a verdict. The concluding chapter of the part gives a single map: the real content of nonstandard analysis is entirely processual (Element $+$ removable scaffolding by conservativity), while in the ontology of ToS the ZFC phantoms stand to the side of Element mathematics—they are formal objects of the chosen set theory, but not senior to the process content.

---

[^1]: `verdict` (in `IllusoryConstructions`) on the enumeration `Construction`; totality `verdict_total`, mutual exclusivity `element_not_illusory`. Machine-checked, 0 axioms.
[^2]: `element_core_props`: ElementCore implies $\neg$`needs_AC` and `has_element_witness`; the witnesses are `GermInfinitesimal`, `StandardPart`, `deriv_sq`. Machine-checked, 0 axioms.
[^3]: `role_limit_scaffold`: RoleLimitTool implies `is_conservative_scaffold` and `needs_AC`; the noncanonicity of the ultrafilter is proved in `UltrafilterRoleLimit` (Chapter 4). Machine-checked, 0 axioms.
[^4]: `illusory_hallmark`: Illusory implies `needs_AC`, $\neg$`has_element_witness`, $\neg$`is_conservative_scaffold`. Machine-checked, 0 axioms.
[^5]: `banach_tarski_contradicts_measure`: $\mu=p_1+p_2$, $p_1=\mu$, $p_2=\mu$ imply $\mu=0$; the summary theorem `illusory_constructions_summary` (8 Qed). Machine-checked, 0 axioms.

---

Part: [[19 Nonstandard Analysis over Processes|Part XIX. Nonstandard Analysis over Processes]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/05 The Boundary Is Invertibility One Seed Negb|Chapter 5. The Boundary Is Invertibility; One Seed negb]] · [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/07 Synthesis Map of Mathematics Beyond the Boundary|Chapter 7. Synthesis: A Map of Mathematics beyond the Boundary]] →
