---
title: "Chapter 1. The Finitization Boundary"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/20 Заключительный синтез/01 Граница финитизации.md"
sourceBlob: 61ae54d01d156fac6a78e9330f42dc9885e70337
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

One line runs through the whole of the present volume. In Part III a number turned out to be not a pre-existing object but a *position-role*, and the square root of two not a ready point but a *process* of approximations[^1]. In Part IV the principle P4 fixed this very stance: *infinity is a property of processes, not of completed objects*, and uncountability turned out to be a *rule about processes*, not a property of a ready set.

The present chapter closes this line with one observation. Wherever we asked “does the process terminate?”, the answer split in two *with no middle*: the process either *closes* in finitely many steps—and then it has a terminus, a finitely actual Element—or *provably never closes*—and then its “value” remains only a role-limit, never actualized over ℚ. This dividing line we call the *finitization boundary*.

*The finitization boundary is, in the instances considered, one line running through ontology (Element versus role-limit), logic (constructive versus classical), and spectrum (discrete versus continuous).*

The thesis of the chapter is twofold. First, the scattered demarcations of the present volume and its applications are *one* principle, not a list of independent results. Second—and this is the main point—in the instances considered the finitization boundary coincides with the boundary of *axiom price*: the Element side (and the very non-termination of processes) is provable without axioms, while the classical layer enters only where the talk is of a *completed* continuum object. This is a working map by instances, not a proved identity.

## What the Chapter Establishes and What It Does Not

Honesty is needed here from the very start. The finitization boundary in the form in which it is asserted below is not a new universal theorem deriving all demarcations from one formula. It is an *observation over concrete cases*: in a number of areas—the kinematics of finite rotations, rational quantum information, finite-order rotations of space, the operator limit, the spectrum, the continuum—one and the same line runs through, and each individual case is *machine-checked*[^2]. The universality of the form is a matter of interpretation, not a proved metatheorem, and it is called just that.

What is proved exactly are the *instances*: concrete role-limits (the impossibility of a rational value for $\sqrt2,\sqrt3,\sqrt5$), concrete closures (finite rotation groups), a concrete operator no-go, a concrete process non-convergence. What remains a matter of interpretation is the *unity* of the form and its coincidence with the boundary of constructivity; the latter rests on an honest audit of the axiom price of each instance, not on one general theorem.

## The Terminating Process and Its Role-Limit

Take any object given by a *rule of generation*—a sequence of rational approximations, a step taking a state to the next. By the principle P4 such an object is a *process*, and at each finite stage it gives a finitely actual result—a rational number, an Element. The question that divides everything is one: *does the process close*?

**A terminating process** closes in finitely many steps. Its terminus is an Element: the rational value at which the process arrives and stops. Here the Element is not a primary category but precisely the *terminus* of a terminated process; the process is primary, the Element derived.

**A non-terminating process** provably does not close. It has no terminus-Element; its “value” remains a *role-limit*—a role that the process approaches but that no finite stage fills with an Element. It is important to name this directly: the role-limit is a *positive* object (a non-terminating process), not “the absence of an Element.” To define it through a lack is a category mistake; it is a process that does not close.

*In each instance analyzed, one of the two sides is proved*—either a finite terminus-Element is presented, or it is proved that there can be no terminus (a role-limit). We do not assert a universal algorithm deciding this dichotomy *for all* processes: “there is nothing between them” means not a general decider but the absence of a third *status* once a concrete instance has already been classified.

Hence one spurious question falls away at once. “Is $X$ infinite?”, “Is $X$ irrational?”—in the P4 ontology these are not primary questions. $X$ *is* a process; of a process it is meaningful to ask only whether it closes. The “irrationality” of $\sqrt2$ is neither a defect nor a property of a ready object but the correct P4 status of a process of approximations: it does not terminate in an Element. The statement of the impossibility of a rational value is a proof precisely of *non-termination*, not of a “flaw.”

## One Boundary—Many Areas

The strength of the observation is that one and the same line runs through areas that look incompatible. Each has its own *criterion of termination*, but the form of the division is one—a dichotomy without a middle.

| **Area** | **Element side** | **Role-limit side** |
|---|---|---|
| Kinematics of rotations | finite order (a closed group) | aperiodic rotation ($\sqrt2,\sqrt3$) |
| Rational information | probability is rational | amplitude normalization ($\sqrt2$) |
| Higher dimension | orders $\{1,2,3,4,6\}$ | icosahedron, order 5 ($\sqrt5$) |
| Operator limit | finite-dimensional operators | canonical commutator |
| Spectrum | discrete (enumerable) | continuum (a perfect subset) |
| Continuum | rational approximations | the process $\sqrt2$, the whole interval |

The kinematics of finite rotations gives the purest case. A rational *orthogonal* rotation of the plane of finite order—that is, a rational point $(\cos\theta,\sin\theta)\inℚ^2$ on the circle that returns to the initial one after finitely many repetitions—turns out to be exactly one of four: the identity, the half-turn, and the two quarter-turns[^3]. Every other rational rotation *does not close*—for example, the rotation corresponding to the $3$–$4$–$5$ triangle never returns to the start. It closes or it does not—and nothing in between.

The same boundary in *rational quantum information*[^4] runs along the rule of passage from amplitude to probability: the “irrational” normalization lives only in the unobservable layer of amplitudes, while the observable quantity—probability—remains a rational Element. In the operator area the finite-dimensional analogue of the canonical commutator $[A,B]=c\cdot I$ forces $c=0$: a nonzero “constant” has no finite realization and is a role-limit[^5]. And the spectral dichotomy—“the spectrum is discrete or continuous, and there is no intermediate cardinality”[^6]—is *not* a separate fact but the same “there is nothing between them.” The finitization boundary *is* a dichotomy, everywhere; its spectral guise is only the sharpest form.

## Irrationals as Obstructions: $\sqrt2,\sqrt3,\sqrt5$

The boundary is concentrated in a few concrete role-limits. These are quadratic irrationals—but in our ontology they are not “ready numbers” but non-terminating processes; and each is an obstruction to a quite definite *finite structure*.

**$\sqrt2$** locks the rotation by $45^\circ$: its process of approximations (the converging sides of isosceles Pythagorean triangles) improves forever but does not reach a rational value[^7]—therefore the corresponding rotation does not close.

**$\sqrt3$** locks the $60^\circ$ point. Here one sees exactly how a process becomes an obstruction: the cosine of $60^\circ$ is *rational* (equal to one half), but the sine is $\sqrt3/2$—a non-terminating process[^8]. A rational point of the circle requires the termination of *both* coordinates; the cosine-process closes, the sine-process does not; hence a *rational point* $(\cos,\sin)$ of order 6 on the circle is a phantom that has a closed cosine-role but no Element-point (as a matrix in another representation, order 6 is possible—the obstruction belongs precisely to the orthogonal point). It is excluded not by fiat but by the fact that $\sqrt3$ provably does not close.

**$\sqrt5$** locks the icosahedron. In the *rational/crystallographic* arena over $ℚ$ a rotation of finite order is limited to the orders $\{1,2,3,4,6\}$; order 5 is impossible (in the real orthogonal group it of course exists—the obstruction is precisely over $ℚ$), since the trace of a rotation of order 5 satisfies the golden-ratio equation, whose roots are processes around $\sqrt5$, not rational numbers[^9]. This explains why fivefold symmetry—icosahedral quasicrystals—is “noncrystallographic”: over ℚ it remains a role-limit.

*As $\sqrt2$ locks the rotation by $45^\circ$ and $\sqrt3$ the $60^\circ$ point, so $\sqrt5$ locks the icosahedron: each of them is a non-terminating process, and it is precisely its non-termination that is the obstruction.*

It is essential that in space *only* the number responsible for the trace (twice the cosine of the angle) is restricted, not the sine: a rotation matrix can be rational with an irrational sine—the axis “absorbs” the irrationality. Therefore the restriction falls directly on the trace, and it is carried by the same numerical obstruction as in the plane.

## The Finitization Boundary Is the Boundary of Constructivity

Now the main point. Let us look not at the content of the demarcations but at their *axiom price*.

All the listed results of the Element side—the finite orders of rotations, rational probabilities, the crystallographic restriction, the operator no-go—are proved *without axioms*. The very *non-termination* of the role-limit is constructive too: the impossibility of a rational terminus for $\sqrt2,\sqrt3,\sqrt5$ is proved without classical choice. The classical axiom price appears not with the role-limit as a process but where the talk is of a *completed* continuum object: the spectral dichotomy and the uncountability of the interval, in the current formalization, *inherit* the Law of Excluded Middle ($L3$) and the associated witness parameter[^10].

This is no accident.

*The Law of Excluded Middle is needed for talk of a *completed* continuum—of a perfect subset, of an uncountable set as a ready object. The Element side is constructive; so is the non-termination of the role-limit as a process. The classical layer enters only with the *completed* form of the infinite.*

Hence the working map: in the instances considered, the finitization boundary coincides with the boundary of *axiom price*. One and the same line divides ontology (Element / role-limit), logic (constructive / requiring $L3$ in completed form), and spectrum (discrete / continuous)—but this is a synthetic map by instances, not a proved identity. The demarcation that gathers the instances of the Element side into one statement turns out itself to be *zero-axiom*[^11]—and its own axiom status is testimony to the principle: it is constructive precisely because it gathers only the Element side.

Let us also specify the reverse side. Even where external programs see “indeterminism”—non-completion, the openness of the future—our role-limit side remains constructive, *if* it is formulated as a non-terminating process rather than as a ready continuum[^12]. The Law of Excluded Middle is required not for non-termination as such, but for talk of a *completed* infinite object—which P4 does not have.

## E/R/R Analysis: The Boundary as a System

The finitization boundary is itself a *system* in the sense of ToS, and it should be analyzed by E/R/R. Epistemically we went from the observed demarcations (Elements) to their common form (Rules); ontologically the structure is generated in the reverse, generating order: Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *criterion of termination*: does the process close in finitely many steps? This rule stands one level above the objects themselves and sorts them. Adjoining it is the *form* of the sorting—a dichotomy without a middle: it closes *or* it does not; there is no third. In separate areas the criterion is concrete (the return of an orbit, the integrality of the trace, the enumerability of the spectrum), but the form is one.

**Roles (L4).** Two roles that every object plays: a *terminating process* (its terminus is an Element) and a *non-terminating process* (a role-limit, outside the finitely actual). The positions are grounded by structure: the role of an object is defined not by its “nature” but by whether the rule closes it—that is, by its relation to the Rules.

**Elements (L1 + P4).** The bearers are the rational approximations that the process gives at each finite stage, and the termini of terminating processes. Actualization under P4 is *finite*: only finite approximations are actual; where the “value” is a completed limit (the role-limit side), it is *not* actualized as an Element—only the stages are actual. This is what gives all objects their processual character.

**Well-formedness check.** Each object falls into exactly one role (it closes or it does not), and there is no third category; no component is assigned to two at once. Self-application, which P1 rules out, does not arise: the rule of sorting stands one level above the objects it sorts; it does not sort itself as an object.

**What the analysis yields.** First, it shows that “is $X$ infinite” is a confusion of categories: it demands that a role-limit be an Element-object, whereas $X$ is a process. Second, it explains the coincidence with the boundary of constructivity: the Element side is generated by a terminating rule and is therefore constructive; the role-limit side is a non-terminating process, and only talk of its *completed* limit brings in the classical axiom.

Thus the line begun in Part III by number-as-process and continued in Part IV by the principle P4 closes here as a single boundary—and in the following chapters it already works as a ready divider between the constructive core and the honestly marked remainder.

---

[^1]: Chapter III.4, “From Position to Process,” section “The Square Root of Two as a Functional System”: $\sqrt2$ is decomposed into three layers of the generating order; the exact statement of the impossibility of a rational value is `no_rational_sqrt2`.
[^2]: Each corresponding file compiles with zero open goals; belonging to the Element side is confirmed by checking the axioms used (`Print Assumptions`).
[^3]: “A rational orthogonal rotation of finite order $\Leftrightarrow$ one of four” (Niven’s theorem for rational $\cos,\sin$): proved through a bridge between the orbit and the integer trace. This concerns precisely the orthogonal arena with rational $\cos,\sin$; in other representations (e.g. $GL_2(ℚ)$) the orders $3,6$ also occur.
[^4]: These areas are an application to physics; here they serve as an illustration of a single mathematical form, not as the subject of the present volume.
[^5]: The corresponding statement for an arbitrary finite dimension is `no_finite_ccr`; the synthesis uses its $2\times2$ representative.
[^6]: `spectral_dichotomy`: within the *process* continuum hypothesis adopted in the project, not an arbitrary ZFC theorem about all spectra; in the current formalization it inherits $L3$.
[^7]: `no_rational_sqrt2`.
[^8]: `no_rational_sqrt3`, proved by infinite descent through the primality of three.
[^9]: “There is no rational rotation of order 5” is obtained as follows: the fifth trace polynomial factors, and a nontrivial order 5 forces $x^2+x-1=0$, whence $x=(-1\pm\sqrt5)/2$; a rational root is excluded through `no_rational_sqrt5`. This is the crystallographic restriction over ℚ.
[^10]: The technical Rocq object `L4_witness` is a declaration in the code connected with the Law of Sufficient Reason ($L4$), but it is *not* the law itself (not to be confused with a full-fledged axiom L4); “inherit” is meant according to `Print Assumptions` (sufficient dependencies in the current layer), not as a claim of minimality.
[^11]: The synthesis file, which ties representatives of all the constructive areas into one statement, checks as “Closed under the global context”—that is, without axioms.
[^12]: This is checked directly on the process formalization of Gisin’s numbers that reveal their digits in time: the process $\sqrt2$ has an exact nonzero error at every stage and does not reach a rational terminus—all without axioms. “Indeterminism as non-termination” is constructive.

---

Part: [[20 Final Synthesis|Part XX. The Final Synthesis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/07 Synthesis Map of Mathematics Beyond the Boundary|Chapter 7. Synthesis: A Map of Mathematics beyond the Boundary—Part XIX]] · [[Library/Branches/Mathematics/Volume/20 Final Synthesis/02 Finitization without Cutoff|Chapter 2. Finitization without Cutoff]] →
