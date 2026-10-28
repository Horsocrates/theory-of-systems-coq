---
title: "Chapter 1. The Infinitesimal as a Process"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/19 Нестандартный анализ над процессами/01 Бесконечно малое как процесс.md"
sourceBlob: 2de4cd23aea6d02f45fb7e4f73803997857611ac
translated: 2026-10-20
status: draft
---

## Where the Part Stands

After function-as-process (Part XVI), discrete mathematics and information (Part XVII), and the process hierarchy (Part XVIII), the volume takes a step *beyond the boundary* of finitization—to where classical mathematics builds the hyperreal numbers, infinitesimals, and the transfer principle through a nonprincipal ultrafilter. ToS asserts: this is *process mathematics in role-limit packaging*.

*The flagship of the part: all the real content of nonstandard analysis is relocated onto processes. An infinitesimal is the process $\delta=1/(n+1)$, not a “vanishingly small number”; the hyperreals are the role-limit closure of germ-processes, and nonconstructivity sits at exactly ONE point: the maximization of the Fréchet filter (cofinite, constructive) to a nonprincipal ultrafilter (omniscience). This chapter builds the Element core—the ring of germs WITHOUT an ultrafilter.*

Since the system is ontological, it must deliver a verdict on every construction “beyond the boundary”: an *Element core* (real content, expressible by processes, 0 axioms); a *role-limit instrument* (a real organizing role, but nonconstructive packaging—removable formwork); or the *illusory* (consistent in ZFC, but without a referent or application—ToS names it and dispels it, Chapter 6). The part goes through the constructions of nonstandard analysis with this verdict; we begin with the very core—the infinitesimal.

The approach was not invented by ToS: infinitesimals through the Fréchet filter, without an ultrafilter, are close in spirit to the Schmieden–Laugwitz tradition (the $\Omega$-calculus, 1958). The contribution of ToS is the relocation ONTO PROCESSES $ℕ\toℚ$, the machine check of the Element core, zero divisors as the trace of the missing ultrafilter, and the tie to the finitization boundary. The index $n$ here runs over the natural type *from zero* (a convention of the instrument): $\delta_n=1/(n+1)$, that is, $1,\tfrac12,\tfrac13,…$ There is no completed infinity and no $ℝ$ as a primary object—only processes and their roles.

## The Infinitesimal Is a Process

Take $\delta_n = 1/(n+1)$: $1, \tfrac12, \tfrac13, …$ This is a *process*, finitely actual at every stage (P4): at stage $n$ we have before us a concrete rational number, not a completed object. It has two different statuses, which classical intuition confuses.

*As an element* $\delta$ is **nonzero**: $1/(n+1)\neq 0$ for every $n$—and even as a germ $\delta\not\sim 0$ (there is no tail on which $\delta_n=0$). *As a role* $\delta$ is **infinitesimal**: for every standard $\varepsilon>0$, from some $n$ on, $|\delta_n|<\varepsilon$ holds[^1].

This is where the old riddle “is the infinitesimal zero or not?” falls away. Nonzeroness is a *fact about elements* ($\delta_n\neq 0$); infinitesimality is a *role* (the behavior of the process in the limit). They do not contradict each other, because they belong to different levels: $\delta$ is not a number with a paradoxical property but a *process*. In the next chapter the same move will rigorously lay open Berkeley’s paradox of the “ghosts of departed quantities”: the ghost is the shadow operation, taken at the end, not a substitution of zero.

## The Ring of Germs: $\omega\cdot\delta=1$ and the Trace of the Missing Ultrafilter

Processes $ℕ\toℚ$ are added and multiplied pointwise and identified as *germs*—by the Fréchet filter: $x\sim y$ if $x_n=y_n$ for all $n\ge N$, for some $N$ (cofinite agreement). This rule is given *constructively*: it requires no choice on $2^{ℕ}$ and does not select one of two infinite parts (although for arbitrary processes it is not a total Boolean decider). We work with germs at the *setoid* level—processes modulo $\sim$, with operations compatible with $\sim$ (congruent); an explicit quotient type is not needed, and no ultrafilter is used. This is the ring of germs $ℚ^{ℕ}/\text{Fréchet}$.

$\delta$ is *invertible* in the ring of germs: its inverse representative is the process $\omega_n=n+1$ ($1,2,3,…$, an infinitely *large* quantity), and $\omega\cdot\delta\sim 1$[^2]. The infinitely large and the infinitesimal are mutually inverse processes; there is no mystery, just the ordinary $1/(n+1)\cdot(n+1)=1$.

But the ring of germs is precisely **a ring, not a field**: it has *zero divisors*. The indicator of the evens $E_n=[ n\text{ even} ]$ and the indicator of the odds $O_n=[ n\text{ odd} ]$ are both nonzero as germs (each equals $1$ infinitely often), but their product is pointwise zero: $E\cdot O\sim 0$[^3].

*Zero divisors are the machine TRACE of the missing ultrafilter. An ultrafilter would decide “the set of evens is large OR the set of odds is,” identifying one of $E,O$ with $1$ and the other with $0$—and thereby removing this particular zero divisor. Without this decision both are nonzero, while the product is zero. The undecidedness of “what is large” is the role-limit gap itself (Chapter 3); a field requires closing it (Chapter 4).*

## The Infinitesimals Form an Ideal

Infinitesimals behave algebraically as the “negligible”: the sum of two infinitesimals is infinitesimal, and the product of a finite quantity and an infinitesimal is infinitesimal[^4]. That is, the infinitesimals form an *ideal* in the ring of finite germs—the algebraic backbone of the notion “negligibly small,” on which the whole technique of $\infty$-small quantities rests: to discard an infinitesimal correction is to factor by this ideal. The chapter’s capstone gathers four facts—$\delta$ is nonzero-and-$\infty$-small, $\omega\cdot\delta=1$, zero divisors, the ideal—into one machine-checked statement[^5].

## E/R/R Analysis: The Germ as a System

Let us analyze the ring of germs by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is *germ equality* (the Fréchet filter): $x\sim y$ under cofinite agreement. The ring operations are pointwise and compatible with $\sim$ (congruent). The roles are read from the *eventual* behavior of the process, not from individual values.

**Roles (L4).** The germ class; three roles by the behavior of the process: *finite*—a bounded process, *infinitely large*—an unbounded one, *infinitesimal*—one tending to zero (in the standard $\varepsilon$-sense). $\delta$ is the canonical infinitesimal, $\omega$ the canonical infinitely large quantity (inverse to $\delta$ in the ring). Invertibility is the role of a unit; a zero divisor is the role of the gap.

**Elements (L1 + P4).** The bearers are processes $ℕ\toℚ$, finitely actual at every stage: $\delta_n=1/(n+1)$, $\omega_n=n+1$, the even/odd indicators. There is no completed “infinitesimal number”—only a process.

**Well-formedness check.** The rule is germ equality; the roles are infinitesimal / finite / infinitely large; the elements are rational processes; there are no overlaps. $\delta$ itself is a complete E/R/R system: the rule-descent $n\mapsto 1/(n+1)$ (Archimedean decrease), the role “$<$ every standard $\varepsilon$,” and the elements, rational values.

**What the analysis yields.** It removes the riddle of the infinitesimal: $\delta$ is nonzero (an element) and $\infty$-small (a role)—this is not a paradox but two levels of one process. And it names the boundary: the ring of germs is the Element core (decidable, 0 axioms); the field $^{*}ℝ$ (a total order, full transfer) requires closing the gap of the zero divisors with an external ultrafilter—a role-limit, and this is the horizon of Chapter 4. Zero divisors are the honest price of “a ring, not a field”: the machine trace of that very undecided distinction.

The infinitesimal has been built as a process. The next chapter brings the *shadow* (the standard part) and the *derivative* through the infinitesimal: one operation $\mathrm{st}$, on which the whole calculus rests, and a rigorous laying open of Berkeley’s paradox.

---

[^1]: `delta` $=1/(n{+}1)$, `delta_nonzero` ($\delta\not\sim 0$ as a germ), `delta_infinitesimal` (the role of the $\infty$-small: $\forall\varepsilon>0\;\exists N\;\forall n\ge N\;|\delta_n|<\varepsilon$), the definition `g_infinitesimal` (in `GermInfinitesimal`). Machine-checked, 0 axioms.
[^2]: `omega` $=n{+}1$, `omega_infinite` (the role of the $\infty$-large), `omega_delta_one` ($\omega\cdot\delta\sim 1$ as germs). Machine-checked, 0 axioms.
[^3]: `even_ind`, `odd_ind`, `zero_divisors_exist`: $E\not\sim 0$, $O\not\sim 0$, but $E\cdot O\sim 0$. Machine-checked, 0 axioms.
[^4]: `infinitesimal_add` (closure under addition) and `finite_times_infinitesimal` (finite $\times \infty$-small $=\infty$-small), with the definitions `g_finite`/`g_infinitesimal` (in `GermInfinitesimal`). Machine-checked, 0 axioms.
[^5]: `germ_ring_infinitesimal_summary` (in `GermInfinitesimal`): the summary theorem of the Element core. Machine-checked, 19 Qed, 0 axioms.

---

Part: [[19 Nonstandard Analysis over Processes|Part XIX. Nonstandard Analysis over Processes]] · Volume: [[Mathematics|“Mathematics”]]

Concepts: [[Paradox]]

Navigation: ← [[Library/Branches/Mathematics/Volume/18 Process Hierarchy/05 Synthesis the Hierarchy Is a Process|Chapter 5. Synthesis: The Hierarchy Is a Process—Part XVIII]] · [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/02 Shadow Derivative Integral Calculus as One Operation St|Chapter 2. Shadow, Derivative, Integral: Calculus as One Operation st]] →
