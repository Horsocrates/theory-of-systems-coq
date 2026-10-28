---
title: "Chapter 3. A Ring, Not a Field: One Gap, Three Forms"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/19 Нестандартный анализ над процессами/03 Кольцо, а не поле один зазор — три формы.md"
sourceBlob: 3091a4eb6512fa8b940bf0e7cf002027e52f3173
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapters 1–2 built the infinitesimal as a process and the calculus as one shadow operation. Both ran up against one and the same stone: the germ ring of processes is *a ring, not a field*. This chapter lays it open completely.

*The flagship: one **undecided distinction**—a set $S\subseteqℕ$ such that both $S$ itself and its complement are infinitely large (Fréchet does not decide which one is “large”)—generates **three** algebraic forms of one role-limit gap: a zero divisor (multiplication), an oscillator without a shadow (addition), a non-invertible element (the ring). One root, three faces. And everything is constructive—0 axioms, even without the law of excluded middle.*

Why “a ring, not a field” is not a defect but an exact record of the finitization boundary; why the gap has exactly one root; and what exactly is undecidable (size, not membership)—these are the three steps of the chapter.

## A Ring, Not a Field

A field has no zero divisors: if $xy=0$, then $x=0$ or $y=0$. The germ ring of processes *violates* this rule. The indicator of the evens $E$ and that of the odds $O$ are both nonzero as germs, but $E\cdot O\sim 0$ (Chapter 1). Hence $E$ is nonzero but **non-invertible**: its inverse would be $1/E(n)=1/0$ at the odd indices. The Fréchet ring of germs is not a field[^1].

Invertibility in the ring of germs has an exact characterization: *a unit $\Leftrightarrow$ eventually nonzero* (then the inverse is the termwise $1/x$ on the tail), and *a zero divisor $\Leftrightarrow$ zeros occur arbitrarily far out* (the zero set is infinite—cofinal in the order of $ℕ$, not necessarily cofinite)[^2]. The infinitesimal $\delta=1/(n+1)$ is a *unit* (nonzero everywhere, with inverse $\omega=n+1$); the indicator $E$ is a *zero divisor*[^3]. Thus algebra divides: what is eventually nonzero is invertible (the Element); what vanishes infinitely often is the gap.

## One Gap, Three Forms

Where does a zero divisor come from? From an *undecided distinction*. Let us call a set $S$ **undecided** if both it and its complement occur *infinitely often*—for every $N$ there is $n\ge N$ with $n\in S$ (this is *cofinality in the order* of $ℕ$, **not** cofiniteness: the complement need not be finite). $E$ (the evens) and $O$ (the odds) are the canonical example: both are infinite, but neither is cofinite. The definition is *positive* (both infinitely often), without double negation—therefore everything below is constructive, without the law of excluded middle.

And this one property generates **three** forms of one gap[^4]:

- **multiplication**—a zero divisor: $\ind S\cdot\ind\neg S\sim 0$, but neither factor is $\sim 0$;
- **addition**—an oscillator without a shadow: $\osc S=\ind S-\ind\neg S$ has no constant shadow (this is exactly the $\mathrm{alt}$ of Chapter 2);
- **the ring**—non-invertibility: $\ind S$ is not a unit.

*Three algebraic faces—multiplication, addition, invertibility—of one and the same thing: Fréchet does not decide which of $S,\neg S$ is “large.” This is a genuine unification (one root $\to$ three forms), not a new theorem of nonstandard analysis—the forms themselves are classical; what is new is their reduction to one root, by machine and without `classic`.*

## The Gap Concerns Size, Not Membership

What exactly is undecidable? Not *membership*: to check $n\in E$ is to compute the parity of $n$, and this is decidable elementwise for every set *represented by a Boolean predicate* $ℕ\to\mathrm{bool}$[^5]. What is undecidable is *size*—“is $S$ large.” The Fréchet filter decides only the extreme cases: cofinite sets are large, finite ones small; for $E$ and $O$ it does not choose a side. The singleton $\{0\}$ is finite (its size is decided—an Element), while $E$ is undecided[^6]. The far side of the boundary is therefore *graded*: the Element (both axes decided) $\sqsubset$ the LPO rung (membership decidable, size not: $E$) $\sqsubset$ the Turing rung (membership undecidable: halting).

*The gap lives in **totalization**, not in the set: $E$ is computable elementwise, but “is it large” requires an external decision. And this decision is stronger than a one-off one: $\mathrm{LPO}$ decides *one* limiting alternative, whereas an ultrafilter decides *coherently for all* subsets of $ℕ$ at once. This is a global choice principle (a fragment of the Axiom of Choice), standing above the one-off $\mathrm{LPO}/\mathrm{WLPO}/\mathrm{LLPO}$ decisions.*

The zero divisor is the honest price of “a ring, not a field”: the machine trace of the fact that the distinction “large/small” has been left undecided. Closing it is the task of the next chapter.

## E/R/R Analysis: The Undecided Distinction as a System

Let us analyze by E/R/R in the generating order Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *undecided distinction*: $S$ and $\neg S$ are both cofinal (positively, constructively). From it come three forms: a zero divisor (multiplication), an oscillator without a shadow (addition), non-invertibility (the ring). A field would require deciding “what is large” by an external choice.

**Roles (L4).** $\ind S$ is the indicator; $\osc S$ is the oscillator; invertibility is the role of a unit (eventually nonzero); a zero divisor is the role of the gap (the zero set is cofinal); size is the role of the undecided (the $\mathrm{LPO}$ axis), membership the role of the decidable (the Turing axis, below the boundary).

**Elements (L1 + P4).** The bearers are processes $ℕ\toℚ$ and sets $ℕ\to\mathrm{bool}$: $E,O$ (undecided), $\{0\}$ (finite), $\delta$ (a unit). They are finitely actual; membership is decidable on each, but size is not.

**Well-formedness check.** The rule is the undecided distinction; the roles are the indicator, the oscillator, the unit, the divisor; the elements are processes and bool-sets; there are no overlaps. $E$ as a system: the values $1,0,1,0,…$ (Elements), the role of indicator and of divisor (Roles), while the unit status is *not determined internally*—the rule of invertibility is external (Fréchet does not decide “is the set of evens large”) $\Rightarrow$ the system is not closed internally (it requires external closure) $\Rightarrow$ a role-limit.

**What the analysis yields.** It reduces everything to one root: the undecided distinction “what is large” generates three algebraic forms of the gap, and the ring of germs is not a field precisely because this question is left open. The Element side consists of eventually nonzero units; the role-limit side, of zero sets that recur arbitrarily far out, decidable only by a global fragment of choice (above the one-off $\mathrm{LPO}$ decisions).

The ring will become a field only at the price of an external, noncanonical choice. The next chapter presents the ultrafilter as a role-limit engine: what it decides, why it cannot be presented, and why, by conservativity, its scaffolding is removable.

---

[^1]: `germ_ring_not_field` (in `UltrafilterRoleLimit`): $\exists$ a nonzero non-invertible element ($E$); supporting lemmas `even_ind_not_zero`, `even_ind_not_invertible`. Proved for the canonical indicators $E/O$ (that NO choice-free quotient is a field is an honest extrapolation). Machine-checked, 0 axioms.
[^2]: `unit_iff_eventually_nonzero` and `zero_divisor_iff_cofinal_z` (in `UnitZeroDivisorBoundary`); constructively (an explicit $1/x$, positive cofinality, `Qmult_integral`). Machine-checked, 0 axioms.
[^3]: `delta_is_unit`, `even_ind_is_zero_divisor` (in `UnitZeroDivisorBoundary`). Machine-checked, 0 axioms.
[^4]: `undecided` ($S$ and $\neg S$ are cofinal, positively), and `undecided_zero_divisor`, `undecided_no_shadow`, `undecided_non_unit`; the summary theorem `nonstandard_synthesis` (in `NonstandardOverProcessesSynthesis`). Machine-checked, 10 Qed, 0 axioms—and WITHOUT `classic`.
[^5]: `bool_pred_decidable` (in `UndecidedHierarchy`): every set given by a predicate $ℕ\to\mathrm{bool}$ is decidable elementwise. Machine-checked, 0 axioms.
[^6]: `undecided_evens`, `singleton_finite`, the summary theorem `undecided_hierarchy` (in `UndecidedHierarchy`). Machine-checked, 0 axioms.

---

Part: [[19 Nonstandard Analysis over Processes|Part XIX. Nonstandard Analysis over Processes]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/02 Shadow Derivative Integral Calculus as One Operation St|Chapter 2. Shadow, Derivative, Integral: Calculus as One Operation st]] · [[Library/Branches/Mathematics/Volume/19 Nonstandard Analysis over Processes/04 Ultrafilter as Role Limit Engine|Chapter 4. The Ultrafilter as a Role-Limit Engine]] →
