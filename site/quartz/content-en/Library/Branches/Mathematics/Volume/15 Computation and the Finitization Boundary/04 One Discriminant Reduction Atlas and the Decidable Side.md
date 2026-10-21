---
title: "Chapter 4. One Discriminant: The Reduction Atlas and the Decidable Side"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/15 Вычисления и граница финитизации/04 Один дискриминант редукционный атлас и разрешимая сторона.md"
sourceBlob: 9429e79c083a8e5cafddffd0a77cd96f6859d022
translated: 2026-10-20
status: draft
---

## The Mirror of the Diagonal

Chapter 15.3 gave the *negative* master structure: one diagonal *rules out* a decider where the boundary is a role-limit. The boundary has two sides, and the second has its own master structure, a *positive* one:

> **where the boundary is decidable, it is drawn by one terminating criterion—the discriminant.**

In short: *undecidability is one diagonal, decidability is one discriminant*. And these are one boundary, not two topics: the decidable (Element) face and the undecidable (role-limit) faces stand in *the same* extended capstone about the four faces of the boundary (15.3)—number is decidable; program / set / complexity are not. This chapter unfolds the Element face: what draws it, why by one criterion, and why choice on it is free of the Axiom of Choice.

## The Discriminant: A Rational Eigenvalue

Take a $2\times2$ matrix with integer entries, trace $\trace$, and determinant $\det$. Its eigenvalues are the roots of the characteristic quadratic, and everything is decided by the *discriminant*

$$
\Delta \;=\; \trace^{2} - 4\det,
  \quad
  \lambda_{1,2} \;=\; \frac{\trace \pm \sqrt{\Delta}}{2}.
$$

Mathematically (for an integer $2\times2$ matrix) an eigenvalue is *rational* if and only if $\sqrt{\Delta}$ is rational, that is, when $\Delta$ is a *perfect square*:

$$
\lambda \in ℚ
  \quad\Longleftrightarrow\quad
  \sqrt{\Delta}\inℚ
  \quad\Longleftrightarrow\quad
  \Delta = r^{2}\ \text{for some integer } r.
$$

The *key directing* side of this bridge is singled out by machine: an integer root of the characteristic polynomial *forces* a square discriminant ($\Delta=(2x-\trace)^2$); the contrapositive: $\Delta$ is not a square $\Rightarrow$ there is no rational root $\Rightarrow$ role-limit. And the question “is $\Delta$ a perfect square?” itself is **decidable** by a *terminating* computation (take the integer part of the root and check the square): the Element boundary is drawn—the presence of a rational characteristic root is decided in a finite number of steps.[^1]

Examples from the atlas itself: $\Delta=9$ is a perfect square, there is a rational characteristic root (Element); $\Delta=8$ (Hadamard) and $\Delta=32$ (Pell) are not squares, there is no rational root ($\sqrt2$), and this is a role-limit. Here a role-limit means *not* the uncomputability of a process (as with the diagonal) but *going beyond the rational Element layer*: $\sqrt{\Delta}$ requires an extension of the carrier—exactly the rational / irrational barrier that divided Part IV, now as a decidable *test*.

## The Reduction Atlas: Different Engines, One Question

The strength of the positive side is that this *one* criterion covers a great deal. Several seemingly unrelated “engines”—Pell’s equation, Niven’s theorem (rational values of the cosine at rational angles), quadratic surds, parity, unimodular matrices—all *reduce to the same question*: “is the discriminant a perfect square?” This is the **reduction atlas**: different surfaces, one underlying criterion.[^2]

Structurally, this is the *mirror* of 15.3. There one diagonal ($b\neq\negb b$) turned out to be the root of many negative results; here one discriminant (is $\Delta$ a square?) turns out to be the root of many *positive*, decidable ones. The finitization boundary has two axes of symmetry, and each is unique.

## Choice without the Axiom of Choice

On the decidable side one more thing is given for free—*choice*. If a predicate over a finite list is decidable, then the *first witness* is a canonical, *terminating* choice: run through the list and take the first suitable element. The Axiom of Choice is not needed—choice is *computed*.[^3]

This is the same line as in our set theory without AC (deterministic choice: argmax-by-index, the first witness): where the role-limit side would require an *oracle* (an unreachable choice from all at once), the Element side *computes* the choice in a finite number of steps—on a finite ordered carrier with a decidable predicate. Choice as a process, not as an oracle—P4 in action.

{
And this is not the ceiling of the finite. The same device—a decidable criterion plus a canonical order (the least element of $ℕ$)—rises as a *ladder*: from a countable carrier (countable choice) to a countable chain (dependent choice) and to an infinite tree with decidable branching (Kőnig’s lemma). At every rung, as long as the criterion is decidable and the carrier is ordered, choice remains *computable*, and the Axiom of Choice is not required. The synthesis is one: of the five levels of the ladder, four are free of the Axiom of Choice—the finite, the countable, the dependent, and Kőnig’s—and its price falls exactly on the fifth, where the predicate becomes undecidable. Ramsey’s theorem sits on the same boundary: finite Ramsey is *decidable* ($R(3,3)=6$ is computed by exhaustive search), while infinite Ramsey is a role-limit (one must choose a color that repeats infinitely). The same Element/role-limit face on which the whole chapter stands.[^4]
}

## The Discriminant as a Decision Procedure

Let us gather the positive side into one. The diagonal (15.3) *rules out* a decider for role-limit boundaries; the discriminant *gives* a decider for the Element boundary. This is the exact mirror:

$$
\underbrace{\text{diagonal}}_{\text{no decider}}\ (\text{15.3})
  \quad\Longleftrightarrow\quad
  \underbrace{\text{discriminant}}_{\text{a decider exists}}\ (\text{here}).
$$

And both stand in one theorem about the faces of the boundary: number is *Element*-drawn (the discriminant), program / set / complexity are role-limit-drawn (the diagonal).[^5] One boundary, two master structures: the *diagonal* (negative) $\oplus$ the *discriminant* (positive). This is the spine of the part.

## The Horizon: General Degree

Let us be exact about scale. The discriminant criterion is carried out in our system *concretely*—for the quadratic case ($2\times2$, $\Delta=\trace^2-4\det$) and for the five engines of the atlas, all by machine and 0-axiom. A *fully general* procedure—deciding the rationality of the spectrum *in any degree* ($n\times n$, the rational roots of an arbitrary characteristic polynomial)—is a natural *continuation* of the same criterion (the rational root test and the factorization of the characteristic polynomial; for higher degrees one discriminant no longer suffices). In our system it has so far been developed case by case (the quadratic atlas), not closed into *one* procedure of general degree; this is the nearest horizon of the positive side, not a claimed result.

The distinction is honest and of the same kind as in 15.3 (where four faces are assembled by machine and the top of the ladder is a standard reading): here the quadratic discriminant and the atlas are assembled by machine, and the general degree is named as a direction.

## E/R/R Analysis and What the Chapter Has Prepared

**Rules (L5).**  The discriminant $\Delta=\trace^2-4\det$ is a *rule* that draws the Element boundary: “$\Delta$ is a perfect square $\Rightarrow$ rational spectrum $\Rightarrow$ Element.” Its terminating realization is the perfect-square test; the reduction atlas is a rule that reduces many engines to this one.

**Roles (L4).**  “Rational spectrum / Element” versus “irrational / role-limit” are two roles of the spectral datum; the decider (the square test) is a role-criterion; the first witness is the role of *choice-as-computation* (not an oracle).

{

**Elements (L1${}+{}$P4).**  Concrete matrices, values of $\Delta$, finite lists of witnesses. *Not* an element *of the current confirmed layer*: a closed procedure of general degree—a boundary of coverage, not an ontological P4 exclusion (rational root procedures exist).}

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| discriminant $\Delta=\trace^2-4\det$; the atlas of engines | the drawing of the Element boundary | Rule (L5) |
| rational / irrational spectrum; decider-test; first witness | roles and the criterion-choice | Role (L4) |
| matrices; values of $\Delta$; lists of witnesses | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  The decidable side is exactly the *finitizable* side: the boundary folds into a terminating test, and this is what “Element” means. The discriminant is the *positive* face of the finitization boundary, the diagonal the *negative* one; together they are the very boundary that divides the computable from the uncomputable.

**What the chapter has prepared.**  The second master structure of the part has been presented: decidability is one discriminant ($\Delta$ is a perfect square), the reduction atlas reduces many engines to it, and choice on this side is free of the Axiom of Choice. Everything proved here is 0-axiom and machine-checked; the general degree is honestly named as a horizon. Next comes Chapter 15.5: *type safety through fuel*, where an infinite chain of reductions is finitized into a finite run—one more face of the same boundary; and the finale, 15.7, will bring both master structures together: *diagonal $\oplus$ discriminant—one finitization boundary*.

---

[^1]: Machine-checked, **0 axioms**: `src/cs/BoundaryDecidability.v`—`is_square` (the perfect-square test via the integer root), `rational_split` ($\Delta$ is a square), `discriminant_ element_drawn` (the Element-drawnness of the criterion). The bridge and the discriminant: `src/stdlib/ReductionAtlasSynthesis.v`—`disc` / `tr2` / `det2`, `disc_eq` ($\Delta=\trace^2-4\det=(a{-}d)^2{+}4bc$), `char_poly_ complete_square`, and the directing `eigenvalue_ forces_ square_disc` (a rational root $\Rightarrow$ a square $\Delta$). The full iff is a standard mathematical reading for an integer $2\times2$.
[^2]: Machine-checked, **0 axioms**: the capstone `src/stdlib/ReductionAtlasSynthesis.reduction_ atlas_ synthesis` (all engines reduced to `disc`); the five engines are `ReductionAtlasPell.v`, `ReductionAtlasNiven.v`, `ReductionAtlasSurd.v`, `ReductionAtlasParity.v`, `ReductionAtlasUnimodular.v` (additional quadratic lemmas are in `QuadraticDiscriminant.v`).
[^3]: Machine-checked, **0 axioms**: `src/cs/DecidableSelection.v` (7 Qed)—`first_witness` (the first witness in a list) with `first_witness_sound / complete / first`, `decidable_list_choice` (choice under a decidable finite predicate).
[^4]: Machine-checked, **0 axioms**: `src/cs/CountableSelectionFree.v` (6 Qed, `countable_selection_free`, `dec_family_choice`); `CountableDependentChoiceFree.v` (7 Qed, `countable_dependent_choice_free`, `dc_chain_step`); `DecidableKonig.v` (7 Qed, `decidable_konig`); the synthesis `SelectionWithoutChoiceSynthesis.v` (8 Qed, `selection_without_choice_synthesis`: `count_free_4` are free, `count_priced_1` comes with a price); the boundary is `RamseyBoundary.v` (15 Qed, `R33_upper` / `R33_lower` /  `ramsey_3_3`, $R(3,3)=6$).
[^5]: The Element face and the role-limit faces together: `src/cs/BoundaryDecidability.one_boundary_three_faces` and `KolmogorovRoleLimit.one_boundary_four_faces` (**0 axioms**): `discriminant_ element_drawn` stands in one conjunction with `halting_ role_limit_drawn` and Cantor.

---

Part: [[15 Computation and the Finitization Boundary|Part XV. Computation and the Finitization Boundary]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/03 One Diagonal Halting Rice Cantor Kolmogorov|Chapter 3. One Diagonal: Halting, Rice, Cantor, Kolmogorov]] · [[Library/Branches/Mathematics/Volume/15 Computation and the Finitization Boundary/05 Type Safety as Fuel Finitization|Chapter 5. Type Safety as Fuel Finitization]] →
