---
title: "Chapter 6. Processes as Universal Constructions; Setoid as a Topos"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/14 Категория систем/06 Процессы как универсальные конструкции; Setoid как топос.md"
sourceBlob: fc5e9adbf1ed36f3b1d9d81dad1bcd0cf6abc139
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

Chapters 14.1–14.3 worked within a level, 14.4 linked the levels by an adjunction (complementarity), and 14.5 raised the adjunction to a language of dualities. This chapter is about P4 (Finite Actuality)—about how ToS understands *universal constructions*: limits, colimits, exponentials, the subobject classifier. Here ToS has **two readings**, and both dispense with the “completed infinite object”:

- **The process reading (P4 literally):** a limit and a colimit *are processes*. A product is a process of pairs, an equalizer a process of differences, a colimit *the process itself*.
- **The setoid-topos reading (abstract):** the category of setoids $\SetoidCat$ carries a *topos kit* of structures—finite (co)limits, cartesian closedness, a predicate subobject classifier—and all of them are constructive.

**Tiers (honestly, checked against dependencies).**  The process reading is the process layer, *conservatively assigned* to the `classic` tier (it depends on `ProcessArithmetic`, which imports `Classical`; the exact status of particular lemmas is by `Print Assumptions`); in `origin/main`. The setoid-topos reading is **0 axioms by the local build**, but in the *local* layer `src/category/` (commit `90ebd74`, awaiting `push`). The contrast is instructive: the *concrete* P4 reading drags in L3 (analysis over ℚ), while the *abstract* topos reading is fully constructive.

## The Process Reading: Limits Are Processes

Under P4 a universal construction is *computed stage by stage* rather than “assembled” from a completed cone—that is, it *is a process*.
[^1]

**The product is a process of pairs.**  $A\times B$ is the pointwise pairing `process_product`: $n\mapsto(R_1 n, R_2 n)$; the projections return the components (`product_fst`/`_snd`), the pairing is unique (`product_universal`), and if both components are Cauchy, so is the product (`product_cauchy`).

**The equalizer is a process of differences.**  $\mathrm{eq}(f,g)$ is `equalizer_process` $f g
= \lambda n. f n - g n$. It converges to zero exactly when $f$ and $g$ are equivalent as processes (`equalizer_converges` and conversely `equalizer_zero_means_equiv`). That is, for processes “to coincide” means that *the equalizer tends to zero*, not “they are equal as completed objects.”

**The coproduct is an interleaving.**  $A+B$ is the alternation (`process_coproduct`): the even positions carry $R_1$, the odd ones $R_2$; the injections land exactly in their places ($R_1(k)$ at position $2k$, $R_2(k)$ at $2k+1$—`coproduct_inj1`/`_inj2`).

## The Flagship of P4: The Colimit Is a Process

The high point of the process reading is the *directed colimit*. A chain of processes $a_0,a_1,a_2,…$ needs no “completed” colimit-object: the **diagonal** serves as one—the process itself

$$
\texttt{directed\_colimit}\ \mathrm{chain}\ =\ \lambda n. \mathrm{chain} n n
$$

(`colimit_diagonal`). This is P4 in the flesh: “the colimit of the chain $a_0,a_1,…$ is the process $a$ itself”—no completed limit object is required or introduced.

The same lesson runs through the whole volume: $ℝ$ is a process (Part IV), $\overline{ℚ}$ is a tower without a maximal rung (Part XI), a manifold is a process (Part XII). Categorically it is named in one phrase: **the colimit is the process itself, not a completed object over and above it**. Potential infinity (the process) takes the place of actual infinity (the completed colimit)—exactly what P4 requires.

## The Process Category

When processes are packaged into a *category* (the objects are processes, the morphisms are consistent maps), L3 comes into play: the formalization of the process category *imports* `Classical`.
[^2] This is an honest boundary of tier: the *elementary* process definitions are simple, but already the Cauchy equalizer (`equalizer_cauchy`) and the like rest on the ℚ-Cauchy analysis, and that analysis imports `Classical`. Therefore we *conservatively* assign the process side to the `classic` tier rather than to “0 axioms”; the exact status of particular lemmas is verified via `Print Assumptions` (the map of boundaries is in 14.7).

## The Setoid-Topos Reading: $\SetoidCat$ as a Topos Kit

The abstract side presents universal constructions in the *category of setoids* $\SetoidCat$ (the objects are types with an equivalence, the morphisms are maps that respect it; see 14.1). Here a **topos kit** of structures is assembled—and all of it is **0-axiom**.

**Finite limits.**  The terminal object is the unit setoid (`setoid_terminal`); binary products with the universal property (`setoid_prod_beta1`/`_beta2`, `setoid_prod_unique`); equalizers (`eq_equalizes`, `eq_univ`, `eq_unique`). Mathematically, terminal ${}+{}$ binary products ${}+{}$ equalizers form the standard basis of *all* finite limits; these basic components and their universal properties are machine-checked.
[^3]

**Finite colimits.**  The initial object is the empty setoid (`setoid_initial`); coproducts with the universal property (`coprod_beta1`/`_beta2`, `coprod_unique`). Initial ${}+{}$ binary coproducts form the standard basis of finite colimits (by machine: these components and their universal properties).
[^4]

**Cartesian closedness.**  The exponential $B^A$ is the setoid of maps $A\to B$ with pointwise equality, with application (`setoid_eval`) and currying (`setoid_curry`); the universal property is the bijection

$$
\Hom(C\times A,\ B)\ \cong\ \Hom(C,\ B^A)
$$

(`exp_beta`, `exp_unique`). Hence $\SetoidCat$ is *cartesian closed*.
[^5]

**The subobject classifier.**  The object of truth values $\Omega=(Prop,\leftrightarrow)$ (at the level of the current setoid layer) with truth `true` and the characteristic arrow `char`: a respecting predicate corresponds to an arrow $A\to\Omega$, and the subobject $\{a\mid P a\}$ is the preimage of truth (`subobject_commute`, `subobject_univ`, `subobject_unique`).
[^6]

**Summary.**  $\SetoidCat$ carries finite (co)limits ${}+{}$ cartesian closedness ${}+{}$ a predicate classifier—a **constructive predicate (elementary) topos layer**, entirely 0-axiom (by the local build; after the `push`, a final `Print Assumptions` check). This is the concrete “structure of structures” promised in 14.1.

## The Honest Boundary: A Predicate Topos, Not a Full One

The classifier classifies *respecting predicates* (constructive subsetoids), *not* arbitrary monomorphisms: the latter would need an image factorization, which we do not build. Therefore it is honest to speak of a **predicate** topos layer rather than of a full elementary topos. This is the exact domain of the construction, not its defect: the predicate classifier is exactly what the constructive setoid setting gives.

**P4 in both readings.**  The topos constructions are P4 to the same extent as the process ones. The product is *finitely actual* (a pair is a finite bearer); the exponential $B^A$ is a *role-level* internal hom (a setoid with pointwise equality), *not* a cardinal operation on completed sets (cf. Part X); $\Omega=(Prop,\leftrightarrow)$ (at the level of the setoid layer) is an object of values with logical equivalence, *not* “the set of all subsets.” The universal property is everywhere a *rule* of unique factorization, not a completed object over all cones. Both readings are one P4 movement: *the potential instead of the actual*.

## E/R/R Analysis: Universal Constructions as E/R/R

**Rules (L5).**  Universal properties ($\beta$, $\eta$-uniqueness) constitute each construction; on the process side, the preservation of the Cauchy property; on the topos side, pointwise/componentwise setoid equality (role-level, not Leibniz).

**Roles (L4).**  Projections/injections/mediators (limits/colimits); application/currying (the exponential); `char`/the classifier (subobjects); *process-as-colimit*, the role of P4 itself.

**Elements (L1${}+{}$P4).**  Concrete data: the pairs $(R_1 n,R_2 n)$, the differences $f n-g n$, the interleaving, the diagonal $\mathrm{chain} n n$; setoid carriers, $Prop$. *Not* an element: a *completed* infinite limit/colimit (the process side does not introduce it); and the cardinal $B^A$ / a classifier of arbitrary monos (the topos side gives only a *predicate* one).

| **Component** | **What it determines** | **E/R/R category** |
|---|---|---|
| universal properties ($\beta$/$\eta$); Cauchy preservation; setoid equality | the constitution of the constructions | Rule (L5) |
| projections/mediators; eval/curry; `char`; process-as-colimit | the status of universal arrows | Role (L4) |
| pairs, differences, diagonal; setoids, $Prop$ | finitely actual bearers | Element (L1${}+{}$P4) |

**P4 diagnostics.**  Both sides are one: *there is no completed infinity*. The colimit is a process, not an object; the exponential is a role-level hom, not a cardinal; the classifier is over respecting predicates, not over all monos. P4 here constructively *builds* rather than rules out.

## What the Chapter Has Prepared

Universal constructions have received two concordant readings. The *process* one (P4 literally): the product is a process of pairs, the equalizer a process of differences, the coproduct an interleaving, and **the colimit is the process itself** (the diagonal $\mathrm{chain} n n$)—the flagship of P4. The *setoid-topos* one: $\SetoidCat$ carries finite (co)limits, cartesian closedness, and a predicate subobject classifier—a constructive predicate topos layer. Both readings are one P4 movement: the potential instead of the completed.

**Tiers (honestly).**  The process side—`ProcessLimitColimit.v` + `ProcessCategory.v`—is the process layer, *conservatively* assigned to `classic` (the ℚ-Cauchy analysis; `ProcessCategory.v` imports `Classical` directly); in `origin/main`. The topos side—five files of `src/category/` (`SetoidProducts` 4, `SetoidEqualizers` 3, `SetoidCoproducts` 4, `SetoidExponential` 2, `SetoidClassifier` 4 = **17 Qed**)—is **0 axioms by the
local build**, but in the *local* layer (`90ebd74`, awaiting `push`). The honest boundary: a predicate topos, not a full one (an image factorization is needed).

Next comes Chapter 14.7, the finale: *all of ToS as a category* (E/R/R itself is a category); the bridge to type theory (Curry–Howard); and the **map of boundaries of Part XIV**—the universe walls (“the category of all categories/presheaves is large”), the `classic` tier, the continuum price—gathered in one place.

---

[^1]: `src/process/ProcessLimitColimit.v` (0 Admitted; in `origin/main`). The file header states `AXIOMS: none`; but the module depends on the process stack, where `ProcessArithmetic` imports `Classical`, so we *conservatively* assign the process side to the `classic` tier (the exact status is by `Print Assumptions`). Key names: `process_product`, `product_universal`, `equalizer_process`, `equalizer_converges`, `equalizer_zero_means_equiv`, `process_coproduct`, `coproduct_inj1`/`_inj2`, `directed_colimit`, and others.
[^2]: `src/process/ProcessCategory.v` (20 Qed, 0 Admitted; inherits `classic`—“inherited from ProcessNoetherian”—and imports `Classical`; in `origin/main`). Next to it is `src/process/ProcessUniversalAdjunction.v` (24 Qed; the process layer; in `origin/main`): the universal adjunction on the process side.
[^3]: `src/category/SetoidProducts.v` (4 Qed) and `SetoidEqualizers.v` (3 Qed); 0 Admitted, 0 axioms; **local layer** `src/category/` (`90ebd74`, awaiting `push`): `unit_setoid`/`setoid_terminal`, `prod_setoid`/`setoid_fst`/`_snd`/`_pair`, `setoid_prod_beta1`/`_beta2`/`_unique`; `eq_setoid`/`eq_incl`/`eq_mediator`, `eq_equalizes`/`eq_univ`/`eq_unique`.
[^4]: `src/category/SetoidCoproducts.v` (4 Qed, 0 Admitted, 0 axioms; the local layer): `empty_setoid`/`setoid_initial`, `sum_setoid`/`inl_mor`/`inr_mor`/`sum_copair`, `coprod_beta1`/`_beta2`/`_unique`.
[^5]: `src/category/SetoidExponential.v` (2 Qed, 0 Admitted, 0 axioms; the local layer): `exp_setoid`, `setoid_eval`, `curry_app`, `setoid_curry`, `exp_beta`, `exp_unique`.
[^6]: `src/category/SetoidClassifier.v` (4 Qed, 0 Admitted, 0 axioms; the local layer): `omega_setoid` $=(Prop,\leftrightarrow)$, `setoid_true`, `char`, `char_self`, `sub_setoid`, `subobject_commute`/`_univ`/`_unique`.

---

Part: [[14 Category of Systems|Part XIV. The Category of Systems]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/14 Category of Systems/05 Adjunctions as a Universal Language of Dualities|Chapter 5. Adjunctions as a Universal Language of Dualities]] · [[Library/Branches/Mathematics/Volume/14 Category of Systems/07 Synthesis All of Tos as a Category Bridge to Type Theory Map of Boundaries|Chapter 7. Synthesis: All of ToS as a Category; the Bridge to Type Theory; the Map of Boundaries]] →
