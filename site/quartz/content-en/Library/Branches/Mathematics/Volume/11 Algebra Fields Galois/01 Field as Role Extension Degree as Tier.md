---
title: "Chapter 1. Field as Role-Extension; Degree as Tier"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/01 Поле как роль-расширение; степень как ярус.md"
sourceBlob: bd33a96006d0c30366bdde594c7b744b285ae3c5
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### The Opening of Part XI

Part X revised the foundation itself—set, membership, cardinality, choice, infinity—and found behind the strong axioms a single category mistake: *the reification of a rule or role-totality as a completed Element-object*. Part XI makes the same move one storey up—in *algebra*: the field, the extension, the degree, the automorphism group, solvability by radicals, the algebraic closure.

Classical Galois theory takes as its primary objects the *field* $L$, its subfield $K$, the abstract *automorphism group* $\Aut(L/K)$ as a completed thing, the number $[L:K]$ as a ready characteristic, and the *splitting field* and the *algebraic closure* as existing totalities, and it formulates the Fundamental Theorem as a correspondence between the subgroups of $\Aut(L/K)$ and the intermediate fields. ToS makes the reverse move—the same one as in Part X with set theory:

- a “field” is a *role-extension*—the bearer of the role “$ℚ$ with an adjoined surd,” given by finite data (pairs, records of coordinates), and *not* a self-standing object $L$;
- “the degree of an extension” is the *tier of a role*—how many storeys of surds the bearer needs: $1$ (the Elements of $ℚ$ themselves) $\subset 2$ (quadratic) $\subset 3$ (cubic) $\subset …$;
- an “algebraic number” is a *role-limit of a process* or a *finite coordinate with a rule* ($\sqrt2$ as a symbol with the rule $x^2=2$), not a point of a completed continuum;
- abstract completed objects—the abstract group $\Aut(L/K)$ for an arbitrary $L/K$, the algebraic closure of an arbitrary field, the general Abel–Ruffini theorem—are either *built concretely* for concrete extensions or honestly remain *outside* the construction (role-limits and backlog), as the map of boundaries (11.6) will explain.

The central thesis of Part XI. *Within the P4 ontology of ToS*, the substantive core of Galois theory is *which tier of degree your construction reaches* and *what the multiplicative norm form buys*. The symmetry of the roots is encoded not by the abstract group $\Aut(L/K)$ but *concretely* (automorphisms as explicit maps of coordinates, the group as their table). Algebra over $ℚ$ is, moreover, *constructive*: the algebraic layer of Part XI over $ℚ$ uses not a single axiom—not even L3 (the excluded middle).[^1]

### What This Part Claims—and What It Does Not

A short formula worth getting used to from the first page: ToS does *not* “formalize abstract Galois theory.” ToS realizes its *concrete degree-tier and norm-form shadow over $ℚ$*—and in doing so goes further than one might expect of a “shadow”:

- for the extension $ℚ[\sqrt2,\sqrt3]$ a *genuine* Galois correspondence is built: four explicit automorphisms, their Klein group $V_4$, the computed fixed subfields, and a concrete table of the correspondence “subgroup $\leftrightarrow$ subfield” (the full bijection is its mathematical reading)—not counts (Chapter 11.5);[^2]
- the unsolvability of the quintic receives a *genuine engine*, not a flag: an abstract definition of solvability via the derived series is given, and it is proved that *a perfect nontrivial group is not solvable*—the group core of Abel–Ruffini (Chapter 11.5);[^3]
- the algebraic closure of $ℚ$ turns out to be *not a wall but a process*—an ascending tower of finite extensions with no maximal rung (Chapter 11.6).[^4]

What ToS does *not* do: it does not build the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an *arbitrary* $L/K$ (only concretely, for concrete extensions); it does not prove the general Abel–Ruffini theorem and the Fundamental Theorem in full generality; it presents the simplicity of the group $A_5$ (heavy finite combinatorics) as an explicit premise rather than deriving it in the engine. This is an honest boundary—but a boundary that, as 11.6 will show, is *much narrower* than the classical one: almost everything usually called a “wall” turns out to be either a backlog of labor or one of the two prices already named in Part X (the Axiom of Choice for arbitrary fields; the continuum for embedding into $ℝ$/$\mathbb{C}$).

*Part XI is the algebraic tier of the same optics: a field is a role-extension, a degree a tier, symmetry a concrete encoding. The substantive core of Galois-in-ToS is the reachable tier of degree and the work of the norm form, not a completed abstract object.*

## Field as Role-Extension

The bearer that the classical theory calls “the field $ℚ[\sqrt d ]$” is in ToS a *role-extension*: $ℚ$, playing the role of the base, with the adjoined symbol $\sqrt d$ under the rule $(\sqrt d)^2=d$. An element of such a field is not a point of a mysterious continuum but *finite data over $ℚ$*: a pair $(a,b)$ meaning $a+b\sqrt d$. Addition and multiplication are defined on pairs by the rules[^5]

$$
(a,b)+(c,d) = (a+c,\;b+d), \quad
  (a,b)\cdot(c,d) = (ac+bd d,\;ad+bc),
$$

and every nonzero element has the norm $N(a+b\sqrt d)=a^2-d b^2\inℚ$, by which the inverse is built. The field does not precede these rules as an object—it is *constituted* by them as a role.

A decisive subtlety, echoing all of Parts II–IV. In the *field* $ℚ[\sqrt2]$ the symbol $\sqrt2$ is a *finite coordinate* with the rule $x^2=2$, *not* the analytic Cauchy process $( n\mapsto$ approximation $)$. These are two different representations of one number: the *analytic* one (a role-limit of a process, P4-infinite) and the *algebraic* one (a finite symbol plus a rule). The algebraic representation *terminates in finite data*—and therefore algebraic numbers are in this sense *more P4-actual* than a general real, which needs a nonterminating process. The same finiteness lets ToS distinguish roles within an extension: $i\inℚ[i]$ has *finite order* ($i^4=1$, an Element-role of the group $ℤ_4$), as does $\omega\inℚ[\omega]$ with $\omega^3=1$ (an Element-role of $ℤ_3$), whereas $\sqrt2$ is not a root of unity (infinite multiplicative order); its process reading is the topic of Chapter 11.2.

Multistorey extensions remain just as finite. The field $ℚ[\sqrt2,\sqrt3]$ is *quadruples* of rational coordinates: an element is

$$
a + b\sqrt2 + c\sqrt3 + d\sqrt6, \quad (a,b,c,d)\inℚ^4,
$$

with the rules for multiplying surds $\sqrt2\cdot\sqrt2=2$, $\sqrt3\cdot\sqrt3=3$, $\sqrt2\cdot\sqrt3=\sqrt6$, $\sqrt6\cdot\sqrt6=6$. This is a *record* (Record) of four fields with values in $ℚ$—exactly the object on which Chapter 11.5 will present the genuine automorphisms and the Galois correspondence.[^6]

Here the generating order of ToS is at work: *Rules* $\to$ *Roles* $\to$ *Elements*. First the *rule* of algebraicity ($x^2=d$, the minimal polynomial) sets what is adjoined at all; then the *role* of the extension is defined (a base with an adjoined surd); and only then do the *elements* become clear—the actual finite coordinates at each stage.

*A field is a role-extension of $ℚ$ by an adjoined surd, given by finite coordinates; $\sqrt d$ in a field is a finite symbol with the rule $x^2=d$, not a Cauchy process. An algebraic number is algebraically finite; it becomes a role-limit only in the analytic representation.*

## Degree as the Tier of a Role

If a field is a role-extension, then its *degree* $[L:ℚ]$ is the *tier of the role*: how many independent storeys of surds the bearer carries. The degree is not an abstract number attached to a ready object but a *measure of the height of a construction*. The base tier is $ℚ$ itself (degree $1$, pure Elements). Adjoining a square surd raises it to tier $2$: $[ℚ[\sqrt2]:ℚ]=2$. The supporting polynomial here is $x^2-2$, and its degree is computed as $2$;[^7] it turns out to be *minimal* because it has no rational root—and this is exactly the irrationality of $\sqrt2$ (a polynomial of degree $2$ without a rational root is irreducible over $ℚ$).[^8]

The tiers combine by the tower law. For $ℚ[\sqrt2,\sqrt3]$ the expected tier $4$ is confirmed by *two independent layers*. The first is the *nondegenerate tower* $2\cdot2$: each storey is an honest extension of degree $2$ (see below). The second is the *four explicit automorphisms* ($\mathrm{id}$; $\sigma:\sqrt2\mapsto-\sqrt2$; $\tau:\sqrt3\mapsto-\sqrt3$; their composition $\sigma\tau$), pairwise distinct in their action on the surds, so that the symmetry group has four elements (the Klein group $V_4$). In the formalization this is laid out as a *coincidence* of the dimension of the basis with the order of the group: $[ℚ[\sqrt2,\sqrt3]:ℚ]=|\Gal|=4$.[^9]

What makes this tier *genuine* rather than bookkeeping of coordinates is the *nondegeneracy of the tower*: the second storey does not reduce to the first. It is proved that $\sqrt3\notinℚ[\sqrt2]$—no pair $(a,b)$ gives $(a+b\sqrt2)^2=3$. The proof is purely algebraic over $ℚ$, without any embedding into $ℝ$: if $a+b\sqrt2$ squared equals $3$, then $2ab=0$ and $a^2+2b^2=3$; for $b=0$ we get $a^2=3$ (no rational root), for $a=0$, $(2b)^2=6$ (no rational root).[^10] Thus the tower $ℚ\subsetneqℚ[\sqrt2]\subsetneqℚ[\sqrt2,\sqrt3]$ is nondegenerate: each step is an honest extension of degree $2$.

Degree-as-tier immediately turns into a *measure of obstruction*—the topic of Chapters 11.2 and 11.3. Doubling the cube and trisecting the angle require reaching tier $3$ (a cubic minimal polynomial), unreachable by the quadratic tower ($\sqrt2$-tools); this is not a “shortage of tools” but a *rule about the tier*. But this is running ahead: here it matters only that degree in ToS is a role-tier of a construction, not a property of a completed object.

*Degree is the tier of a role-extension: $[ℚ[\sqrt2]:ℚ]=2$, $[ℚ[\sqrt2,\sqrt3]:ℚ]=4$ (proved: four automorphisms ${}={}$ the order of the group; the tower $2\cdot2$). The tier is genuine because $\sqrt3\notinℚ[\sqrt2]$—the tower is nondegenerate.*

## The Framework of a Field: The Abstract Structure and Its Role

A legitimate question arises: where, then, is the *abstract* field—a structure with axioms of associativity, distributivity, and invertibility? In ToS it *is there*—as a *framework*: a record with operations and the proved axioms of a ring and a field.[^11] But the role of this framework in ToS differs from its role in the classical theory. The classical theory *starts* from the abstract field and descends to examples; ToS starts from *concrete degree-tiered extensions* and keeps the abstract record as a *confirming frame*—a check that the concrete $ℚ[\sqrt d ]$ do indeed satisfy the axioms.

This is the same “level B” discipline as in the whole book: *the theory leads, the repository confirms*. The abstract `Record Field` is not the substantive core of the part—the core remains the reachable tier of degree and the norm form. The framework is instantiated by concrete extensions, not the other way around; and precisely because the concrete is finite and computable, the whole cluster does without axioms.

*The abstract structure of a field is a role-framework (a record with axioms) that confirms the concrete extensions, not a primary object. The theory leads with the concreteness of tiers; the record $\mathrm{Field}$ certifies it.*

## E/R/R Analysis

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the minimal polynomial as the rule of algebraicity ($\sqrt2\mapsto x^2-2$); the rules for multiplying surds ($\sqrt2\cdot\sqrt2=2$, $\sqrt2\cdot\sqrt3=\sqrt6$); the tower law of tiers ($2\cdot2=4$); the ring/field axioms as the rule of a well-formed structure |
| *Roles* (L4) | field ${}={}$ role-extension ($ℚ$ with an adjoined surd); degree ${}={}$ the tier of a role ($1\subset2\subset3$); $\sqrt2$ ${}={}$ a formal generator / a finite coordinate with the rule $r^2=2$ (the process reading—11.2); $i,\omega$ ${}={}$ finite algebraic roles (a preview of 11.4–11.5) |
| *Elements* (L1${}+{}$P4) | at each stage, finite data over $ℚ$: pairs $(a,b)\inℚ[\sqrt d ]$, quadruples $(a,b,c,d)\inℚ[\sqrt2,\sqrt3]$, lists of coefficients of a polynomial; the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an arbitrary $L/K$ is *not* an Element |

**Well-formedness.** An extension is well-formed as an algebraic structure: the coordinates are closed under $+,\cdot$ and have a norm in $ℚ$; a tier is well-formed when the tower is nondegenerate ($\sqrt3\notinℚ[\sqrt2]$); the abstract record, by the ring/field axioms. Each component falls into exactly one E/R/R category.

**What it yields.** Extensions of $ℚ$ are finite pairs/records, 0 axioms. Degree is a tier with a proved tower law ($[ℚ[\sqrt2,\sqrt3]:ℚ]=4$). The genuineness of the tier is a theorem of independence. The abstract field is a confirming framework, not a source.

**Diagnosis.** The root error that the chapter removes is the reification of *the field and its degree as a completed object*. ToS returns them to their category: a field is a role, a degree is a tier of a construction.

**Honest boundaries.** The abstract $\Aut(L/K)$ for an arbitrary $L/K$ is not built here (concretely—in 11.5 for $ℚ[\sqrt2,\sqrt3]$). The general tower law for arbitrary extensions is not proved—only for concrete quadratic families. The detailed map of boundaries is in 11.6.

*A field is a role-extension; a degree is a tier; the minimal polynomial and the rules of surds are rules; the abstract record is a framework. The substantive core is the reachable tier, not a completed object.*

## Summary and Transition

The chapter has laid the foundation of Part XI: a field is a role-extension given by finite coordinates over $ℚ$, and a degree is the tier of a role, measuring the height of a construction. The tower $ℚ\subsetneqℚ[\sqrt2]\subsetneqℚ[\sqrt2,\sqrt3]$ is nondegenerate, degree $4$ is proved through four automorphisms and the independence of $\sqrt3$ from $ℚ[\sqrt2]$, and the abstract record of a field plays the role of a confirming framework, not of a primary source. All of this without axioms.

Further on, Part XI unfolds this optics. Chapter 11.2: the algebraic number as a role-limit of a process and the minimal polynomial as a rule; the rational root test in general form. Chapter 11.3: constructibility as reachability by tier $2$ and the Greek impossibilities (trisection, doubling the cube, the heptagon) as going beyond this tier. Chapter 11.4: symmetry groups over $ℚ$, the crystallographic restriction and norm forms (the Hurwitz tower $1,2,4,8$), and also the finite fields $\mathbb{F}_p$. Chapter 11.5 is the center: the genuine Galois correspondence for $ℚ[\sqrt2,\sqrt3]$ and the engine of the unsolvability of the quintic. Chapter 11.6: synthesis and an honest map of boundaries—where the boundary turns out to be narrow compared with the classical one.

*A field is a role-extension, not an object; a degree is the tier of a role, not a property of a thing; an algebraic number is algebraically finite. Such is the frame in which Part XI rereads Galois: not as a completed functor but as the reachable tier of degree and the work of the norm form over the finitely actual $ℚ$.*

---

[^1]: A contrast with Part X, where comparing cardinalities (Schröder–Bernstein) relied on L3 plus `L4_witness`. Each of the listed files (`GaloisQ23`, `GaloisDegreeQ23`, `IndependenceQ23`, `SplittingFieldQ23`, `FiniteFieldFp`, `RationalRootTest`, `SolvableGroup`, `AlgebraicClosureProcess`) is “Closed under the global context” (0 axioms), as checked by `Print Assumptions` for each; for the broader algebraic cluster this is verified file by file.
[^2]: `GaloisQ23.v` (26 Qed, 0 axioms): `a_sig`, `a_tau`, `a_st`, and the fixed subfields.
[^3]: `SolvableGroup.v` (18 Qed, 0 axioms): `perfect_nontrivial_not_solvable`.
[^4]: `AlgebraicClosureProcess.v` (14 Qed, 0 axioms): `no_maximal_rung`, `germ_finitely_sited`.
[^5]: For $ℚ[\sqrt2]$ vs $ℚ[i]$, the concrete records and closure are in `CliffordField.v`: $ℚ[\sqrt2]$ *really* contains a square root of $2$ but does *not* contain $i$ (`i_not_in_Qsqrt2`), and $ℚ[i]$ does not contain $\sqrt2$ (`no_gaussian_sqrt2`).
[^6]: `GaloisQ23.v`: `Record E := mkE {c0 c1 c2 c3}` with the coordinatewise equality `Eeq` and the multiplication `Emul` implementing the rules of surds. This is the free $ℚ$-module on the basis $\{1,\sqrt2,\sqrt3,\sqrt6\}$.
[^7]: `FieldExtension.v`: `sqrt2_poly`${}=[-2;0;1]$ (that is, $x^2-2$), and `ext_degree_sqrt2_is_2` proves that the `poly_degree` of this polynomial equals $2$. The file itself *computes* the degree without proving irreducibility.
[^8]: `no_rational_sqrt2` (`analysis/Sqrt2Irrational.v`): $\forall r\inℚ,\ r\cdot r\neq2$. Hence the minimality of $x^2-2$ and the basis $\{1,\sqrt2\}$ in the mathematical reading.
[^9]: `GaloisDegreeQ23.v`: `galois_group_four_distinct` (the four automorphisms are pairwise distinct), `ext_degree`${}={}$`galois_order`${}=4$, the tower law `tower_law`: $2\cdot2=4$. Degree $4$ here is the dimension of the formal model (the free $ℚ$-module on the basis $\{1,\sqrt2,\sqrt3,\sqrt6\}$), which coincides with the number of automorphisms; its faithfulness to the real field is secured by the nondegeneracy of the tower (below).
[^10]: `IndependenceQ23.v`: `sqrt3_not_in_Qsqrt2`, relying on the irrationality of $\sqrt3$ and $\sqrt6$. Together with `GaloisDegreeQ23.v` this makes degree $4$ genuine rather than a formal dimension.
[^11]: `RingField.v`: `Record Ring` and `Record Field` with the full set of axioms. Similarly `GroupTheory.v`: `Record Group` (see also the solvability engine of Chapter 11.5, where the abstract group is used in earnest).

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/10 Set Theory without the Axiom of Choice/06 Synthesis What Is Provable without Choice and Map of Boundaries|Chapter 6. Synthesis of Part X: What Is Provable without Choice, and the Map of Boundaries—Part X]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/02 Algebraic Number as Role Limit Minimal Polynomial|Chapter 2. Algebraic Number as Role-Limit; Minimal Polynomial]] →
