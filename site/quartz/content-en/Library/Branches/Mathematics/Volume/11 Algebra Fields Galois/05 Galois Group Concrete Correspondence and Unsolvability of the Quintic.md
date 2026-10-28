---
title: "Chapter 5. Galois Group: Concrete Correspondence and Unsolvability of the Quintic"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/11 Алгебра, поля, Галуа/05 Группа Галуа конкретное соответствие и неразрешимость квинтики.md"
sourceBlob: b3266f72a915e8f0114493ea02869e9d8cff89a4
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

This is the center of Part XI. Chapters 11.1–11.4 put up the scaffolding: the field as a role-extension, the degree as a tier, the algebraic number as a role-limit with a minimal polynomial, constructibility as tier $2$, finite multiplicatively stable structures. Now comes the *symmetry of the roots* itself: the Galois group, which organizes the solutions of an equation.

The chapter presents two results of ToS, and both are *genuine*, not imitations:

1. **A genuine Galois correspondence for $ℚ[\sqrt2,\sqrt3]$.** Four explicit automorphisms, their Klein group $V_4$, and the *computed* fixed subfields—an explicit table of the correspondence “subgroup $\leftrightarrow$ intermediate field,” not merely a coincidence of *counts*.
2. **A genuine engine of the unsolvability of the quintic.** An abstract definition of solvability via the derived series and a proved theorem: *a perfect nontrivial group is not solvable*—the group core of Abel–Ruffini, not a flag.

The Galois correspondence in ToS lives on two levels. The coarse one is the *numerical shadow*: the count of subgroups ${}={}$ the count of fields ($5=5$), and the unsolvability of the quintic is a *flag-definition* (`s5_is_solvable := false`). The precise one is the *concrete table of the correspondence* for $ℚ[\sqrt2,\sqrt3]$ and the *group engine* of unsolvability as a theorem under an explicit premise.[^1] The honest frame (in detail in 11.6): the correspondence is *concrete* (for $ℚ[\sqrt2,\sqrt3]$, not the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an arbitrary $L/K$); the engine of unsolvability is *complete*, but the simplicity of $A_5$ enters as an explicit *premise* and is not derived; there is no full Abel–Ruffini theorem in general form.

*The center of Part XI: the symmetry of the roots. Two concrete results—the table of the Galois correspondence for $ℚ[\sqrt2,\sqrt3]$ and the engine of unsolvability (perfect$ \Rightarrow$ not solvable).*

## A Genuine Galois Correspondence for $ℚ[\sqrt2,\sqrt3]$

Take the field $E=ℚ[\sqrt2,\sqrt3]$ from 11.1—quadruples of coordinates $a+b\sqrt2+c\sqrt3+d\sqrt6$. Its automorphisms are maps that preserve $+,\cdot$ and are fixed on $ℚ$. Four standard automorphisms are presented, each given by an *explicit* formula on the coordinates (in the mathematical reading they exhaust $\Gal(E/ℚ)$):[^2]

$$
\begin{gathered}
\mathrm{id}; \quad
  \sigma:\ \sqrt2\mapsto-\sqrt2\ (\sqrt3\ \text{fixed}); \\
  \tau:\ \sqrt3\mapsto-\sqrt3\ (\sqrt2\ \text{fixed}); \quad
  \sigma\tau:\ \text{both signs}.
\end{gathered}
$$

Each is an involution ($\sigma^2=\mathrm{id}$), and $\sigma\tau=\tau\sigma$; hence the four automorphisms form the *Klein group* $V_4$.[^3]

The main thing is that the *fixed subfields* here are not postulated but *computed*. An element is fixed by $\sigma$ exactly when its coordinates at $\sqrt2$ and $\sqrt6$ are zero, that is, when it lies in $ℚ[\sqrt3]$; and so for each automorphism:[^4]

$$
\mathrm{Fix}(\sigma)=ℚ[\sqrt3],\quad
  \mathrm{Fix}(\tau)=ℚ[\sqrt2],\quad
  \mathrm{Fix}(\sigma\tau)=ℚ[\sqrt6],\quad
  \mathrm{Fix}(V_4)=ℚ.
$$

Hence an *explicit table* of the Galois correspondence—an order-reversing matching of five subgroups with five intermediate fields:

$$
\{\mathrm{id}\}\!\leftrightarrow\! E,\quad
  \langle\sigma\rangle\!\leftrightarrow\!ℚ[\sqrt3],\quad
  \langle\tau\rangle\!\leftrightarrow\!ℚ[\sqrt2],\quad
  \langle\sigma\tau\rangle\!\leftrightarrow\!ℚ[\sqrt6],\quad
  V_4\!\leftrightarrow\!ℚ.
$$

The larger the subgroup, the smaller the fixed field; the reversal of inclusion is checked on a concrete link ($\mathrm{Fix}(V_4)=ℚ\subseteq\mathrm{Fix}(\sigma)=ℚ[\sqrt3]$).[^5] This is not “equal counts ($5=5$)” but the maps themselves and the subfields themselves; $|{\Gal}|=4=[E:ℚ]$ (11.1).

*For $ℚ[\sqrt2,\sqrt3]$ an explicit table of the Galois correspondence has been built: four explicit automorphisms (the group $V_4$), the computed fixed subfields ($ℚ[\sqrt3],ℚ[\sqrt2],ℚ[\sqrt6],ℚ$), and the order-reversing matching subgroup$ \leftrightarrow$ subfield—the maps and subfields themselves, not a numerical shadow.*

## The Symmetry Group of the Roots: From $S_3$ to $S_5$

In the general case the Galois group is the symmetries of the *roots* of a polynomial: the permutations of the roots that preserve all the algebraic relations among them. For a polynomial of degree $n$ (in the classical separable case) it is a subgroup of the symmetric group $S_n$.

The group $S_3$ is presented concretely: permutations as functions, transpositions, and a proved *noncommutativity* ($\sigma_{12}\sigma_{23}\neq\sigma_{23}\sigma_{12}$—they act differently already on the element 1).[^6] Noncommutativity is the first sign of rich symmetry: the group of the roots is no longer abelian.

For the *general quintic* (an equation of degree 5) the Galois group is $S_5$ of order $120$, containing the alternating group $A_5$ of order $60$; and $A_5$ is a *simple* nonabelian group.[^7] It is precisely the simplicity of the nonabelian $A_5$ that sets an insurmountable barrier: the passage $S_4\to S_5$ is the Abel–Ruffini threshold—$S_4$ is still solvable, $S_5$ no longer is.

*The Galois group is the role-symmetry of the roots; for degree $n$, a subgroup of $S_n$. $S_3$ is noncommutative (concretely), and for the quintic the group is $S_5$ ($120$), with the simple nonabelian $A_5$ ($60$). The jump $S_4\to S_5$ is the Abel–Ruffini threshold.*

## Unsolvability through the Derived Series

Why does the simplicity of $A_5$ rule out a solution by radicals? A solution by radicals is a tower of extensions, at each storey of which a root ($\sqrt[k]{\cdot}$) is added; in the language of groups this means that the group is *solvable*. ToS formalizes solvability *in earnest*—through the *derived series*:[^8]

$$
G \;\trianglerighteq\; [G,G] \;\trianglerighteq\; [[G,G],[G,G]] \;\trianglerighteq\; \cdots
$$

A group is *solvable* if this series reaches the trivial $\{e\}$. A *perfect* group is one that equals its derived subgroup, $G=[G,G]$: on it the series freezes and never reaches $\{e\}$.

Hence the engine—a proved theorem: *a perfect nontrivial group is not solvable*.[^9] This is the group core of Abel–Ruffini. On the positive side the engine is just as real: *an abelian group is solvable* (the series breaks off at once)—these are exactly the cyclic steps of radicals; for illustration, a concrete example $ℤ/2$ is built.[^10]

Now the quintic—in the *classical reading* on top of the engine. For $A_5$ the classical fact is this: its commutator subgroup is nontrivial and normal, and by simplicity it equals all of $A_5$—hence $A_5$ is perfect. Then the engine gives: $A_5$ (and $S_5$, which contains it) is not solvable, whence the general quintic is not solvable by radicals.[^11]

**An honest premise.** Where is the boundary here? The *engine* itself (perfect nontrivial$ \Rightarrow$ not solvable) is proved in full. But the *simplicity of $A_5$*—heavy finite combinatorics on 60 elements (an enumeration of normal subgroups)—is fed into the engine as an *explicit premise* “$A_5$ is perfect,” not derived inside it. This is a *premise, not an axiom*: the file remains at *0 axioms*; a heavy finite fact is simply taken as input. Given this premise, unsolvability follows *strictly*—a substantive theorem, not the flag `s5_is_solvable := false`.

*Solvability ${}={}$ the derived series reaches $\{e\}$; a perfect (self-derived) group does not. The theorem (0 axioms): a perfect nonabelian/nontrivial group is not solvable. The application to the quintic ($A_5$ perfect $\Rightarrow S_5$ not solvable) goes on top of the engine as a classical reading with explicit premises (the simplicity/perfectness of $A_5$, $A_5$ as the commutator subgroup of $S_5$); the engine itself is complete.*

## E/R/R Analysis and Honest Boundaries

Let us gather the structure of the chapter in the generating order.

| **Layer** | **Content** |
|---|---|
| *Rules* (L5) | the Galois correspondence as a rule (subgroup ${}\leftrightarrow{}$ fixed subfield, reversal of order); solvability as a rule (the derived series reaches $\{e\}$); composition of automorphisms / permutations |
| *Roles* (L4) | Galois group ${}={}$ the role-symmetry of the roots ($V_4$ for $ℚ[\sqrt2,\sqrt3]$; $S_n$ in general); solvability ${}={}$ a role-limit (the series collapses to $\{e\}$); unsolvability ${}={}$ a perfect core (a self-derived group) |
| *Elements* (L1${}+{}$P4) | finite data: four automorphisms as coordinate formulas, fixed subfields, the permutations $S_3/S_5$, steps of the derived series; the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an arbitrary $L/K$ is *not* an Element |

**Well-formedness.** The correspondence is well-formed: each automorphism is a homomorphism fixed on $ℚ$; the fixed subfields are computed; inclusion is reversed (on a concrete link). The engine is well-formed: solvability is defined via the derived series, and perfectness gives strict unsolvability.

**What it yields.** An explicit table of the correspondence $V_4\leftrightarrow$ subfields for $ℚ[\sqrt2,\sqrt3]$. A concrete noncommutative $S_3$ and a numerical layer of $S_5$ ($120$, $A_5$ as a marker of simplicity). A genuine engine: perfect nonabelian$ \Rightarrow$ not solvable; abelian$ \Rightarrow$ solvable. The unsolvability of the quintic under explicit premises (the classical reading).

**Diagnosis.** The root error is the reification of *the Galois group as a completed object-functor* and the “solution” of an equation through the properties of this object. ToS: symmetry is encoded *concretely* (automorphisms, permutations), and unsolvability is a structural property (a perfect core), not the magic of abstraction.

**Honest boundaries (the key point).** *(a)* The correspondence is built for the
*concrete* $ℚ[\sqrt2,\sqrt3]$ (an explicit table, without a separate bijection object and without a classification of all automorphisms); the abstract correspondence $L/K\mapsto\Aut(L/K)$ for an arbitrary $L/K$ and the Fundamental Theorem in full generality are not built. *(b)* The engine of unsolvability is complete (perfect$ \Rightarrow$ not solvable, 0 axioms), but the simplicity of $A_5$ is taken as a *premise* (heavy finite combinatorics—backlog labor, not an axiom). *(c)* There is no full Abel–Ruffini theorem (quintic$ \to S_5$ via irreducibility ${}+{}$ the equivalence “radical tower ${}\Leftrightarrow{}$ solvable group”). Important: *there is not a single new P4 exclusion here*—everything not done is of the kind “labor / role-limit” (in detail, 11.6).

*The Galois group is the role-symmetry of the roots, encoded concretely (the explicit $V_4$ correspondence); unsolvability is a perfect core (the engine, 0 axioms, under the premise of the simplicity of $A_5$). The boundary is labor and role-limits (the abstract functor, the full Abel–Ruffini), not a P4 exclusion.*

## Summary and Transition

The central chapter has given two genuine results. *The Galois correspondence* for $ℚ[\sqrt2,\sqrt3]$ is not a coincidence of counts but the four automorphisms themselves, the group $V_4$, the computed fixed subfields, and the order-reversing matching subgroup$ \leftrightarrow$ subfield (the full bijection is the mathematical reading of this explicit table). *The unsolvability of the quintic* is not a flag but an engine: solvability via the derived series, the theorem “a perfect nonabelian/nontrivial group is not solvable” (0 axioms); the application to $S_5$ goes on top of the engine under explicit premises about $A_5$. The concrete table of the correspondence and the substantive theorem are more precise than the numerical shadow and the flag-definition.

Next comes Chapter 11.6, synthesis and the map of boundaries. There the whole of Part XI will be assembled: Galois-in-ToS is tiers of degree ${}+{}$ norm forms ${}+{}$ a concrete correspondence ${}+{}$ an engine of unsolvability; and the narrow boundary will be honestly outlined. A special place will be taken by a rethinking: *the algebraic closure of $ℚ$ is not a wall but a process* (an ascending tower of finite extensions). It will turn out that Part XI contains not a single new P4 exclusion—only labor and role-limits, plus the two prices already named in Part X (choice and the continuum).

*The explicit $V_4$ correspondence and the engine of unsolvability are the center of Part XI: the symmetry of the roots, encoded concretely, and unsolvability as a perfect core. These are concrete results, not counts and a flag. The boundary is labor, not an exclusion; the synthesis and the map are in 11.6.*

---

[^1]: The numerical layer is `algebra/GaloisCorrespondence.v` (`v4_subgroup_count`${}=5={}$`biquadratic_field_count`, `s5_is_solvable`${}={}$`false`). The concrete table of the correspondence is `algebra/GaloisQ23.v`; the engine is `algebra/SolvableGroup.v` (both 0 axioms).
[^2]: `GaloisQ23.v`: `a_id`, `a_sig`, `a_tau`, `a_st`. The file checks their action, their being homomorphisms (`sig_add`/`sig_mul`, etc.), their fixing $ℚ$ (`base_fixed_by_all`), the compositions, and the fixed subfields; the *classification* “every automorphism is one of these four” is not proved in the file (mathematical reading).
[^3]: `sig_invol`, `sig_tau_eq_st` ($\sigma\circ\tau=\sigma\tau$), `V4_abelian` ($\sigma\tau=\tau\sigma$).
[^4]: `fix_sig_iff`: $\mathrm{fixed\_by}\ \sigma\ u \Leftrightarrow (c_1=0\wedge c_3=0)$, that is, $u\inℚ[\sqrt3]$; similarly `fix_tau_iff` ($ℚ[\sqrt2]$), `fix_st_iff` ($ℚ[\sqrt6]$), `fix_V4_iff` ($ℚ$).
[^5]: `correspondence_inclusion_reversing` (`GaloisQ23.v`)—one concrete inclusion; the full bijection of all five objects is the mathematical reading of this explicit table, not a separate formal object.
[^6]: `GaloisGroup.v`: `perm_compose`, `transpose`, `s3_non_commutative` (with the witnesses `s3_12_23_at_1`${}=2$ versus `s3_23_12_at_1`${}=3$); `s3_order`${}=6$.
[^7]: `GaloisCorrespondence.v`: `s5_order`${}=120$, `a5_order`${}=60$, `a5_is_simple`—this is a *numerical marker* (`a5_normal_subgroup_count`${}=2$), not a machine enumeration of all normal subgroups of $A_5$. This is a numerical/constant layer; the genuine engine of unsolvability is in §11.5.4.
[^8]: `algebra/SolvableGroup.v` (0 axioms): the abstract group `GroupStr`—a record in which the group axioms (associativity, the neutral element, the inverse) enter as *fields of the structure*, not as global axioms of the theory; further, the commutator, `IsDerived` (the derived subgroup as the smallest one containing all commutators), and the inductive predicate `SolvableFrom`.
[^9]: `perfect_nontrivial_not_solvable` (`SolvableGroup.v`): if $G$ coincides with its derived subgroup and contains a non-identity element, then $G$ is not solvable. Proved constructively, 0 axioms.
[^10]: `abelian_solvable` and `boolGroup_solvable` (`SolvableGroup.v`).
[^11]: The formal `quintic_galois_group_not_solvable` (`SolvableGroup.v`) proves precisely the engine: *a perfect nonabelian group is not solvable*. The links “$A_5$ is perfect,” “$A_5$ is the commutator subgroup of $S_5$,” and “the general quintic has the group $S_5$” are not derived in the file—they are supplied as explicit premises / the classical reading.

---

Part: [[11 Algebra Fields Galois|Part XI. Algebra, Fields, Galois]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/04 Symmetry Groups over Q Norm Forms Finite Fields|Chapter 4. Symmetry Groups over Q; Norm Forms; Finite Fields]] · [[Library/Branches/Mathematics/Volume/11 Algebra Fields Galois/06 Synthesis and Map of Boundaries|Chapter 6. Synthesis and the Map of Boundaries]] →
