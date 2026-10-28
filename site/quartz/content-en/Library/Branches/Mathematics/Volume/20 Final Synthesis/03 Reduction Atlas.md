---
title: "Chapter 3. The Reduction Atlas"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/20 Заключительный синтез/03 Редукционный атлас.md"
sourceBlob: b4705494143049beed4a3e47fe07302851aaeee6
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

The two previous chapters outlined the finitization boundary and refined it. The first fixed the line itself: every object given by a rule of generation either terminates in finitely many steps in a terminus-Element or provably does not terminate and remains a role-limit. The second refined the role-limit side—it is an unbounded process, not a cutoff of the substrate. Both chapters spoke of the boundary *in general*.

Meanwhile, this boundary was established not abstractly but on a multitude of particular cases. In geometry: the integer lattice has no equilateral triangle, and among the regular polygons only the square embeds. In dynamics: a rational rotation closes into a finite cycle only for a few angles, while the “three-four-five” rotation never closes. In number theory: a square root has a rational value only for a perfect square. In information theory: the signs of the Walsh basis are only $\pm1$. Each such case was proved separately, by its own device; sixty-eight such facts accumulated, scattered across different areas.

The present chapter removes this appearance of multiplicity. It shows that dozens of domain facts are not dozens of independent theorems but *five engines*; and that the five engines are five readings of *one* integer $2\times2$ matrix. The compression proceeds in two steps: many domain facts $\to$ five numerical engines $\to$ one matrix with one gate[^1]. This gate is one integer, and the question about it is decidable.

## What the Chapter Establishes and What It Does Not

Honesty is needed here too. The following is *machine-checked*: each of the five engines is an identity in the ring of integers or an elementary fact about integers, and the connecting loop—“a rational eigenvalue implies a square discriminant”—is one identity of completing the square[^2]. Each engine names its domain dichotomy by one integer invariant, and this naming is checkable.

What is *not* asserted is a new universal theorem about the world. “Five engines,” “one matrix” is a *structural synthesis*, an organizing observation on top of the accumulated particular cases, not a single meta-theorem running over all conceivable areas. Its value is compression and clarity: to show that the boundary, wherever it shows through, is read off one integer invariant. This is the level of a generalizing *observation* backed by a checked core, not a new claim.

A second caveat is also needed. Four engines out of five are, in the direct sense, invariants of the $2\times2$ matrix—its determinant, trace, characteristic polynomial, and the squareness of its discriminant. The fifth—parity—is not an invariant of the eigenvalues but the *reduction of the matrix modulo two*, its combinatorial shadow on the Element side. It enters the overall picture as a coordinate of another kind, and this is said directly below.

## Five Engines

Each engine names a domain dichotomy by *one integer held at a special value*. Let us list them in order of increasing structure.

**I. The surd index.** The process $\sqrt D$ terminates in a rational Element if and only if $D$ is a perfect square; otherwise it is a role-limit. The locking integer is the “scaled square”: for a non-square $D$ there is no equality $m^2 = D k^2$ with $k\ge1$. This is an engine in *obstructive* form—it names what does *not* occur[^3].

**II. The unimodular determinant.** The integer determinant $ad-bc$, held at the value $\pm1$, means *adjacency*: the neighborliness of Farey fractions, the tangency of Ford circles, the irreducibility of the descendants in the tree enumerating the rationals, the primitivity of a lattice triangle. The generating move—adding one column to another—preserves the determinant; it is an elementary generator of the group $\mathrm{SL}_2(ℤ)$[^4].

**III. The norm form.** The expression $x^2 - D y^2$ is the norm in the ring $ℤ[\sqrt D]$, and the norm is *multiplicative* (Brahmagupta’s identity). This engine carries *both* sides of the boundary at once: held at $\pm1$, the norm generates a tower of approximations to $\sqrt D$ (the side of approximation); never becoming zero, it gives an integer floor (the side of obstruction, as in the previous chapter)[^5].

**IV. The integer trace.** Twice the cosine of the angle, $2\cos\theta$, is the trace of a unimodular transformation. A rotation has finite order if and only if this trace is an integer and lies in $\{-2,-1,0,1,2\}$; outside this set the order is infinite. The trace runs through an integer recurrence, and its growth or return decides periodicity[^6].

**V. Parity.** The sign of the Walsh basis is the parity character—$(-1)^{ \text{popcount}(i\wedge j)}$, minus one raised to the parity of the number of common one-bits. It is a homomorphism from addition to multiplication of $\pm1$; from it follow both that all entries are $\pm1$ and the orthogonality of the whole construction. This is the *purely Element* side: no role-limit, except in the normalization[^7].

Five engines, five integer invariants at special values. It remains to show that these are not five scattered devices but five readings of one structure.

## One Matrix

Take an integer $2\times2$ matrix

$$
M \;=\; \begin{pmatrix} a & b \\ c & d \end{pmatrix}, \quad a,b,c,d \in ℤ.
$$

It has two basic invariants: the *determinant* $\det M = ad-bc$—engine II—and the *trace* $\operatorname{tr} M = a+d$—engine IV. Its characteristic polynomial is $x^2 - (\operatorname{tr} M) x + (\det M)$, and its *discriminant* is

$$
\Delta \;=\; (\operatorname{tr} M)^2 - 4\det M \;=\; (a-d)^2 + 4bc.
$$

The connecting link is completing the square. For any integer $x$

$$
4\bigl(x^2 - t x + e\bigr) \;=\; (2x - t)^2 - \bigl(t^2 - 4e\bigr).
$$

Setting $t=\operatorname{tr} M$ and $e=\det M$, we obtain: if $x$ is an integer *eigenvalue* of the matrix, that is, a root of its characteristic polynomial, then the right-hand side reduces to its first term, and

$$
\Delta \;=\; (2x - \operatorname{tr} M)^2
$$

is a *perfect square*[^8].

Thus three engines converge in one matrix: the determinant (II) and the trace (IV) are its coefficients, and the surd (I) is the squareness of their discriminant. The fourth, the norm form (III), is the determinant of the regular representation—a determinant of the same breed. And the fifth, parity (V), reads the reduction of the matrix modulo two; and the Hadamard matrix $\bigl(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\bigr)$, whose entries are values of the parity character, connects it with the rest: its discriminant equals $8$.

To each engine there corresponds an explicit matrix, on which its invariant is seen directly[^9]:

$$
\begin{array}{llll}
    \text{(II)} & \begin{pmatrix}1&1\\1&0\end{pmatrix}
      & \det = -1 & \text{unimodular, adjacency;} \\[1.6ex]
    \text{(IV)} & \begin{pmatrix}1&-1\\1&0\end{pmatrix}
      & \operatorname{tr}=1,\ \det=1,\ \Delta=-3 & \text{elliptic, order six;} \\[1.6ex]
    \text{(III)} & \begin{pmatrix}3&4\\2&3\end{pmatrix}
      & \det=1,\ \Delta=32 & \text{Pell unit, } \sqrt2; \\[1.6ex]
    \text{(V)} & \begin{pmatrix}1&1\\1&-1\end{pmatrix}
      & \det=-2,\ \Delta=8 & \text{Hadamard, } \sqrt2.
  \end{array}
$$

The discriminant $\Delta=8$ is *not* a perfect square—there is no integer square between $2^2=4$ and $3^2=9$—and therefore the Hadamard matrix has no rational eigenvalue: its eigenvalues $\pm\sqrt2$ are a role-limit.

The elliptic case (engine IV, $\Delta=-3$) stands apart: the discriminant is negative and not a square, but the eigenvalues are complex roots of unity, and the rotation is of *finite order* (here, six). Closure here is decided not by a real $\sqrt\Delta$ but by the integer trace in the set $\{-2,…,2\}$ (engine IV); the matrix $\bigl(\begin{smallmatrix}1&-1\\1&0\end{smallmatrix}\bigr)$ is a representative in $GL_2(ℤ)$, not the standard orthogonal rotation matrix.

## The Discriminant as a Gate

Now let us reduce everything to one thing. In the atlas instances reduced to such a matrix, the status of an object—a finitely actual Element or a role-limit—is read off its $2\times2$ matrix by *one* question:

*Is the discriminant $\Delta = (\operatorname{tr} M)^2 - 4\det M$ a perfect square?*

If yes (and $\Delta\ge0$), the eigenvalues are rational ($\lambda=(t\pm\sqrt\Delta)/2\inℚ$), and the object lands rationally: it is an *Element*. If $\Delta>0$ is not a square, the eigenvalue is the non-terminating process $\sqrt\Delta$: it is a *role-limit*. And for $\Delta<0$ the case is *elliptic* (complex roots): termination there is decided not by $\sqrt\Delta$ but by the integer trace (engine IV), and the finite order closes. Thus *one decidable arithmetic question for a given matrix* separates a rational landing from an irrational one, and the elliptic case adds the trace.

It is to this gate that the sixty-eight particular cases converge. There is no equilateral triangle on the lattice—because the discriminant corresponding to it leads to $\sqrt3$. A rotation of the fifth order is ruled out—$\sqrt5$. The correlation optimum is rationally unreachable—$\sqrt8$. There is no rational bisection of the right angle, as in the Hadamard normalization—$\sqrt2$[^10]. In each case, its own matrix, its own discriminant, one and the same question.

*Sixty-eight domain facts—five engines—one matrix with one gate.*

This is the deepest compression available at the present level. The role-limit remains, as everywhere in this work, the *process* $\sqrt\Delta$—not a completed number but an unbounded approximation; the gate only says on which side of the boundary the object stands, without turning the irrational into a ready object.

## E/R/R Analysis: The Atlas as a System

The atlas itself is a *system* in the sense of ToS, and it should be analyzed by E/R/R. Epistemically we went from particular facts (Elements) to their common law (Rules); ontologically the structure is generated in the reverse, generating order: Rules $\to$ Roles $\to$ Elements.

**Rules (L5).** The holding rule is the *rule of reading*: the status of an object is read off its $2\times2$ matrix through the discriminant. Completing the square connects the trace and the determinant with the surd; the squareness of the discriminant is the deciding criterion—a perfect square separates a rational eigenvalue from an irrational one. This rule stands above all the particular matrices and sets their status.

**Roles (L4).** The roles that a matrix plays: *Element* (the discriminant is a perfect square, $\Delta\ge0$, a rational eigenvalue, the process terminates) and *role-limit* ($\Delta>0$ is not a square, the eigenvalue is the non-terminating process $\sqrt\Delta$); the *elliptic* case ($\Delta<0$) stands apart, where the role is decided by the integer trace (engine IV). The positions are grounded by structure: the role is defined not by the “nature” of the object—whether it is a circle, a rotation, a fraction, or a correlation—but by one integer, the discriminant of its matrix, that is, by its relation to the Rules.

**Elements (L1 + P4).** The bearers are explicit integer $2\times2$ matrices and their integer invariants: the determinant, the trace, the discriminant. Actualization under P4 is finite: the matrices and their integer coordinates are actual; the eigenvalue of the non-square side, $\sqrt\Delta$, is *not* actualized as an Element—only approximations to it are actual. The fifth coordinate, parity, is the reduction of the matrix modulo two—the combinatorial shadow of the same structure on the Element side.

**Well-formedness check.** In this atlas classification every matrix receives a role by its integer invariants (the discriminant and the trace): a perfect square is a rational landing, $\Delta>0$ not a square is a role-limit, $\Delta<0$ is the elliptic case. For integer invariants this is decidable; there is no third *status* after classification. There is no self-application, which P1 rules out: the rule of reading stands one level above the matrices it sorts and does not sort itself as a matrix.

**What the analysis yields.** First, it shows that the diversity of the sixty-eight cases is only apparent: geometry, dynamics, number theory, and information theory spoke of one matrix in different languages. Second, it names the gate of the boundary: the question “is the object finitely actual?” is exactly “does its $2\times2$ matrix have a rational eigenvalue?”, that is, “is its discriminant a perfect square?”—one decidable arithmetic question.

With this the synthesis of the finitization boundary (Chapters 20.1–20.3) is complete. The finitization boundary, which the first chapter fixed and the second refined as an unbounded process, appears here, on top of all the particular cases, as one arithmetic gate: the squareness of the discriminant of a $2\times2$ matrix. From here on the work uses this atlas as a ready map—reducing every new domain dichotomy to its matrix and to one question about an integer.

---

[^1]: Six files make up this atlas: one for each engine and one synthesizing file. The synthesis is `reduction_atlas_synthesis`; below we refer to the individual engines by their synthesis theorems. All statements are checked without axioms.
[^2]: All theorems of the chapter are checked as “Closed under the global context”: without the Law of Excluded Middle and without additional witness axioms. The connecting loop is `eigenvalue_forces_square_disc`, which relies on the identity `char_poly_complete_square`.
[^3]: The synthesis of the engine is `surd_atlas`. One and the same question, “is it a perfect square?”, put to different $D$ explains why there is no equilateral triangle on the lattice ($D=3$), why a rotation of the fifth order is ruled out ($D=5$), and why the correlation optimum is a role-limit ($D=8$).
[^4]: The synthesis is `unimodular_atlas`. The mediant, Ford tangency, lowest terms, Pick’s area—one identity about columns and one invariant $|\det|=1$.
[^5]: The synthesis is `pell_atlas`. The norm is the determinant of the regular representation of the number $x+y\sqrt D$—which directly connects engine III with engine II.
[^6]: The synthesis is `niven_trace_atlas`. The trace is the second invariant of the $2\times2$ matrix—a full sibling of the determinant of engine II; together they exhaust its characteristic polynomial.
[^7]: The synthesis is `parity_atlas`. The whole Element side of the Walsh constructions rests on this character; its only contact with the role-limit is the normalization factor $\sqrt2$.
[^8]: The core proves the necessary direction: an integer root of the characteristic polynomial implies a square discriminant (`eigenvalue_forces_square_disc`). The converse—“a square $\Delta\ge0$ $\Rightarrow$ a rational eigenvalue”—follows from the quadratic formula $\lambda=(t\pm\sqrt\Delta)/2$ (an integer one under a parity condition). The identity of the discriminant $\Delta=(a-d)^2+4bc$ is `disc_eq`.
[^9]: The four witnesses are `instance_unimodular`, `instance_finite_order`, `instance_pell`, `instance_hadamard`; the impossibility of $m^2=8$ is `no_square_8`.
[^10]: Here the line joins the application to physics of the previous chapter: $\sqrt2$ in the Hadamard normalization, $\sqrt8$ in the correlation optimum—these are the same role-limits, now read as non-square discriminants of explicit $2\times2$ matrices. The physical images serve as an illustration of a single numerical form, not as the subject of the volume.

---

Part: [[20 Final Synthesis|Part XX. The Final Synthesis]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[Library/Branches/Mathematics/Volume/20 Final Synthesis/02 Finitization without Cutoff|Chapter 2. Finitization without Cutoff]] · [[Library/Branches/Mathematics/Volume/20 Final Synthesis/04 Construct or Name|Chapter 4. Construct or Name]] →
