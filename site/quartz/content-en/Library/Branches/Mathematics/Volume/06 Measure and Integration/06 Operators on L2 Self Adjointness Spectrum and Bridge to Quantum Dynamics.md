---
title: "Chapter 6. Operators on L²: Self-Adjointness, Spectrum, and the Bridge to Quantum Dynamics"
lang: en
translationOf: "Библиотека/Направления/Математика/Том Математика/06 Меры и интегрирование/06 Операторы на L^2 самосопряжённость, спектр и мост в квантовую динамику.md"
sourceBlob: 9054225edb6566a2ce5e97f6cc0244a87ba921a1
translated: 2026-10-20
status: draft
---

## Where the Chapter Stands

### From the Space to Its Operators

Chapter 6.5 assembled $L^2$: a space with an inner product, a squared distance, best approximation, orthonormal expansions, and completeness by construction. The present chapter, the last in Part VI, studies its *operators*: linear maps $T$ of the space into itself, and three questions about them—*self-adjointness*
($\langle Tf,g\rangle=\langle f,Tg\rangle$), the *spectrum* (eigenvalues and eigendirections), and *evolution* (how a state changes in time under the action of an operator). These three topics are the mathematical apparatus on which quantum mechanics stands; the chapter carries the line of Part VI to its natural exit into physics, leaving the physical payoff itself to physics.

### What Is Proved—and Where the Honest Boundary Lies

Let us stress the level: everything proved is the operator geometry of *finite rational truncations* (matrices over ℚ, finite sums, fixed $N$), the process core of a future $L^2$ theory; the completed $\ell^2/L^2$, the exact propagator, and an arbitrary compact operator are role-limits. Three levels of rigor, as everywhere in Part VI. *Proved without axioms* (on a finite support, at every stage): self-adjointness as the commutativity of a double sum; the Rayleigh identity $\langle Tf,f\rangle=\lambda\|f\|^2$; the orthogonality of eigendirections for distinct eigenvalues; the canonical $[a,a^\dagger]=1$ for the oscillator ladder and its infinite spectrum; the absence of a finite-dimensional realization of the canonical commutator; the conservation of the norm (probability) and of energy under isometric evolution. *Remains an honest boundary* (P4): the *existence* of an eigenvector for an arbitrary operator (“the supremum is attained”—over ℚ eigenvalues are in general irrational); the exact propagator $e^{-i\hat H t}$ (the complex exponential, continuous time); a complete orthobasis of an arbitrary compact operator. These are role-limits, not actualizable objects.[^1]

### The E/R/R Framework of the Chapter

We set out the framework of the system in the generating order Rules $\to$ Roles $\to$ Elements; the full analysis with a table and a check of correctness is in § “E/R/R Analysis: Operators on L^2 as a System.” The chapter introduces the system of operators on $L^2$.

**Rules ($\leftrightarrow$ L5).** Self-adjointness
$\langle Tf,g\rangle=\langle f,Tg\rangle$; the Rayleigh quotient; the orthogonality of eigendirections for distinct $\lambda$; the absence of a finite realization of the canonical commutator; the conservation of the norm and of energy under isometric evolution.

**Roles ($\leftrightarrow$ L4).** The operator $T$ is an observable (when self-adjoint); the eigenvalue $\lambda$ is a value of the observable; an eigendirection is a state with a definite value; the step $U$ is the propagator; $\psi_n$ is the state in time; the norm and the energy are invariants.

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The rational entries
of the matrix $T_{ij}$, the coordinates of states, the finite sums $\sum_{i,j<N}$, the steps $n$; the exact propagator, irrational eigenvalues, and the completed basis lie outside the elements.

The subsequent sections fill in the framework: § “Self-Adjoint Operators”—self-adjointness; § “The Spectrum: The Rayleigh Quotient and Orthogonality”—the spectrum; § “The Position Operator on a Lattice”—position; § “The Canonical Commutator: Why the Operators Are Unbounded”—the commutator; § “The Harmonic Oscillator: The Ladder and the Spectrum”—the oscillator; § “Evolution as a Process: Conservation of Probability and Energy”—evolution.

## Self-Adjoint Operators

An operator $T$ (a matrix over ℚ acting by $(Tf)_i=\sum_j T_{ij}f_j$) is *self-adjoint* if moving it to the other side of the inner product changes nothing:

$$
\langle Tf,g\rangle \;=\; \langle f,Tg\rangle .
$$

A sufficient condition is the symmetry of the matrix, $T_{ij}=T_{ji}$. The proof of this equality is exactly an *interchange of a double sum* (the discrete Fubini theorem from Chapter 5.7) plus symmetry: both sides unfold into $\sum_{i,j}T_{ij}f_j g_i$ and coincide after swapping the indices. Without axioms.[^2]

Self-adjointness is precisely the condition under which $T$ plays the role of an *observable* (a role in the E/R/R analysis, not a separate type in the code). In the current rational layer the eigenvalue in the formulation of an eigenpair already has type ℚ; therefore the chapter proves not the “reality of the spectrum” in the classical complex sense (there is no complex space here) but the rational spectral *structure* for presented eigenpairs: the Rayleigh quotient and orthogonality.

## The Spectrum: The Rayleigh Quotient and Orthogonality

Let $Tf=\lambda f$ be an eigenpair. The *Rayleigh quotient* links the eigenvalue with the energy of the direction: $\langle Tf,f\rangle=\lambda\|f\|^2$. Proved by direct computation, without axioms.[^3] The main spectral fact is *orthogonality*: eigendirections for *distinct* eigenvalues are mutually orthogonal. Indeed, for $Tf=\lambda f$, $Tg=\mu g$, and self-adjointness,

$$
\lambda\langle f,g\rangle=\langle Tf,g\rangle=\langle f,Tg\rangle=\mu\langle f,g\rangle,
$$

whence $(\lambda-\mu)\langle f,g\rangle=0$, and for $\lambda\ne\mu$ we get
$\langle f,g\rangle=0$. This is the structural core of the spectral theorem, proved constructively.[^4]

For a *diagonal* (compact) operator the spectrum is *discrete*: the eigenvalues $\lambda_n$ decrease to zero, which is expressed in process form: for every threshold only finitely many of them exceed it.[^5]

**The *structure* of the spectrum—Rayleigh, orthogonality, the discreteness
of the diagonal model—is proved without axioms.** But the *existence* of an eigenvector for an *arbitrary* self-adjoint operator—the attainment of the maximum of the Rayleigh quotient—remains an honest boundary: over ℚ eigenvalues are, as a rule, irrational (the root of the discriminant), and existence requires completeness / compactness—the same boundary as the attainment of a maximum in the analysis of Part V: a finite grid is accessible, while a sup on the continuum requires an additional layer. The structure we build; existence on the continuum we mark (P4).

## The Position Operator on a Lattice

The simplest physical operator is *position* $\hat q$. On a lattice of $N$ sites with positions $x_i$ it is *diagonal* and acts by multiplication:

$$
(\hat q f)_i \;=\; x_i f_i .
$$

That is, position does not mix the sites but only weights each by its position. Its eigendirections are the lattice sites themselves (the basis states $e_j$), and its eigenvalues are the coordinates of the sites:

$$
\hat q e_j \;=\; x_j e_j .
$$

And, being diagonal with rational $x_i$, position is automatically *self-adjoint*.[^6]

*Position is the model observable of ToS:* diagonal, rational, self-adjoint, with an explicit discrete spectrum—the lattice sites. Its companion, momentum $\hat p$ (on a lattice a *difference* operator, not the continuum $-i\hbar\partial_x$), cannot be diagonal—and it is precisely their joint behavior that leads to the next section.

## The Canonical Commutator: Why the Operators Are Unbounded

Quantum mechanics stands on the *canonical commutator* of position $\hat q$ and momentum $\hat p$, the relation $[\hat q,\hat p]=i\hbar \mathbf{1}$. It has a purely algebraic consequence that explains *why* $\hat q,\hat p$ must be unbounded (infinite-dimensional). The trace of a commutator is always zero—since
$\mathrm{tr}(AB)=\mathrm{tr}(BA)$ (again an interchange of a double sum)—whereas the trace of $c\cdot\mathbf{1}$ equals $c\cdot N$. Hence:

$$
[A,B]=c\cdot\mathbf{1}\ \text{on $N\ge1$ coordinates}\;\Longrightarrow\;c=0 .
$$

The canonical commutator with $c=i\hbar\ne0$ is *not realizable* by any finite matrices. Proved over ℚ, without axioms.[^7]

On a lattice this is seen explicitly: position $\hat q$ is diagonal (§ “The Position Operator on a Lattice”), and its commutator with the difference momentum has an *identically zero diagonal*—and therefore cannot be $i\hbar\mathbf{1}$. The defect is unavoidable.[^8]

*Finite Actuality (P4) does not accommodate the canonical commutator: it lives only as a process / an infinite-dimensional limit.* The theorem on the absence of a finite realization is itself the rigorous proof of this—a rare case in which the P4 boundary becomes a theorem.

## The Harmonic Oscillator: The Ladder and the Spectrum

The first *infinite-dimensional* quantum object, the harmonic oscillator, realizes the canonical algebra with *ladder* operators, creation $a^\dagger$ and annihilation $a$, whose canonical relation is

$$
[a,a^\dagger] \;=\; 1 .
$$

The number operator $N=a^\dagger a$ counts quanta, and the Hamiltonian of the oscillator has a spectrum growing without bound:

$$
E_n \;=\; n+\tfrac12,\quad n=0,1,2,…
$$

with ground energy $\tfrac12$ (not zero: the irremovable zero-point oscillation) and a constant step $1$ between levels. The spectrum is *infinite and unbounded*: the oscillator does not fit into any finite dimension, which agrees with the obstruction of § “The Canonical Commutator: Why the Operators Are Unbounded.”[^9]

Here “infinite spectrum” means the *formula for the levels* $E_n=n+\tfrac12$ as a process in $n$ (for every bound there is a higher level), not the spectral theorem for a completed self-adjoint operator on the full Fock space.

The state space of the oscillator, *Fock space*, is held as a process: as a process of finite truncations (the first $K$ levels), actual at every stage. The irrational factor $\sqrt n$ that enters the action of the ladder operators is introduced as an *abstract parameter* $s$ with $s^2=n$; the ladder algebra itself does not depend on it, and in the observables—the levels, the step, the commutator—the $\sqrt{\;}$ cancels, leaving rational quantities.

**The oscillator is a model of an infinite-dimensional observable in ToS:** the canonical algebra
$[a,a^\dagger]=1$ and the level formula (with unboundedness) are proved over ℚ without axioms; the completed operator on the full Fock space is a role-limit (a process of truncations), not an actualizable object.

## Evolution as a Process: Conservation of Probability and Energy

The Schrödinger equation $i\hbar \partial_t\psi=\hat H\psi$ sets a *unitary* evolution: the total probability is conserved. The exact propagator $e^{-i\hat H t}$, a complex exponential of continuous time, is unattainable over ℚ; ToS keeps its constructive core: the *discrete* evolution $\psi_{n+1}=U\psi_n$. If the step $U$ is an *isometry* ($\|U\psi\|=\|\psi\|$, discrete unitarity), then the norm is conserved at every step, $\|\psi_n\|^2=\|\psi_0\|^2$ for all $n$, proved by induction on the number of steps.[^10] The norm $\|\psi_n\|^2$ is the total probability; its constancy is the law of its conservation.

The second conservation law is *energy* $E(\psi)=\langle\psi,\hat H\psi\rangle$. If the step conserves energy (a discrete analogue of commuting with $\hat H$), then $E(\psi_n)=E(\psi_0)$ for all $n$, by the same induction.[^11] In general form this is the germ of Noether’s theorem: a symmetry of the evolution (commuting with an observable) implies the conservation of that observable—a line naturally continued in physics.

**Both conservation laws of quantum mechanics—of probability and of energy—are proved as
process facts, without axioms.** The exact propagator $e^{-i\hat H t}$ is a role-limit (continuous time, the complex exponential); the process $\psi_n$ approximates it, and the conservation laws already hold at the discrete step.

## E/R/R Analysis: Operators on $L^2$ as a System

### Analysis in the Generating Order

The framework was set at the beginning (§ “The E/R/R Framework of the Chapter”); here we unfold it with a table and a check of correctness (well-formedness), completing the analyses of Part VI. The reservation about the level is the same as before. The generating order is Rules $\to$ Roles $\to$ Elements.

**Rules ($\leftrightarrow$ L5).** Self-adjointness
$\langle Tf,g\rangle=\langle f,Tg\rangle$; the Rayleigh quotient
$\langle Tf,f\rangle=\lambda\|f\|^2$; the orthogonality of eigendirections for distinct $\lambda$; the canonical $[a,a^\dagger]=1$ of the ladder and the absence of a finite realization of the commutator ($[A,B]=c\mathbf{1}\Rightarrow c=0$); the conservation of the norm and of energy under isometric evolution. The universal layer is L1–L5 and P4, which moves the existence of an eigenvector, the exact propagator, and the completed basis beyond the boundary.

**Roles ($\leftrightarrow$ L4).** The operator $T$ is the role-observable (when self-adjoint). The eigenvalue $\lambda$ is the role-value of the observable; an eigendirection is the role-state with a definite value. Position $\hat q$ is the observable of location; the ladder $a,a^\dagger$ are the roles of lowering / raising a quantum. The step $U$ is the role-propagator; $\psi_n$ is the role-state in time. The norm and the energy are role-invariants (conserved quantities).

**Elements ($\leftrightarrow$ L1${}+{}$P4).** The bearers are finite at
every stage: the rational entries of the matrix $T_{ij}$, the coordinates of states, the finite sums $\sum_{i,j<N}$, the levels and steps $n=0,1,2,…$ The exact propagator, irrational eigenvalues, the completed Fock space, and the completed basis do not belong to the elements.

| **Component** | **What it determines** | **E/R/R** |
|---|---|---|
| self-adjointness; Rayleigh; orthogonality; $[a,a^\dagger]=1$; no finite CCR; conservation of norm / energy | HOW operators, spectrum, and evolution are arranged | Rules ($L5$) |
| observable operator; eigenvalue; position; ladder; propagator; invariants | WHAT FOR the bearers are significant: roles of observables and of evolution | Roles ($L4$) |
| $T_{ij}$; coordinates of states; sums $\sum_{i,j<N}$; levels and steps $n$ | WHAT exists at each stage (P4) | Elements ($L1$, P4) |

The analysis is well-formed: each component is in one category, without self-reference (P1). The operator and the propagator are roles over value-elements; the conservation laws are rules, not objects; the completed propagator lies outside the elements.

### What the Analysis Yields—and How Part VI Closes

The analysis shows that operator theory on $L^2$ in ToS is a process theory: the rules (self-adjointness, Rayleigh, orthogonality, the canonical ladder, the absence of a finite commutator, the conservation of norm and energy) are proved at finite stages without axioms, and the infinitary—the existence of an eigenvector, the exact propagator, the completed basis—is honestly moved to the P4 boundary and marked as a role-limit. The canonical commutator is not merely “moved out”: it is proved that finite actuality does *not accommodate* it—a rare case in which the P4 boundary itself becomes a theorem.

With this Part VI closes. It has gone from measure zero and the Lebesgue integral as processes (6.1–6.3) through the convergence theorems (6.4) to the spaces $L^1$, $L^2$ and their completeness by construction (6.5), and finally to operators, the spectrum, and quantum dynamics (6.6). The through-line is one: infinity is a property of processes, not of completed objects; every infinitary step is either proved as the constructibility of a limit or named and placed on the boundary. The resulting $L^2$ apparatus—the inner product, orthonormal expansions, completeness, self-adjoint operators, the spectrum, position and the oscillator, unitary evolution with the conservation of probability and energy—is a ready mathematical stage for quantum mechanics.

---

[^1]: The supporting files in the directory `src/process/`: `ProcessSelfAdjointSpectral.v`, `ProcessCompactSpectral.v`, `ProcessHarmonicLadder.v`, `ProcessCanonicalCommutator.v`, `ProcessPositionMomentum.v`, `ProcessSchrodingerEvolution.v`, `ProcessEnergyConservation.v`; the links are in `ProcessL2HilbertSynthesis.v`. According to the file headers and the synthesis file of the cluster, 0 axioms; the key theorems carry `Print Assumptions`.
[^2]: `adjoint_inner` in `ProcessSelfAdjointSpectral.v` (0 axioms): through the interchange of sums `q_sum_swap` and the symmetry `op_symmetric`. A diagonal operator is symmetric automatically.
[^3]: `rayleigh_eq` in `ProcessSelfAdjointSpectral.v` (0 axioms).
[^4]: `eigvec_orthogonal` in `ProcessSelfAdjointSpectral.v` (0 axioms): from `adjoint_inner` and the integral-domain property of multiplication in ℚ. A concrete diagonalization of the matrix $\bigl(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\bigr)$ over ℚ with eigenvalues $3$ and $-1$ and orthogonal eigendirections is checked by computation (`spectral_2x2_concrete`).
[^5]: `diag_spectrum_discrete` in `ProcessCompactSpectral.v` (0 axioms).
[^6]: `position_apply` ($(\hat q f)_i=x_i f_i$), `position_eigenpair` ($\hat q e_j=x_j e_j$, the eigenvalues are the sites), and `position_symmetric` in `ProcessPositionMomentum.v` (0 axioms); the supporting lemma is the extraction of the diagonal from a sum, `q_sum_delta`.
[^7]: `no_finite_ccr` in `ProcessCanonicalCommutator.v` (0 axioms): from `trace_commutator_zero` ($\mathrm{tr}[A,B]=0$, relying on `trace_mul_comm`) and $\mathrm{tr}(c\mathbf{1})=cN$. A concrete witness: $[A,B]=\mathrm{diag}(1,-1)$, trace $0$, not a multiple of $\mathbf{1}$.
[^8]: A concrete commutator $[\hat q, \hat p]$ on the lattice $N=3$ with zero diagonal and trace $0$ is in `ProcessPositionMomentum.v` (0 axioms).
[^9]: `commutator_canonical` ($[a,a^\dagger]=1$), `cre_ann_eq_num` ($N=a^\dagger a$), `energy_spacing` (step $1$), `ground_energy` ($\tfrac12$), and `energy_unbounded` (the spectrum is unbounded) in `ProcessHarmonicLadder.v` (0 axioms).
[^10]: `evolution_conserves_norm` in `ProcessSchrodingerEvolution.v` (0 axioms). A concrete rational unitary is the $3\text{-}4\text{-}5$ rotation ($c=3/5,\ s=4/5,\ c^2+s^2=1$), `rotation_isometry`.
[^11]: `evolution_conserves_energy` in `ProcessEnergyConservation.v` (0 axioms); the witness is the sign flip $\mathrm{diag}(1,-1)$, which conserves the energy of any diagonal $\hat H$ and the norm. The link between both laws for one evolution is in `ProcessL2HilbertSynthesis.v`.

---

Part: [[06 Measure and Integration|Part VI. Measure and Integration]] · Volume: [[Mathematics|“Mathematics”]]

Navigation: ← [[05 L1 and L2 Spaces as Processes Completeness as Constructibility|Chapter 5. L¹ and L²: Spaces as Processes, Completeness as Constructibility]] · [[01 Orthonormal Systems and Fourier Coefficients|Chapter 1. Orthonormal Systems and Fourier Coefficients—Part VII]] →
