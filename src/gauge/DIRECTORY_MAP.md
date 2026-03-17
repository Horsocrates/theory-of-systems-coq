# gauge/ Directory Map

100 files, 2030 Qed. SU(2) lattice gauge theory and Yang-Mills mass gap.

---

## Core — Transfer Matrix + Characters (10 files, 234 Qed)

Computational foundation: transfer matrix, character expansion, Bessel partial sums.

| File | Qed | Key exports |
|------|-----|-------------|
| SU2Group.v | 30 | SU(2) group axioms |
| SU2Lattice.v | 20 | SU(2) lattice structure |
| SU2TransferMatrix.v | 19 | SU(2) transfer matrix |
| SU2Characters.v | 38 | Character expansion, Peter-Weyl |
| CharacterTransfer.v | 21 | Character-based transfer |
| TransferMatrix.v | 23 | General transfer matrix |
| TransferMatrixProof.v | 32 | Transfer matrix proofs |
| GaugeField.v | 18 | Gauge field definitions |
| WilsonAction.v | 13 | Wilson action S = beta*Sum(1-cos theta) |
| CosineAction.v | 22 | Cosine action variant |

## Mass Gap Proofs (15 files, 308 Qed)

Spectral gap = 289/384 at beta=1. Gap at beta=1,2,3,4. PMG criterion.

| File | Qed | Key exports |
|------|-----|-------------|
| SpectralGapCorrect.v | 28 | `spectral_gap_pos_all_rational` |
| ExactMassGap.v | 28 | Exact mass gap computation |
| ProcessMassGap.v | 44 | `su2_has_process_mass_gap` (PMG1+PMG2+PMG3) |
| GapBound.v | 17 | Gap lower bounds |
| GapDecayRate.v | 22 | Gap decay rate analysis |
| GapMatching.v | 21 | Gap matching across scales |
| GapRatio.v | 36 | Gap ratio computations |
| GlobalMassGap.v | 18 | Global mass gap |
| MassGapBound.v | 13 | Mass gap bound |
| MassGapProcess.v | 12 | Mass gap as process |
| NonperturbativeGap.v | 12 | Non-perturbative bounds |
| SpectralBound.v | 22 | Spectral bound analysis |
| TensorGapBound.v | 14 | Tensor product gap bound |
| TridiagonalGap.v | 18 | Tridiagonal matrix gap |
| ExactEigenvalues.v | 23 | Exact eigenvalue computation |

## Renormalization Group (10 files, 224 Qed)

RG flow for SU(2) lattice gauge. Contraction, convergence, universality.

| File | Qed | Key exports |
|------|-----|-------------|
| RGFlow.v | 23 | RG flow equations |
| RGContraction.v | 24 | RG contraction mapping |
| RGConvergence.v | 13 | RG convergence |
| ExactRGProcess.v | 18 | Exact RG as process |
| HigherOrderRG.v | 24 | Higher-order RG corrections |
| LatticeRG.v | 29 | Lattice RG implementation |
| NonlinearRG.v | 36 | Nonlinear RG analysis |
| PerturbationRG.v | 18 | Perturbative RG |
| UniversalityClass.v | 17 | Universality classes |
| IrrelevantOperators.v | 24 | Irrelevant operators |

## Dimensions — 2D and 3D (17 files, 312 Qed)

Extensions to 2+1D and 3+1D. Block-diagonal transfer matrices. Dimension ladder.

| File | Qed | Key exports |
|------|-----|-------------|
| Coupled2D.v | 20 | 2D coupled system |
| BlockDiagonal2D.v | 26 | 2D block-diagonal transfer |
| Gap2D.v | 18 | 2D mass gap |
| Synthesis2D.v | 10 | 2D synthesis |
| ContinuumGap2D.v | 13 | 2D continuum gap |
| ContinuumMatrix2D.v | 22 | 2D continuum transfer matrix |
| EigenAnalysis2D.v | 16 | 2D eigenvalue analysis |
| Coupled3D.v | 19 | 3D coupled system |
| Block3D.v | 15 | 3D block-diagonal transfer |
| Gap3D.v | 14 | 3D mass gap |
| CombinedTransfer3D.v | 24 | 3D combined transfer |
| KDependence.v | 32 | K-dependence analysis |
| DimensionLadder.v | 10 | 1D -> 2D -> 3D ladder |
| LargerLattice.v | 29 | Larger lattice analysis |
| StripTransfer.v | 33 | Strip geometry transfer |
| StripSpectrum.v | 25 | Strip spectrum |
| StripSynthesis.v | 21 | Strip synthesis |

## Continuum Limit (8 files, 158 Qed)

Continuum limit analysis. Thermodynamic limit. Spatial Hamiltonian.

| File | Qed | Key exports |
|------|-----|-------------|
| ContinuumCharacter.v | 24 | Continuum character expansion |
| ContinuumCovariance.v | 22 | Continuum covariance |
| ContinuumGap.v | 22 | Continuum gap |
| ContinuumOperator.v | 24 | Continuum operator |
| ContinuumSynthesis.v | 11 | Continuum synthesis |
| Continuum3DSynthesis.v | 9 | 3D continuum synthesis |
| ThermodynamicLimit.v | 20 | Thermodynamic limit |
| SpatialHamiltonian.v | 26 | Spatial Hamiltonian |

## Confinement + Correlations (10 files, 218 Qed)

Confinement proofs. Strong coupling expansion. Domain walls, instantons.

| File | Qed | Key exports |
|------|-----|-------------|
| ConfinementCorrection.v | 19 | Confinement corrections |
| StrongCoupling.v | 21 | Strong coupling expansion |
| CorrelationProof.v | 24 | Correlation function proofs |
| ClusterProof.v | 23 | Cluster expansion |
| CovarianceProof.v | 13 | Covariance proofs |
| LatticeCorrelations.v | 21 | Lattice correlation functions |
| LatticeStructure.v | 23 | Lattice structure definitions |
| DomainWalls.v | 37 | Domain wall analysis |
| InstantonEnhanced.v | 16 | Instanton-enhanced corrections |
| ExtendedInterval.v | 28 | Extended interval analysis |

## OS Axioms + Wightman (11 files, 204 Qed)

Osterwalder-Schrader axioms. Reflection positivity. Wightman reconstruction.

| File | Qed | Key exports |
|------|-----|-------------|
| ReflectionPositivity.v | 28 | Reflection positivity |
| ReflectionPositiveProof.v | 29 | RP detailed proof |
| LatticeOS1_Analyticity.v | 19 | OS1: analyticity |
| LatticeOS2_Regularity.v | 15 | OS2: regularity |
| LatticeOS3_Covariance.v | 16 | OS3: covariance |
| WightmanReconstruction.v | 23 | `yang_mills_mass_gap` (7-step chain) |
| TopologicalObstruction.v | 12 | Topological obstructions |
| HilbertConstruction.v | 18 | Hilbert space construction |
| FormalAnalytic.v | 15 | Formal analyticity |
| FormalTempered.v | 11 | Tempered distributions |
| FormalSO4.v | 9 | SO(4) rotation structure |

## Synthesis + Milestones (19 files, 296 Qed)

Synthesis and milestone files. Wall theorem. Complete Yang-Mills proof structure.

| File | Qed | Key exports |
|------|-----|-------------|
| GaugeSynthesis.v | 11 | Basic gauge synthesis |
| SU2Synthesis.v | 13 | SU(2) synthesis |
| PhaseB_Synthesis.v | 17 | Phase B synthesis |
| WallTheorem.v | 12 | Wall theorem (obstruction) |
| WallBreachSynthesis.v | 14 | Three attacks on the wall |
| YangMillsProcess.v | 12 | Yang-Mills as process |
| YangMillsCorrected.v | 23 | Corrected YM results |
| YangMillsComplete.v | 13 | Complete YM proof |
| YangMillsFinal.v | 8 | Final YM statement |
| YangMillsSealed.v | 11 | Sealed YM result |
| YMLevel4Complete.v | 25 | Level 4 complete |
| YMLevel5Complete.v | 15 | Level 5 complete |
| YM3DComplete.v | 16 | 3D complete |
| YMWallBreach.v | 19 | Wall breach |
| MillenniumSynthesis.v | 13 | Millennium Prize synthesis |
| ProofClosure.v | 18 | Proof closure |
| ExtendedAction.v | 26 | Extended action |
| ExtendedAction7.v | 12 | Extended action (7-link) |
| ClebschGordan.v | 37 | Clebsch-Gordan coefficients |
