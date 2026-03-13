# Lattice Gauge Theory — Yang-Mills Mass Gap

**58 files | 633 Qed | 0 Admitted**

Process-based formalization of SU(2) Yang-Mills theory on a lattice,
targeting the Clay Millennium Prize Problem (mass gap existence).

## Summary

**Proved (conditional):**
- Mass gap exists at strong coupling (g >> 1)
- Mass gap persists under RG flow for bounded coupling range
- Confinement from gap decay rate analysis
- Strip geometry mass gap via transfer matrix spectrum

**The wall:**
- Continuum limit requires g -> 0 (weak coupling)
- Gap bounds degrade as g -> 0
- Same fundamental issue as Navier-Stokes: nonlinear vs linear

## File Organization

### Lattice Foundation (6 files, 100 Qed)
| File | Qed | Description |
|------|-----|-------------|
| LatticeStructure.v | 22 | Plaquettes, sites, links |
| GaugeField.v | 17 | Gauge field configurations |
| WilsonAction.v | 11 | Wilson plaquette action |
| TransferMatrix.v | 22 | Transfer matrix formalism |
| MassGapProcess.v | 11 | Mass gap as process |
| GaugeSynthesis.v | 10 | Phase synthesis |

### SU(2) Theory (6 files, 126 Qed)
| File | Qed | Description |
|------|-----|-------------|
| SU2Group.v | 28 | SU(2) group axioms |
| SU2Lattice.v | 16 | SU(2) on lattice |
| SU2TransferMatrix.v | 18 | SU(2) transfer matrix |
| StrongCoupling.v | 15 | Strong coupling expansion |
| RGFlow.v | 20 | Renormalization group flow |
| SU2Synthesis.v | 5 | SU(2) synthesis |

### Beyond Quadratic RG (5 files, 90 Qed)
| File | Qed | Description |
|------|-----|-------------|
| CosineAction.v | 14 | Cosine action formulation |
| HigherOrderRG.v | 21 | Higher-order RG terms |
| PerturbationRG.v | 17 | Perturbative RG analysis |
| RGConvergence.v | 12 | RG flow convergence |
| MassGapBound.v | 12 | Mass gap lower bound |

### Nonlinear RG + Extended Interval (3 files, 82 Qed)
| File | Qed | Description |
|------|-----|-------------|
| NonlinearRG.v | 23 | Full nonlinear RG |
| ExtendedInterval.v | 27 | Extended coupling interval |
| GlobalMassGap.v | 10 | Global mass gap |

### Exact Non-Perturbative (5 files, 93 Qed)
| File | Qed | Description |
|------|-----|-------------|
| LargerLattice.v | 18 | Larger lattice analysis |
| GapMatching.v | 17 | Gap matching across scales |
| ExactRGProcess.v | 17 | Exact RG as process |
| NonperturbativeGap.v | 11 | Non-perturbative gap |
| MillenniumSynthesis.v | 12 | Millennium synthesis |

### Confinement (5 files, 74 Qed)
| File | Qed | Description |
|------|-----|-------------|
| GapDecayRate.v | 21 | Gap decay rate analysis |
| ConfinementCorrection.v | 15 | Confinement corrections |
| TopologicalObstruction.v | 7 | Topological obstructions |
| WallTheorem.v | 8 | The wall theorem |
| YangMillsFinal.v | 5 | Yang-Mills final |

### Three Attacks (4 files, 84 Qed)
| File | Qed | Description |
|------|-----|-------------|
| SpectralBound.v | 20 | Spectral bound approach |
| KDependence.v | 13 | K-dependence analysis |
| InstantonEnhanced.v | 12 | Instanton-enhanced bounds |
| WallBreachSynthesis.v | 10 | Wall breach synthesis |

### Continuum Limit (4 files, 75 Qed)
| File | Qed | Description |
|------|-----|-------------|
| ContinuumOperator.v | 16 | Continuum operator |
| ExactEigenvalues.v | 5 | Exact eigenvalues |
| GapBound.v | 3 | Gap bound |
| ContinuumSynthesis.v | 6 | Continuum synthesis |

### 2+1D (8 files, 151 Qed)
Coupled2D, BlockDiagonal2D, Gap2D, Synthesis2D,
ExtendedAction, ContinuumMatrix2D, EigenAnalysis2D, ContinuumGap2D

### 3+1D (4 files, 35 Qed)
Coupled3D, Block3D, Gap3D, DimensionLadder, ExtendedAction7,
TensorGapBound, Continuum3DSynthesis

### Strip Geometry (5 files, 95 Qed)
DomainWalls, StripTransfer, StripSpectrum, ThermodynamicLimit, StripSynthesis

## Key Theorems

- `strong_coupling_gap` — mass gap > 0 at strong coupling
- `rg_gap_preserved` — gap persists under RG for bounded coupling
- `strip_gap_at_8` — strip geometry gap = 3/4
- `confinement_from_gap` — confinement follows from mass gap
