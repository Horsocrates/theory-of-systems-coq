# src/physics/ — Quantum Physics (356 Qed)

Quantum mechanics derived from process theory: inner products, Born rule,
spectral dichotomy, measurement, entanglement, decoherence, and concrete
quantum systems (qubit, harmonic oscillator, spin chains).

## Files (14 files, 356 Qed, 0 Admitted)

### Phase 3A — Abstract Framework (160 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `InnerProduct.v` | 36 | Cauchy-Schwarz inequality, process inner products |
| `Orthogonality.v` | 27 | Pythagorean theorem, Bessel inequality, Gram-Schmidt |
| `QuantumState.v` | 19 | Process-valued state vectors, basis states |
| `Observable.v` | 16 | Symmetric matrix processes, eigenstate theory |
| `BornRule.v` | 13 | Transition probabilities, expectation values |
| `SpectralDichotomy.v` | 30 | PCH → discrete/continuous spectrum classification |
| `Measurement.v` | 19 | Post-measurement projection, repeatability |

### Phase 3B-3D — Entanglement & Thermodynamics (63 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `Entanglement.v` | 25 | Tensor products, Bell state, `bell_entangled` |
| `Decoherence.v` | 21 | Environment-induced decoherence, pointer states |
| `ThermodynamicArrow.v` | 17 | Entropy increase from decoherence |

### Phase 3E — Concrete Quantum Systems (133 Qed)

| File | Qed | Description |
|------|-----|-------------|
| `Qubit.v` | 42 | Pauli-X/Z, superposition probability = 1/2 |
| `HarmonicOscillator.v` | 35 | Equispaced levels, non-degeneracy |
| `SpinChain.v` | 32 | Bell state, Ising ⟨Φ+|H|Φ+⟩ = 2J |
| `QuantumDynamics.v` | 24 | Time evolution, norm preservation |

## Crown Jewel

**Spectral Dichotomy**: Every observable's eigenspace is either discrete or
continuous — proven from the Process Continuum Hypothesis (PCH).
