# stdlib/qchem/ — Quantum Chemistry

**25 files, 281 Qed, 0 Admitted**

Quantum chemistry calculations over Q with Slater basis (Padé approximants).

## Atoms & Molecules
- **Hydrogen**: E = -1/2 Hartree (exact)
- **Helium**: E = -729/256 (Slater Q-basis, CI J=5α/8)
- **H₂**: R₀ = 7/5 Bohr (first verified molecule)
- **HF**: First heteronuclear molecule verified over Q

## Key Files
- **JIntegralExact.v** — J-integral for two-electron systems
- **HeMultiSlater.v** — Helium CI with multiple Slater determinants
- **HeEnergyLadder.v** — Helium energy level ladder
- **HFMolecule.v** — Hydrogen fluoride molecule
- **G2TestSet.v** — NIST G2 atomization energies

## Condensed Matter
- **CooperPair.v** — BCS superconductivity from transfer matrix
- **BCSGap.v** — BCS gap equation
- **HoneycombLattice.v** — Graphene hexagonal lattice
- **GrapheneTransfer.v** — Graphene Dirac cone from transfer matrix
