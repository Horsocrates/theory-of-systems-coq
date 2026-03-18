# process/ Directory Map

221 files, 3524 Qed. All of P4 process mathematics + physics derivation + gauge connections.

---

## Core — Foundation (12 files, 222 Qed)

Core definitions, arithmetic, basic process infrastructure. All other modules depend on this.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessCore.v | 19 | `RealProcess`, `is_Cauchy`, `const_process` |
| ProcessArithmetic.v | 17 | `monotone_bounded_Cauchy`, `process_scale` |
| ProcessBounds.v | 11 | `has_process_mass_gap`, `pmg_implies_cauchy` |
| ProcessSimple.v | 19 | Simple functions for measure theory |
| ProcessDerivative.v | 17 | Process derivative, differentiable |
| ProcessSeries.v | 13 | Series, partial sums |
| ProcessTaylor.v | 13 | Taylor expansion as process |
| ProcessGroup.v | 26 | Process group, subgroup |
| ProcessRing.v | 24 | Process ring, ideal |
| ProcessHomomorphism.v | 16 | Morphisms between process algebras |
| ProcessL2.v | 21 | L2 space, bounded_above |
| ProcessFourPrinciples.v | 25 | `four_principles_complete` (P1 /\ P2 /\ P3 /\ P4) |

## Analysis — Classical Theorems (15 files, 215 Qed)

Process versions of classical analysis theorems. Every theorem proved over Q as a process.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessIVT.v | 13 | `process_ivt` |
| ProcessEVT.v | 9 | `process_evt` |
| ProcessBW.v | 9 | Process Bolzano-Weierstrass |
| ProcessHB.v | 7 | Process Heine-Borel |
| ProcessUncountable.v | 7 | Process uncountability |
| ProcessFTC.v | 9 | `process_ftc` — fundamental theorem of calculus |
| ProcessIntegral.v | 12 | Process Riemann integral |
| ProcessLebesgue.v | 17 | Process Lebesgue integration |
| ProcessFatou.v | 16 | Process Fatou's lemma |
| ProcessMeasureTheory.v | 22 | Measure theory over processes |
| ProcessMeasureUnified.v | 9 | Unified measure results |
| ProcessGronwall.v | 18 | Gronwall inequality |
| ProcessPicard.v | 32 | `picard_iteration_cauchy` |
| ProcessODE.v | 20 | ODE existence via process |
| ProcessODEExamples.v | 20 | Concrete ODE examples |

## Topology (6 files, 103 Qed)

Process topology: open sets, metric spaces, compactness, connectedness over Q.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessTopOpen.v | 14 | Open sets as processes |
| ProcessTopMetric.v | 17 | Metric spaces |
| ProcessTopCompact.v | 16 | Compactness |
| ProcessTopConnected.v | 16 | Connectedness |
| ProcessTopUnified.v | 10 | Unified topology |
| ProcessFiniteDim.v | 30 | Q^n finite-dimensional spaces |

## Functional Analysis + PMG (10 files, 167 Qed)

Operators, spectral theory, Process Mass Gap criterion, category theory processes.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessOperatorFA.v | 18 | Bounded operators |
| ProcessSpectral.v | 19 | Spectral theory |
| ProcessNoetherian.v | 17 | Noetherian processes |
| ProcessPMGMarkov.v | 15 | PMG for Markov chains |
| ProcessPMGQuantum.v | 15 | PMG for quantum systems |
| ProcessPMGSchrodinger.v | 18 | PMG for Schrodinger |
| ProcessPMGEssential.v | 8 | Essential PMG |
| ProcessPMGUnified.v | 12 | 12 instances of PMG |
| ProcessCategory.v | 20 | Process categories |
| ProcessLimitColimit.v | 20 | Limits, colimits |

## Algebra — Unified Structures (4 files, 46 Qed)

Unified algebraic structures and bridges.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessAlgebraUnified.v | 12 | Unified algebra |
| ProcessFuncUnified.v | 12 | Unified functional analysis |
| ProcessUnified.v | 12 | General unified results |
| ProcessBridge.v | 10 | Bridge core <-> applications |

## E/R/R Framework (10 files, 134 Qed)

Elements/Roles/Rules derived from P1+P2+P3. Gauge invariance, fermions, non-abelian extension.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessERRDerived.v | 16 | `err_from_principles` — E/R/R from P1+P2+P3 |
| ProcessERRSymmetry.v | 15 | Symmetry of Rules |
| ProcessERRGauge.v | 12 | Gauge invariance from symmetric Rules |
| ProcessERRGaugeGroup.v | 12 | Gauge group structure |
| ProcessERRGaugeSynthesis.v | 12 | Phase 18 synthesis |
| ProcessERRWilson.v | 12 | Wilson loops from E/R/R |
| ProcessERRFermion.v | 18 | Fermions from antisymmetric Rules |
| ProcessNonAbelianERR.v | 13 | Non-abelian Rules (matrix-valued) |
| ProcessNonAbelianSU2.v | 13 | SU(2) from non-abelian E/R/R |
| ProcessPathOrdering.v | 11 | Path ordering for non-abelian |

## Gravity + Regge (20 files, 290 Qed)

Gravity from P3+P1+L4. Categories Geom and Gauge. Regge calculus. Einstein equations.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessGeomCategory.v | 24 | `QGeometry`, `QEdge`, `geom_nvertices` |
| ProcessGaugeCategory.v | 20 | `GaugeConfig`, `gc_links`, `gc_edges` |
| ProcessGeomGaugeBasic.v | 10 | Basic Geom-Gauge properties |
| ProcessGeomGaugeFunctor.v | 23 | `F_obj`, `G_obj`, `effective_length` |
| ProcessRegge.v | 18 | Regge calculus 1+1D |
| ProcessRegge4D.v | 13 | Regge calculus 3+1D |
| ProcessReggeTransfer.v | 18 | Regge transfer matrix |
| ProcessReggeVariation.v | 19 | Regge variation principle |
| ProcessSimplex4D.v | 19 | 4D simplex geometry |
| ProcessP3Metric.v | 13 | P3 -> metric |
| ProcessP3Dynamics.v | 9 | P3 -> dynamics |
| ProcessP3Gravity.v | 11 | P3 -> gravity |
| ProcessP3Einstein.v | 10 | P3 -> Einstein equations |
| ProcessP3GravitySynthesis.v | 10 | Phase 19 synthesis |
| ProcessL4Variational.v | 12 | L4 -> variational principle |
| ProcessDiscreteEinstein.v | 15 | Discrete Einstein equations |
| ProcessSchwarzschildRegge.v | 17 | Schwarzschild on Regge lattice |
| ProcessBlackHole.v | 17 | Black holes, Hawking temperature |
| ProcessGravWave.v | 14 | Gravitational waves |
| ProcessGravWavePMG.v | 13 | Gravitational wave PMG |

## Adjunction — GR-QFT + Quantum Gravity (14 files, 253 Qed)

Process adjunction from P2. Strict fails, Galois connection, emergence = QG.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessAdjunction.v | 28 | `level_adjunction`, Embed |- Forget |
| ProcessWholeness.v | 24 | P1 wholeness categorical |
| ProcessGGAdjStrict.v | 15 | Strict adjunction fails |
| ProcessGGAdjWeak.v | 15 | Weak adjunction holds |
| ProcessGGAdjProcess.v | 17 | `ProcessAdjunction`, defect process |
| ProcessGGAdjSynthesis.v | 15 | Phase 14A synthesis |
| ProcessGGGalois.v | 15 | `geom_gauge_galois` |
| ProcessBackReaction.v | 15 | Back-reaction (counit epsilon) |
| ProcessCoupling.v | 14 | Coupling strength from defect |
| ProcessQuantization.v | 16 | Quantization (unit eta) |
| ProcessEmergencePhysics.v | 17 | Emergence = QG |
| ProcessQuantumGravity.v | 20 | Quantum gravity from adjunction |
| ProcessUniversalAdjunction.v | 24 | `EffLengthFn` typeclass |
| ProcessIntrinsicDefect.v | 23 | Intrinsic defect pseudometric |

## Spacetime + Dimension (13 files, 167 Qed)

Spacetime from P4, Lorentzian signature, dimension selection, crossing.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessTime.v | 14 | Time as nat (P4) |
| ProcessSpacetime.v | 12 | Spacetime structure |
| ProcessLorentzian.v | 15 | Lorentzian signature from P4 |
| ProcessLightCone.v | 12 | Light cone structure |
| ProcessLorentzianRegge.v | 9 | Lorentzian Regge calculus |
| ProcessLorentzianSynthesis.v | 10 | Phase 22 synthesis |
| ProcessDimension.v | 13 | Dimension from stability |
| ProcessDimensionSelect.v | 12 | D=3+1 preferred |
| ProcessStability.v | 14 | Stability analysis |
| ProcessCrossing.v | 17 | Gauge-gravity crossing |
| ProcessCrossingD.v | 13 | Crossing in D dimensions |
| ProcessCombinedTransfer.v | 14 | Combined transfer matrix |
| ProcessPathBSynthesis.v | 14 | Path B synthesis |

## Electroweak + Higgs (12 files, 194 Qed)

Higgs mechanism, Weinberg angle, W/Z masses, GUT running.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessSymBreaking.v | 16 | Symmetry breaking |
| ProcessGoldstone.v | 12 | Goldstone bosons |
| ProcessHiggsMechanism.v | 13 | Higgs mechanism |
| ProcessHiggsPotentialERR.v | 18 | Higgs potential from E/R/R |
| ProcessHiggsVEV.v | 15 | Higgs VEV |
| ProcessHiggsMassCorrected.v | 14 | Higgs mass with corrections |
| ProcessFermionLoop.v | 18 | Fermion loop corrections |
| ProcessElectroweak.v | 17 | Electroweak unification |
| ProcessElectroweakMasses.v | 20 | W/Z mass predictions |
| ProcessWeinbergAngle.v | 14 | sin^2(theta_W) = 3/13 |
| ProcessRGWeinberg.v | 23 | RG running of Weinberg angle |
| ProcessGUTScale.v | 15 | GUT scale unification |

## Fermions + Mass (13 files, 188 Qed)

Fermions from antisymmetric E/R/R Rules. Mass hierarchy, proton structure.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessPauliExclusion.v | 16 | Pauli exclusion from R(e,e)=0 |
| ProcessGrassmann.v | 15 | Grassmann algebra |
| ProcessLatticeFermion.v | 11 | Wilson fermions on lattice |
| ProcessFermionSynthesis.v | 12 | Phase 21 synthesis |
| ProcessFermionSpectrum.v | 20 | Fermion mass spectrum |
| ProcessFermionDoubling.v | 12 | Fermion doubling problem |
| ProcessFermion3D.v | 16 | 3D fermions |
| ProcessNielsenNinomiya.v | 12 | Nielsen-Ninomiya no-go |
| ProcessStaggered.v | 11 | Staggered fermions |
| ProcessYukawa.v | 14 | Yukawa couplings |
| ProcessMassHierarchy.v | 13 | Mass hierarchy from P3 |
| ProcessDimTransmutation.v | 20 | Dimensional transmutation |
| ProcessProtonStructure.v | 14 | Proton mass structure |

## Standard Model + CP (7 files, 103 Qed)

Standard Model from anomaly cancellation. Q[i] (Gaussian rationals). CP violation.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessAnomaly.v | 17 | Anomaly analysis |
| ProcessAnomalyCancel.v | 12 | Anomaly cancellation |
| ProcessRoleConstraints.v | 9 | Role constraints -> SM |
| ProcessStandardModel.v | 12 | SM group structure |
| ProcessGaussianQ.v | 18 | `Qi`, `qi_mul`, `qi_norm2`, `qi_eq` |
| ProcessComplexRules.v | 12 | Complex-valued Rules |
| ProcessCPViolation.v | 15 | CP violation from chirality |

## RG Flow + Confinement (9 files, 163 Qed)

Renormalization group, asymptotic freedom, string tension, vacuum energy.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessBlocking.v | 15 | Lattice blocking |
| ProcessRGFlow.v | 16 | RG flow u'=2u-u^2/4 |
| ProcessAsymptoticFreedom.v | 18 | Asymptotic freedom |
| ProcessRGHigherOrder.v | 17 | Higher-order RG corrections |
| ProcessRGPrecision.v | 16 | RG precision bounds |
| ProcessStringTension.v | 43 | String tension from defect |
| ProcessLatticeObservable.v | 16 | Lattice observables |
| ProcessVacuumEnergy.v | 18 | Process vacuum energy |
| ProcessCosmologicalConst.v | 14 | Cosmological constant |

## Quantum Foundations — Step 10 (8 files, 135 Qed)

Quantum mechanics derived from L1-L5 and P1-P4. No quantum postulates assumed.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessGaussianQ.v | — | (shared with SM: `Qi`, `qi_mul`, `qi_norm2`) |
| ProcessHeisenberg.v | 22 | `heisenberg_bound` — uncertainty from P2 defect |
| ProcessUncertaintyBound.v | 22 | `heisenberg_at_every_scale` |
| ProcessBornRule.v | 20 | `born_rule`, `norm2_additive_orthogonal` |
| ProcessProbability.v | 16 | Born rule examples, `phase_45_complete` |
| ProcessEntanglement.v | 19 | `bell_state_entangled`, `is_entangled` |
| ProcessBellInequality.v | 15 | `chsh_deterministic_bound`, CHSH |
| ProcessNoCloning.v | 12 | `no_cloning` — linear != clone |
| ProcessMeasurement.v | 13 | `no_measurement_problem`, `quantum_from_logic` |

## Synthesis + Meta (12 files, 282 Qed)

Synthesis files connecting all results. Axiom audit. Final assessment.

| File | Qed | Key exports |
|------|-----|-------------|
| ProcessGrandUnification.v | 23 | Grand unification |
| ProcessPhysicsSynthesis.v | 21 | Physics synthesis |
| ProcessStep3Synthesis.v | 16 | Step 3 synthesis |
| ProcessStep4Synthesis.v | 12 | Step 4 synthesis |
| ProcessStep5Synthesis.v | 11 | Step 5 synthesis |
| ProcessStep8Synthesis.v | 12 | Step 8 synthesis |
| ProcessFinalAssessment.v | 44 | `theory_of_systems_status`, 15 numbers |
| ProcessOpenQuestions.v | 48 | Open questions, honest score |
| ProcessSynthesisStrengthened.v | 18 | Strengthened synthesis |
| ProcessChainVerified.v | 14 | Verified derivation chain |
| ProcessAxiomAudit.v | 13 | Axiom audit |
| ProcessDerivedVsConsistent.v | 20 | Derived vs consistent classification |
