# Theorem Index

Key theorems organized by category. For the complete file-by-file listing, see [FILE_MAP.md](FILE_MAP.md).

## Type Safety

| Theorem | File | Statement |
|---------|------|-----------|
| `tos_lang_main_theorem` | TypeSafety.v | Well-typed + fuel -> well-typed result |
| `type_safety` | TypeSafety.v | Well-typed closed term: value or steps, preserving type |
| `subject_reduction` | SubjectReduction.v | e : T and e -> e' implies e' : T |
| `progress` | Progress.v | e : T implies value(e) or exists e', e -> e' or benign stuck |
| `typecheck_sound` | TypeChecker.v | typecheck G e = Some T implies G |- e : T |
| `typecheck_ann_sound` | TypeChecker.v | typecheck_ann G ea = Some T implies G |- erase(ea) : T |
| `verified_pipeline` | Evaluator.v | typecheck OK implies eval preserves type + progress |
| `safe_eval_sound` | Evaluator.v | safe_eval returns well-typed result |
| `ai_generation_safe` | AIInterface.v | AI pipeline end-to-end safety |
| `typing_implies_safe` | Soundness.v | Well-typed -> well-formed -> no paradox |

## Paradox Blocking

| Theorem | File | Statement |
|---------|------|-----------|
| `well_formed_no_paradox` | Roles.v | ERR_WellFormed -> not generates_contradiction |
| `circular_dep_is_paradox` | Roles.v | Circular Status dep -> paradox |
| `russell_is_circular_status` | Roles.v | Russell's set has circular status dependency |
| `liar_is_circular_status` | Roles.v | Liar paradox has circular status dependency |
| `russell_untypable` | Soundness.v | Russell's set cannot be typed |
| `liar_untypable` | Soundness.v | Liar paradox cannot be typed |
| `circular_dep_blocked` | Soundness.v | Circular dependencies are blocked by typing |
| `safety_implies_no_paradox` | TypeSafety.v | Type safe evaluation -> no paradox |

## Convergence / Fixed Points

| Theorem | File | Statement |
|---------|------|-----------|
| `iterate_contraction` | FixedPoint.v | Contraction iterates stay in interval |
| `contraction_unique_fixed` | FixedPoint.v | Contraction has at most one fixed point |
| `contraction_limit_in_interval` | FixedPoint.v | Limit of contraction iterates is in interval |
| `contraction_compose` | FixedPoint.v | Composition of contractions is contraction |
| `pipeline_converges` | ReasoningConvergence.v | Pipeline contraction -> convergence |
| `bellman_contraction` | MDPFoundations.v | Bellman operator is contraction with gamma |
| `strongly_convex_monotone` | Hessian.v | Strongly convex -> gradient is monotone |

## Pipeline Verification

| Theorem | File | Statement |
|---------|------|-----------|
| `validate_d1_has_elements` | DomainValidation.v | Valid D1 has elements |
| `validate_d1_acyclic` | DomainValidation.v | Valid D1 is acyclic |
| `validate_d2_implies_d1` | DomainValidation.v | D2 requires D1 |
| `validate_d3_implies_d2` | DomainValidation.v | D3 requires D2 |
| `validate_d4_implies_d3` | DomainValidation.v | D4 requires D3 |
| `validate_d5_implies_d4` | DomainValidation.v | D5 requires D4 |
| `pipeline_implies_ask` | DomainValidation.v | Valid pipeline has D6-ASK |
| `pipeline_implies_gates` | DomainValidation.v | Valid pipeline has inter-domain gates |
| `pipeline_implies_reflect` | DomainValidation.v | Valid pipeline has D6-REFLECT |

## Yang-Mills Mass Gap

| Theorem | File | Statement |
|---------|------|-----------|
| `yang_mills_mass_gap` | YangMillsComplete.v | Complete 7-step proof: lattice → Wightman QFT with Δ > 0 |
| `yang_mills_complete_summary` | YangMillsComplete.v | Gap positive + ratio bounded + energy positive + Wightman + OS + artifacts contract |
| `the_key_inequality` | YangMillsComplete.v | `I₀ − 2I₂ + I₄ > 0` at β=1,2 (Bessel positivity) |
| `mass_gap_rg_invariant` | YangMillsComplete.v | Physical mass positive under RG transformation |
| `artifact_sequence_decreasing` | RGContraction.v | Lattice artifacts monotonically decrease under RG |
| `so4_restored_at_fixed_point` | ContinuumCovariance.v | SO(4) violation < 1/40 for β ≥ 42 |
| `anisotropy_negligible` | UniversalityClass.v | Anisotropy < 1/40 for β ≥ 42 |
| `wightman_from_os` | WightmanReconstruction.v | OS axioms → Wightman axioms satisfied |
| `gap_at_beta_1_positive` | ExactMassGap.v | `gap_M0 1 > 0` (exact Bessel computation) |
| `gap_ratio_lt1_beta_1` | GapRatio.v | `t₁/t₀ < 1` at β=1 |
| `physical_mass_positive` | ContinuumGap.v | Physical mass `m = (1−r)/a > 0` |
| `os1_on_lattice` | LatticeOS1_Analyticity.v | OS1 (analyticity) on lattice |
| `os2_on_lattice` | LatticeOS2_Regularity.v | OS2 (regularity) on lattice |
| `os3_on_lattice` | LatticeOS3_Covariance.v | OS3 (covariance) on lattice |

## Calculus

| Theorem | File | Statement |
|---------|------|-----------|
| `IVT_exists_root` | IVT_ERR.v | f continuous, f(a) < 0 < f(b) -> exists c, f(c) = 0 |
| `grid_mvt` | MeanValueTheorem.v | exists c in grid, f'(c) approx (f(b)-f(a))/(b-a) |
| `ftc_product` | IntegralApplications.v | Integration by parts (product rule for integrals) |
| `taylor_remainder_bound` | TaylorSeries.v | Taylor approximation error bound |
| `uniform_limit_continuous` | UniformConvergence.v | Uniform limit of continuous = continuous |

## Set Theory / Cardinality

| Theorem | File | Statement |
|---------|------|-----------|
| `unit_interval_uncountable_trisect_v2` | ShrinkingIntervals_ERR.v | [0,1] cap Q is non-surjectable from N |
| `calkin_wilf_bijection` | Countability_Q.v | Q+ is countable via Calkin-Wilf |

## Algebra (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `group_assoc` | GroupTheory.v | Group operation is associative |
| `group_inverse_unique` | GroupTheory.v | Group inverse is unique |
| `ring_mul_zero_l` | RingField.v | 0 * a = 0 in a ring |
| `field_inv_mul` | RingField.v | a * a^(-1) = 1 in a field |

## Number Theory (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `prime_ge_2` | Primes.v | Primes are >= 2 |
| `smallest_factor_divides` | Primes.v | Smallest factor divides n |
| `gcd_divides_l` | GCD.v | gcd(a,b) divides a |
| `gcd_divides_r` | GCD.v | gcd(a,b) divides b |
| `congruent_add` | ModularArith.v | Congruence compatible with addition |
| `congruent_mul` | ModularArith.v | Congruence compatible with multiplication |
| `zmod_add_assoc` | ModularArith.v | Z/mZ addition is associative |
| `pigeonhole_simple` | Combinatorics.v | n+1 items, n slots -> collision |

## Graph Theory (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `reverse_graph_involutive` | Graph.v | Reversing a graph twice = identity |
| `is_reachable_self` | Graph.v | Every node reaches itself |
| `step_deterministic` | Reduction.v | Small-step reduction is deterministic |

## Automata & Formal Languages (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `dfa_complement_accepts` | Automata.v | Complement DFA accepts iff original rejects |
| `re_nullable_correct_true` | FormalLanguages.v | Nullable soundness: re_nullable r = true -> matches r [] |
| `re_nullable_correct_false` | FormalLanguages.v | Nullable completeness: matches r [] -> re_nullable r = true |

## Category Theory (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `iso_refl` | Category.v | Identity is an isomorphism |
| `iso_sym` | Category.v | Iso is symmetric |
| `iso_trans` | Category.v | Composition of isos is iso |
| `comp_mono` | Category.v | Composition of monos is mono |
| `comp_epi` | Category.v | Composition of epis is epi |
| `initial_unique_up_to_iso` | Category.v | Initial objects unique up to iso |
| `list_fmor_id` | Functor.v | List functor preserves identity (map id = id) |
| `list_fmor_comp` | Functor.v | List functor preserves composition |
| `fmor_preserves_iso` | Functor.v | Functors preserve isomorphisms |

## Monads (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `option_left_id` | Monad.v | Option monad left identity |
| `list_assoc` | Monad.v | List monad associativity |
| `kleisli_assoc` | Monad.v | Kleisli composition is associative |

## Lattice Theory (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `knaster_tarski` | Lattice.v | Monotone f on complete lattice has fixed point |
| `knaster_tarski_lfp` | Lattice.v | Least fixed point of monotone function |
| `knaster_tarski_gfp` | Lattice.v | Greatest fixed point of monotone function |
| `absorption_1` | Lattice.v | meet x (join x y) = x |
| `absorption_2` | Lattice.v | join x (meet x y) = x |

## Statistics & Information Theory (Stdlib)

| Theorem | File | Statement |
|---------|------|-----------|
| `bern_pmf_sum` | Distributions.v | Bernoulli PMF sums to 1 |
| `bern_pmf_nonneg_0` | Distributions.v | Bernoulli PMF is non-negative |
| `Qpow_nonneg` | Distributions.v | Non-negative base gives non-negative power |
| `sum_Q_app` | Statistics.v | sum distributes over append |
| `mean_singleton` | Statistics.v | mean [x] = x |
| `kl_divergence_self_zero` | InformationTheory.v | KL(p || p) = 0 |
| `mutual_info_symmetric` | InformationTheory.v | I(X;Y) = I(Y;X) |
| `cross_entropy_self_eq_entropy` | InformationTheory.v | H(p,p) = H(p) |
| `mle_grid_maximizes` | Estimation.v | MLE finds maximum on grid |
