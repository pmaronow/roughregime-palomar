# Mathematical coverage

The authoritative paper is `paper/main.tex` with mathematical body
`paper/body.tex`. Its authors are P. M. Aronow, Nathan Kallus, and Patrick
Lopatto. Numbers below follow this paper's chapter-local counter; stable TeX
labels are included because numbers can change with typesetting.
`coverage.json` contains the source body's SHA-256 hash, line spans, fuller
endpoint lists, the twenty application rows, and the selected submission
interface.

The submission interface selects **Theorem 2.3(a) and (b)**. In Challenge,
`RoughRegimeSubmission.mainUpper` and `mainLower` state the respective targets;
Solution supplies the proofs from `RoughRegime.Model.uniformUpperClaim` and
`mainLowerClaim`. The broader source inventory below is statement-inspected.
Compilation, exact target comparison, transitive axiom checks and independent
kernel checks are separate evidence recorded by the verification tools and
report. This inventory does not turn a checked name, a proposition-valued
definition, or a proof-bearing input structure into a proof of its contents.

## Explicit typed-check scope

`NumberedClaims.lean` expands the selected Theorem 2.3(a,b) targets and supplies
existing proofs at the explicit types. It also states explicit targets for
Lemma 4.1 (full generating identity and its `z=1` specialization), Lemma 4.6,
Lemma 5.1, Lemma 6.1, both Proposition 7.1 risk conclusions, and the exact
logarithmic scale identity. Two separate definitional equalities check `rho`
and the subcritical scale normalization. These typed checks preserve the
conditional hypotheses and quantifier order. Their current compilation and
kernel status belongs in the verification report. Other entries below remain
semantic correspondence and declaration-existence inventory unless the
verification report expressly records an additional exact type check.

## Selected headline theorem

For positive dimension and smoothness indices, the generic observed-law model
has a bounded measurable nonnegative response function `D`, bounded `U,V,W`,
positive conditional `D` mean, Holder bounds on the conditional ratios, and a
positive bounded design weight `g=wp`. Its target is
`E[W]+lambda*integral(a*b*g)`, with nonzero `lambda`. All observations are iid.
The minimax infimum includes measurable randomized real-output estimators.

The parameters are
`theta=(alpha+beta)/d`,
`nu=binomial(d+ceil(alpha)-1,d)+binomial(d+ceil(beta)-1,d)`,
`rho=(sqrt(gplus)-sqrt(gminus))/(sqrt(gplus)+sqrt(gminus))`, and `tau=-log(rho)`.
For `theta<1/2`, the scale is
`a_n=n^(-theta)*(log n)^(theta/2)*exp(-2*sqrt(theta*(1-2*theta)*tau)*sqrt(log n))`.

- **Upper bound:** one positive constant and sample cutoff precede the response
  space, its measurable structure, all observables at the fixed numerical
  bounds, and all laws. The RMSE is bounded by `C*n^(-1/2)` for
  `theta>=1/2`, including equality, and by
  `C*a_n*(log n)^(nu/2+1/4)` for `0<theta<1/2`.
- **Lower bound:** a finite-support baseline law must satisfy the strict
  interior conditions and either positive definite residual covariance or the
  diagonal alternative `U=V`, `alpha=beta`, and positive residual variance.
  For every positive localization radius, constants precede every intermediate
  class containing the local class and contained in the full model. The RMSE
  lower scales are `c*n^(-1/2)` and `c*a_n*log n`. In the rough regime, the
  minimax probability of error at least `2*c*a_n*log n` is at least `1/4`.

The Holder norm uses order `ceil(t)-1`, Euclidean distance, and the sum of the
maximum derivative supremum and maximum highest-order seminorm. Integer
smoothness therefore means Lipschitz derivatives of order `t-1`.
`holderNorm_eq_classicalHolderNorm` proves the ordered-coordinate/multi-index
bridge. `KernelSeedBridge` proves equivalence between real-output Markov
randomization and the independent uniform seed used in the development.
`RiskBridge` identifies the encoded `eLpNorm` RMSE with squared-integral RMSE.
These are proved bridges, not extra model hypotheses.

## Numbered source results

Declaration names below omit the common `RoughRegime.` prefix.

| Paper result | Stable label | Proved endpoint or definition | Scope |
| --- | --- | --- | --- |
| Theorem 2.3 | `thm:generic` | `Model.uniformUpperClaim`, `Model.mainLowerClaim`, `Model.model_bracket` | Selected headline upper and lower bounds described above. |
| Definition 3.1 | `def:bracket` | `Model.BracketParameters`, `LowerBracket`, `UpperBracket`, `Bracket` | Definitions of rate predicates; definitions alone establish no risk bound. |
| Corollary 3.2 | `cor:applications` | MAR, treatment, separated-design, products, trial, Wald, conditional-Wald and overlap endpoints listed in JSON | Twenty literal observed-law targets/classes; see application qualifications below. |
| Lemma 4.1 | `lem:reciprocal` | `Upper.reciprocal_expansion`, `reciprocal_expansion_at_one`, `interval_reciprocal_angular` | Positive nondegenerate interval, complex disk `abs(z)<rho^-1`, correct constant term. |
| Lemma 4.2 | `lem:matrix-approximation` | `CombinedAnalytic.matrix_determinant_truncation_error`, `CombinedPolynomial.truncationEntryPolynomial_degree`, `KernelExpressions.real_affine_expression_truncations`, `Cauchy.polynomial_derivative_bound` | Symmetric matrices with spectra in the fixed interval; bounded affine families; polynomial derivative estimates. |
| Lemma 4.3 | `lem:projection-polynomials` | `Model.uniform_source_projection_lemma_full_gradient`, `ModelWitness.levelProjectionIncrement_eq`, `uniform_projection_telescope_resolution_bias` | Actual dyadic cells and known polynomials; uncapped gradient exponent `min(alpha,beta)`, including the base term. |
| Lemma 4.4 | `lem:lift` | `LiftTranslation.polynomialLift_eq_paperLift`, `polynomialLift_covariance`; `Upper.polynomialLift_unbiased` | Bounded measurable iid vectors, degrees at most `n`; denominator `r!*(n)_r`; terms vanish above the smaller degree. |
| Lemma 4.5 | `lem:variance` | `LiftVariance.variance_polynomial_cell_lift_paper` | Original cell support/probability, complex bound, gradient and `2R<=n` hypotheses; exact `Cv=2*e^2*C0^7`. |
| Lemma 4.6 | `lem:window-sum` | `Window.window_sum`, `window_sum_finite_set` | Finite set in `(0,X]`, separation at least `log 2`; exact stated constant. |
| Lemma 5.1 | `lem:parametric-path` | `LowerMeasure.parametric_path_minimax_bound` | Positive affine probability-density path, bounded slope, nonzero target derivative at an interior point. |
| Lemma 5.2 | `lem:poisson-comparison` | `PoissonMeasure.AdmissiblePhasePair.original_lemma11` | Admissible independent paired priors and original pointwise response smallness; physical two-block normalization retained. |
| Proposition 5.3 | `prop:reduction` | `PoissonMeasure.AdmissibleReduction.Parameters.paper_reduction_to_two_estimates` | Conditional reduction from the two prior estimates at every sufficiently large sample size and every eligible grid. |
| Lemma 6.1 | `lat:gate` | `LatticeFourier.gated_lattice_laws` | Actual sinc density/lattice law, `Q>=2`, `M>=2`, positive scale and original Fourier bandwidth condition. |
| Lemma 6.2 | `lem:lattice-priors` | `LatticePriors.construct_source_lattice_priors`, `source_lattice_priors` | Genuine smooth density/profile priors, Holder budgets, coefficients and separation with constants before scale choices. |
| Proposition 7.1 | `prop:local-lower` | `LocalLower.StandingData.proposition15_rough`, `proposition15_parametric` | Supplied scores; actual rough hard families and local affine parametric path; target matching only on the constructed laws. |
| Lemma 7.2 | `lem:local` | `LocalLower.StandingData.proposition15_lemma16_hard_family`, `lemma16_constant_path`; `LatticePriors.SourceModelFamily.selected_germ_holder_budget`, `selected_germ_sup_littleO` | Axis-sensitive smooth-germ Holder control, density-margin localization, finite H/I/W restrictions and constant-path membership. |
| Definition A.1 | `def:hard` | `Model.HardAtScale` | Testing property defined as a proposition; definition does not prove hardness. |
| Lemma A.2 | `lem:hard-risk` | `Applications.hardness_to_risk`; `Model.HardAtScale.eventually_risk`, `lowerBracket` | Risk and quarter-tail consequences conditional on the stated hardness premise. |
| Lemma A.3 | `lem:reductions` | `Applications.lipschitz_combination_minimax`, `lipschitz_reverse_minimax`, `lipschitz_iid_minimax_rmse`, `hardness_reverse_transfer_iid`; `Model.kernel_reduction`, `kernel_hardness` | Conditional Lipschitz/reverse/kernel transports, instantiated in applications. |
| Lemma B.1 | `lem:smooth-propensity-pilot` | `Applications.fixed_accuracy_smooth_pilot` | Fixed-accuracy measurable pilot under the stated smoothness, binary-response and design bounds; exponentially small failure probability. |

Section 4 assumes `alpha<=beta` after an explicit symmetry reduction.
`ModelSwap` provides that reduction for the headline theorem. The standalone
Lemma 4.3 endpoint retains the section's ordered hypothesis rather than
silently asserting an unordered package.

In Lemma 4.5, the separately declared independence of cell indices follows
when those indices are measurable functions of iid observations. It is part
of the abstract random-vector encoding and adds no restriction to its iid
statistical applications.

Lemma 5.2 uses `B=2p>=n`, amplitudes in `[0,1]`, and the original pointwise
bound `abs(u*score_u)+abs(v*score_v)<=1/2`. Its Gamma coefficient is the literal
prior-expectation difference. Its norm uses the unnormalized two-block measure
`2*mu`; with normalized cube-times-two-label `mu`, this is
Lebesgue-times-counting measure. `Lambda=2*v0*n/B`, and the Poisson pair mean is
`2*barp*Lambda`. Count means greater than one are permitted. The construction's
stronger global score budget is a sufficient condition used in instantiated
families, not an extra premise of the original comparison endpoint.

Proposition 5.3 is a genuine conditional theorem. Its `GridExistenceHypothesis`
requires primitive admissible priors, the coefficient estimate and bilinear
separation on every sufficiently large eligible grid. It does not assume a
Hellinger bound, concentration, fixed-sample testing result, or the final
minimax conclusion. The lattice construction supplies the primitive hypotheses
when proving the headline lower bound.

For Proposition 7.1, `StandingData` is an **input structure**, not the proved
proposition. The two listed theorems establish the rough and parametric
conclusions. The rough target-offset identity is required only on selected
hard laws, even if the containing class includes unrelated laws. Constants
precede later containing classes, target functions and additive offsets.
The parametric probability family is clipped outside its relevant neighborhood
to define a law for every real parameter; on the neighborhood used in the
proof it is exactly the paper's affine path.

## Applications, examples and remarks

The JSON maps twenty application rows, including missing-data means, ATE,
ATT, ATU, expected conditional covariance/variance, products/squares of
conditional means, explained variance, population R squared, squared CATE and
CATE variance, Wald ratios, overlap weighting, and prediction loss versus a
known bounded predictor.

The eta classes retain `H>2` and `0<eta<1/4`. Separately bounded
propensity/design classes retain the original density interval in the lower
bound and a fixed widened interval in the upper bound. Their logarithmic
squeeze gives the paper's `o(sqrt(log n))` statement; it is not a claim of a
finite-sample identical-interval bracket. R squared retains `0<vmin<1`.
Predictor-uniform endpoints choose constants before every measurable predictor
at the fixed prescribed bound.

The overlap class controls the marginal outcome regression and propensity,
rather than imposing smoothness on both arm regressions. Causal
interpretations require the stated identification assumptions. The real
potential-outcome wrappers derive required bounds from bounded observed
outcomes and the identification assumptions; they do not require bounds on
never-observed potential outcomes.

| Paper example or remark | Stable label | Representative endpoint |
| --- | --- | --- |
| Example 2.1 | `ex:mar` | `Causal.observedMean_fullData_identification`, `real_ate_potential_identification` |
| Example 2.2 | `ex:conditional` | `Conditional.prediction_loss_decomposition`, `ConditionalExamples.mean_conditional_covariance`, `mean_conditional_variance` |
| Remark 2.4 | `rem:gap` | `Model.main_log_risk`, `Model.Bracket.remaining_gap_factor` |
| Remark 2.5 | `rem:smooth-design` | `Model.smooth_localClass_bracket`, `LatticePriors.SourceLatticeSetup.source_density_derivatives_unbounded` |
| Remark A.4 | `rem:combining-rates` | `RateCombination.finite_rate_sum_eventually_le` |
| Example D.1 | `ex:wald` | `Causal.RealIVData.class_wald_identification` |
| Example D.2 | `ex:conditional-wald` | `Causal.RealIVData.witness_complier_identification` |
| Example D.3 | `ex:overlap-effect` | `Applications.Overlap.effect_is_unrestricted_least_squares_optimum` |

## Mathematical limitations and proof routes

The rough upper/lower scales leave the logarithmic ratio
`(log n)^(nu/2-3/4)`, equal to `(log n)^(1/4)` when `nu=2`. The development does
not close that gap. Estimator tuning uses known smoothness indices, numerical
bounds and other class parameters; no adaptive attainability theorem is
claimed.

Persistence under `C-infinity` covariate density imposes no uniform bound on
the density's derivatives. The smooth hard construction can have derivatives
growing with its shrinking blocks. This result does not imply persistence
inside a fixed positive density-smoothness ball.

The formal proof expands the paper's analytic, Holder-calculus,
marked-Poisson, concentration and experiment-transfer steps. It also uses
proved coordinate/multi-index, seed/kernel and norm/integral bridges. These
longer proof routes preserve the statistical target; the selected theorem is
not merely a rate algebra consequence of assumed minimax bounds.

Cited external efficiency, known/smooth-design, adaptive-estimator and
concurrent-work results are background. The source inventory does not assert
that those papers' results are independently formalized here. Definitions of
desired conclusions and conditional analytic/reduction infrastructure are
listed distinctly from proved headline endpoints. All semantic review
performed for this preparation is automated; author or maintainer attribution
does not imply human mathematical review.
