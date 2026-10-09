# Mathematical fidelity review of the selected generic minimax theorem

## Sources and status

The authoritative mathematical paper is the separately attached Hexagon source:
[`paper/main.tex`](../paper/main.tex) and [`paper/body.tex`](../paper/body.tex). Its title is **Nearly
Minimax Rates for Functional Estimation Under Rough Random Design** and its paper
authors are **P. M. Aronow, Nathan Kallus, and Patrick Lopatto**. The selected result
is **Theorem 2.3 (Minimax bounds)**, source label `thm:generic`, parts (a) and (b).
The numbering and stable source labels here follow the retained paper. The auxiliary
examples in the same chapter precede it.

The formal source reviewed directly is `Model.lean`, `Rates.lean`, `ModelUpper.lean`,
`ModelLower.lean`, and the supporting endpoints listed below. This is an automated source-statement review. Authorship and responsibility
do not establish human mathematical review. Compiler, axiom, Comparator, and independent
kernel results must be reported separately, against the final prepared revision.

## Selected endpoints

| Paper claim | Proved source endpoint | Public submission endpoint |
|---|---|---|
| Theorem 2.3(a), uniform generic upper bound | `RoughRegime.Model.uniformUpperClaim` in `ModelUpper.lean` | `RoughRegimeSubmission.mainUpper` |
| Theorem 2.3(b), local generic lower bound and rough quarter-tail bound | `RoughRegime.Model.mainLowerClaim` in `ModelLower.lean` | `RoughRegimeSubmission.mainLower` |

[`Challenge.lean`](../Challenge.lean) imports Mathlib only and supplies the statistical
objects explicitly. It reproduces the required concrete original definitions under
their original names, followed by the two intentional challenge placeholders.
[`Solution.lean`](../Solution.lean) imports the two original proof modules and proves the
same submission theorem names by their actual endpoints. They use module headers, public
imports, and public sections. They are intended to be compared in separate Lean
environments; importing Challenge into Solution would introduce placeholder dependencies
and is deliberately avoided.

## Exact definition and hypothesis comparison

| Mathematical object | Paper convention | Formal convention and assessment |
|---|---|---|
| Dimension/domain | Integer `d >= 1`, covariates on `[0,1]^d` | `d : Nat`, `hd : 1 <= d`; `EuclideanSpace R (Fin d)`, coordinate cube, restricted Euclidean volume. Same dimension and Euclidean norm. |
| Random design | Unknown Lebesgue density `p`, no density smoothness | Nonnegative measurable density witness, marginal exactly `cubeVolume.withDensity (ofReal p)`. No smoothness or shape condition on `p` is assumed. |
| Known observables | Bounded measurable `D,U,V,W`, `0 <= D <= M0`, `abs U, abs V <= M0`, known nonzero lambda | `Observables` has those same measurable functions and bounds, a global finite bound for W, and `lam != 0`. |
| Ratios/weight | `w=E[D|X]`, `a=E[U|X]/w`, `b=E[V|X]/w`, `g=wp` | Witness moments give `E[D|X]=w`, `E[U|X]=wa`, `E[V|X]=wb` almost surely, with w positive. Multiplicative moments are equivalent to the stated ratios on the model. |
| Model restrictions | `w >= delta > 0`, `a in H^alpha(H)`, `b in H^beta(H)`, `0 < gminus <= wp <= gplus`, strict endpoint gap | Exactly these witness restrictions and positive alpha, beta, H, delta, gminus; strict `gminus < gplus`. No positive-definiteness or baseline is imposed on the upper class. |
| Hölder convention | `k=ceil(t)-1`, exponent `t-k in (0,1]`; maximum derivative suprema plus maximum highest-order Hölder seminorm | `holderOrder`, `holderExponent`, `derivativeSup`, `holderSeminorm` use exactly these orders and this sum-of-maxima convention. Integer t means Lipschitz derivatives of order t-1, rather than a silently substituted C^t norm. |
| Target | `E W + lambda E[(E[U|X] E[V|X])/E[D|X]]` | `target` is this conditional-expectation expression on actual measures, not an assumed weighted-integral proxy. `target_weighted_representation` proves it equals `E W + lambda integral a b wp`. |
| Experiment | n independent copies, all measurable estimators including randomized ones | `Measure.pi` over `Fin n` plus independent uniform seed on the closed unit interval, all jointly measurable real output estimators. `KernelSeedBridge` proves exact equivalence with arbitrary real-output Markov rules, without an added standard-Borel hypothesis on response space. |
| RMSE | infimum over estimators of supremum over laws of square root of mean squared error | `minimaxRMSE` is infimum of supremum of actual eLpNorm at p=2. `RiskBridge` proves the exact squared-integral convention, including infinite error and empty classes. |
| Tail risk | infimum/supremum of probability that absolute error is at least threshold | `minimaxTail` evaluates the exact closed error event in the same randomized experiment. |
| Rate constants | `theta=(alpha+beta)/d`, rho from sqrt endpoints, `tau=-log rho`, `kappa=2 sqrt(theta(1-2theta)tau)` | `Parameters.theta` and `Rates` are identical formulas. No enlarged interval replaces the generic theorem's specified sharp interval. |
| Common scale | `a_n=n^-theta (log n)^(theta/2) exp(-kappa sqrt(log n))` | `Rates.subcriticalScale` is exactly this expression; conclusions apply only for n>=n0>=3. |
| Polynomial dimension | `nu=choose(d+ceil(alpha)-1,d)+choose(d+ceil(beta)-1,d)` | `Parameters.nu` uses `holderOrder` and Nat.choose, with identical convention. |

Lean additionally packages `M0 > 0` in Parameters. The paper's meaningful nonempty
classes already force this from `delta > 0`, `w >= delta`, and `D <= M0`; it excludes
only inconsistent/empty choices of the observable magnitude bound, rather than a
statistical case covered by the nonempty-class upper conclusion or by the lower
nondegeneracy assumptions.

The paper defines functions intrinsically on the cube; Lean represents globally
measurable real functions and imposes all Hölder restrictions only within the cube.
Values outside it are irrelevant. Relative differentiability is encoded by
`ContDiffOn` and `iteratedFDerivWithin`. `MultiIndexHolder` proves exact equality of
the ordered-coordinate norm and a canonical multi-index norm, including boundary
symmetry and integer exponents. Both sides of that formal norm identity use the same
`ContDiffOn` regularity gate. Thus this is a formal comparison of the two derivative
indexing conventions, not a separate foundational theorem equating every possible
informal interpretation of continuous cube-boundary partial derivatives with
`ContDiffOn`. The closed-cube relative-derivative convention should be stated in public
documentation; no C-infinity assumption is imposed on upper-bound regressions.

## Upper theorem quantifiers and conclusion

`uniformUpperClaim` proves `UniformUpperClaim A L MW`, which chooses one **C>0** and
one **n0>=3 before** every response type, measurable structure, and observable family
satisfying `abs lambda=L` and `abs W<=MW`. For every n>=n0 and nonempty model class:

- At and above the threshold, `theta >= 1/2`, actual minimax RMSE is at most `C n^-1/2`.
- In the rough branch, `0 < theta < 1/2`, it is at most
  `C a_n (log n)^(nu/2+1/4)`.

This is the paper's “depending only on” statement, not constants chosen after each
unknown law or family. The choice of any upper bound MW rather than the exact W
supremum is harmless strengthening of the bound's uniformity. The theorem is
universe-polymorphic; its uniform response-space quantifier is within a fixed Lean
universe, not a restriction to finite/countable/Borel response spaces. The equality
case theta=1/2 is retained. Both alpha/beta orderings are handled by a proved swap.

The proof constructs actual measurable polynomial estimators and a same-sample
combined empirical W estimator. The relevant chain is:

`ModelProductEstimator` -> `ModelProductRates.uniform_parametricProductEstimator_risk` /
`uniform_subcriticalProductEstimator_risk` ->
`ModelEstimatorCombination.combinedEstimator_eLpNorm_error` -> `ModelUpper.uniformUpperClaim`.

The proof development is substantially more expanded than the paper and has extra
bridges, numerical lemmas, and a capped smoothness exponent in one valid intermediate
variance argument. These are proof choices, not assumptions in the selected endpoint
and not weakened final rates. The separately proved full-gradient projection lemma
should be distinguished from that intermediate capped-exponent proof chain.

## Lower theorem quantifiers and conclusion

`mainLowerClaim` proves `MainLowerClaim A F pi r`. Its only mathematical antecedents
are the source's finite-support baseline nondegeneracy and **every r>0**. It then
chooses one **c>0** and one **n0>=3 before** every intermediate class C and sample n.
The required intermediate-class relations are exactly
`localClass A F pi r subset C subset modelClass A F`.

The baseline quantities are `w0=E_pi D`, `a0=E_pi U/w0`, `b0=E_pi V/w0`. The strict
interior conditions are exactly `max(delta,gminus)<w0<gplus`, `abs a0<H`, `abs b0<H`.
The residual second moments are taken of U-a0D and V-b0D; they have mean zero, so the
condition `uu>0` and `uu*vv-uv^2>0` is precisely positive definiteness of the paper's
2-by-2 covariance matrix. The alternative is exactly global observable equality
U=V, alpha=beta, and positive residual variance. The finite-support clause is
`exists Finset s, pi(s)=1`; no atom cardinality, full-rank condition beyond the stated
alternative, or separate smooth baseline response kernel is added.

For n>=n0, the conclusion retains:

- `theta >= 1/2`: RMSE at least `c n^-1/2`.
- `0 < theta < 1/2`: RMSE at least `c a_n log n`, and minimax error probability at
  threshold **2 c a_n log n** at least **1/4**.

The rough result is proved by genuine canonical finite iid laws and actual lattice
priors, the Poisson-comparison reduction, and a fixed-sample testing theorem, not by
assuming that the desired risks are lower bounded. `ModelLower.mainLowerClaim`
supplies `SourceRoughLower.source_rough_minimax_lower` to `MainLowerAssembly`;
`MainLowerAssembly` alone is only conditional infrastructure. The parametric branch
uses an actual affine baseline path via `ParametricBaselineLower.main_parametric_lower`.
Dimension assembly covers every d>=1; no d=1 or exponent-order limitation survives
in the public endpoint.

## Statements, proved results, and limits

- `UpperBoundAt`, `UniformUpperClaim`, `PerModelUpperClaim`, `MainLowerClaim`,
  `LowerBracket`, `UpperBracket`, `Bracket`, and `HardAtScale` are proposition-valued
  definitions. Merely checking that their names exist proves nothing. The two
  selected Solution declarations prove their actual named predicates.
- Conditional reduction theorems such as `mainLowerClaim_of_rough_lower` and
  `hardness_to_risk` remain useful infrastructure whose premises must be supplied.
  The selected lower theorem supplies the genuine rough source bound.
- `model_bracket` is a proved consequence assembling the two main results on
  intermediate classes. `main_log_risk` and the scale-divergence consequences are
  further genuine endpoints, but are not separate selected Challenge targets.
- The selected interface covers the generic minimax theorem. The large retained
  development includes application-specific and analytic endpoints, but this review
  does not independently certify every application row or every supporting lemma
  merely from old coverage reports. Current theorem-number checks are in the coverage map; transitive axiom checks
  are recorded separately.
- The residual polylogarithmic minimax gap is unresolved: the displayed upper/lower
  ratio is `(log n)^(nu/2-3/4)`, including `(log n)^1/4` when nu=2. Neither the
  formalization nor the selected interface closes that gap or claims exact minimax
  constants.
- The theorem is fixed-parameter and asymptotic, with existential constants and
  sample thresholds. It is not an adaptive estimator or a claim of uniform constants
  as theta tends to the threshold or covariance becomes singular.
- Causal interpretations additionally need the paper's stated causal assumptions.
  Generic theorem selection does not assert causal identification unaided.
- Known/smooth-design rates and historical results cited in the paper remain cited
  background; retaining citations does not independently formalize those authors'
  estimator-attainment claims.

## Verification boundary

No source-statement mismatch was identified for the two selected headline parts.
This semantic assessment does not substitute for building the final modules,
Comparator comparison of concrete copied definitions, transitive axiom inspection,
or the required independent kernel checks. The intentional Challenge sorries must
be excluded from Solution and all proof dependencies. Any final verification claim
must be tied to the prepared source revision rather than to historical packaged
logs or an input theorem count. No Palomar approval or human mathematical review
is established here.
