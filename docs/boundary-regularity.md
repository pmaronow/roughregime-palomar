# Closed-cube Hölder regularity

Let `Q = [0,1]^d`, `U = interior Q`, and `k = ceil(t)-1`. The paper's
continuous partial derivatives on the closed cube mean ordinary interior mixed
partials with continuous extensions to `Q`. Boundary values are therefore the
limits determined by the interior. No differentiability of a representative
outside `Q` is required.

The literal coordinate-partial definition and the encoded `ContDiffOn ℝ k f Q`
condition are equivalent in Lean, for every finite order and dimension. The
proof identifies every derivative coefficient throughout `Q` and gives exact
equality of the Hölder norms. It neither adds a boundary smoothness hypothesis
nor changes the radius `H`.

## Literal source predicate

[LiteralHolder.lean](../RoughRegime/LiteralHolder.lean) defines coefficient fields
`c q σ x`, where `q` is the derivative order and `σ : Fin q → Fin d` is an ordered
word of coordinate indices. `CoordinatePartialJet k f c` requires only:

- The order-zero field equals `f` on `Q`.
- Every field through order `k` is continuous on `Q`.
- For `q < k`, differentiating `c q σ` along the genuine one-dimensional curve
  that updates coordinate `j` of an interior point gives
  `c (q+1) (Fin.cons j σ)` at that point, expressed by `HasDerivAt`.

There is no `ContDiffOn`, `HasFDerivAt`, or `iteratedFDerivWithin` hypothesis in
this source predicate. Derivatives are required only in `U`; continuity determines
their boundary extensions. `CoordinatePartialRegularity k f` is the existence of
such a coefficient family.

The ordered-word indexing expresses the usual requirement that all mixed
partials through the stated order exist and are continuous. It does not assume
mixed-partial symmetry. The proof subsequently derives symmetry and identifies
these words with classical multi-indices. The norm uses the canonical
`multiIndexWord` for each multi-index, so the indexing does not change the paper's
maximum or its normalization.

## Mechanized statements

| Declaration | Exact content |
| --- | --- |
| `coordinatePartialRegularity_iff_contDiffOn` | `CoordinatePartialRegularity k f ↔ ContDiffOn ℝ k f Q`, for every finite `k` and dimension |
| `CoordinatePartialJet.coordinate_eq` | Each supplied ordinary partial through order `k` equals `coordinateDerivative f q σ` everywhere on `Q`, including boundary points |
| `holderNorm_eq_literalHolderNorm` | The model's Hölder norm equals the literal partial-derivative sum-of-maxima norm exactly, including infinite values |
| `interiorJet_iff_contDiffOn` | Continuous finite interior Fréchet jets are equivalent to `ContDiffOn` on `Q`, also for arbitrary normed real codomains |
| `hasFDerivWithinAt_cube_of_interior_jet` | Continuous functions and continuous interior derivative fields give the same within-cube derivative at every point of `Q` |
| `InteriorTaylorJet.eq_iteratedFDerivWithin` | Every supplied tensor coefficient through order `k` equals `iteratedFDerivWithin` on all of `Q` |

`literalDerivativeSup` is the maximum over orders `q ≤ k` and multi-indices of
the supremum of the absolute coefficient on `Q`. `literalHolderSeminorm` is the
maximum, at order `k`, of

\[
 \sup_{x\ne y\in Q}
 \frac{|D^\nu f(x)-D^\nu f(y)|}{\|x-y\|_2^{t-k}}.
\]

For `t > 0`, `literalHolderNorm` adds these two quantities when the literal
regularity predicate holds and gives infinity when it fails. The coefficient
family is chosen existentially; the coefficient equality theorem makes its
values on `Q` independent of that choice. The formal norm also assigns infinity
to `t ≤ 0`, matching the model's existing extension of the paper's positive-order
convention. Integer `t` still means Lipschitz derivatives of order `t-1`.
For `0 < t ≤ 1`, regularity reduces exactly to continuity on `Q`.

## Proof route

[ContinuousPartials.lean](../RoughRegime/ContinuousPartials.lean) proves the
interior calculus criterion from actual one-dimensional coordinate derivatives
and continuity of their fields. It inducts over the finite number of coordinates,
using Mathlib's `hasStrictFDerivAt_uncurry_coprod` for a binary product. The theorem
first applies to finite coordinate products and then transfers through the
continuous linear equivalence to Euclidean space. It derives a strict Fréchet
derivative rather than assuming one.

[CoordinateJets.lean](../RoughRegime/CoordinateJets.lean) proves that a multilinear
tensor is determined by its finitely many coordinate-basis evaluations and
provides the exact inverse reconstruction. Scalar coefficient continuity is
equivalent to continuity of the tensor. In particular, the coefficient fields
assemble as

\[
 T_q(x)[v_1,\ldots,v_q]
 =\sum_{i_1,\ldots,i_q}
    c_q(i_1,\ldots,i_q,x)
    \prod_{r=1}^{q}(v_r)_{i_r}.
\]

For `q=0` this is `f(x)`. Applying the interior calculus criterion to successive
scalar fields, and differentiating this finite reconstruction, gives the interior
link from `T_q` to the appropriate currying of `T_(q+1)`.

[BoundaryRegularity.lean](../RoughRegime/BoundaryRegularity.lean) then extends these
identities to `Q`. The cube is closed and convex with dense interior; Mathlib's
`hasFDerivWithinAt_closure_of_tendsto_fderiv` uses the continuous function and
derivative limits to give the boundary derivatives. The resulting finite Taylor
jet proves `ContDiffOn` and identifies all tensors with the model's iterated
within-cube derivatives.

Conversely, `ContDiffOn` gives continuous iterated within-cube derivatives through
order `k`. Restricting to `U` and differentiating their coordinate evaluations
gives the ordinary coordinate-update derivatives required by
`CoordinatePartialJet`. This proves both directions of the regularity equivalence.
[MultiIndexHolder.lean](../RoughRegime/MultiIndexHolder.lean) supplies the mixed-partial
symmetry and equality between ordered-coordinate and multi-index maxima.

All coefficients agree exactly. The proof does not replace the paper's maximum
by an operator norm or use a norm-equivalence constant to enlarge `H`. No smooth
global extension or Whitney extension theorem is used. These are subsequent Codex
calculus, tensor, and boundary additions, separate from Sol 6.1's original
autoformalization; the attributions are in [provenance.md](provenance.md).

The pinned Mathlib ingredients are in
[FDeriv/Partial.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Partial.lean)
and
[FDeriv/Extend.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Extend.lean).

## Verification scope

These additions preserve the selected Challenge and Solution statements and the
supplied paper sources. The project verifier builds submitted Lean sources and
audits transitive proof axioms. The actual completed checks, independent kernel
results, and checked source fingerprint are in [verification.json](verification.json).

An unsandboxed diagnostic result does not satisfy Palomar's protected verification
requirement. The protected run remains subject to the recorded namespace blocker;
a calculus equivalence theorem does not remove that environment restriction.
Mathematical fidelity assessment and review of these additions are automated.
Neither authorship nor these mechanical checks assert human mathematical review.
