# Closed-cube Hölder regularity

Let `Q = [0,1]^d`, `U = interior Q`, and `k = ceil(t)-1`. The paper's
continuous partial derivatives on the closed cube are interpreted as the ordinary
interior mixed partials, with continuous extensions to `Q`. Boundary derivatives
therefore have the limits determined by the interior. This is the usual closed-cube
convention; no differentiability of an arbitrary representative outside `Q` is
required.

Under this convention, the paper's regularity condition and the Lean condition
`ContDiffOn ℝ k f Q` are mathematically equivalent. The boundary passage and the
exact coordinate tensor reconstruction are now proved in Lean. The elementary
interior theorem converting continuous classical partial derivatives to Fréchet
derivatives is explained below but is not separately mechanized here. Consequently,
this addition resolves the boundary extension issue without claiming that the
literal coordinate-partial definition has a complete end-to-end Lean equivalence
theorem.

## Mechanized statements

[BoundaryRegularity.lean](../RoughRegime/BoundaryRegularity.lean) defines
`InteriorJet k f` recursively. At order zero it is continuity on `Q`. At order
`k+1` it requires continuity of `f` on `Q` and a derivative field `g` that has
`InteriorJet k g`; `HasFDerivAt f (g x) x` is required only for `x` in `U`.
There is no `ContDiffOn` assumption in this predicate and no assumed boundary
derivative identity.

| Declaration | Exact content |
| --- | --- |
| `interiorJet_iff_contDiffOn` | `InteriorJet k f ↔ ContDiffOn ℝ k f Q`, for every finite order, dimension, and normed real codomain |
| `hasFDerivWithinAt_cube_of_interior_jet` | A continuous function and continuous interior derivative field give the same derivative within the cube at every point of the cube |
| `InteriorTaylorJet.ftaylorSeries` | Continuous finite tensor jets with interior derivative linkage form genuine within-cube Taylor jets |
| `InteriorTaylorJet.eq_iteratedFDerivWithin` | Every supplied tensor coefficient through order `k` equals `iteratedFDerivWithin` on all of `Q` |
| `InteriorTaylorJet.coordinate_eq` | Exact equality of supplied coordinate coefficients and the model's coordinate derivatives, including boundary values |
| `holderNorm_eq_interiorJetHolderNorm` | Replacing the regularity gate by `InteriorJet` leaves the multi-index sum-of-maxima Hölder norm exactly unchanged, including the infinite-value case |
| `holderRegularity_le_one_iff` | For `t ≤ 1`, the regularity gate is exactly continuity on `Q` |

[CoordinateJets.lean](../RoughRegime/CoordinateJets.lean) proves that a multilinear
tensor is determined by its finitely many coordinate-basis evaluations. It provides
an explicit inverse reconstruction and proves that tensor continuity is equivalent
to continuity of those scalar coefficients. This holds for every dimension and
derivative order. Tensor reconstruction preserves the coefficients exactly; it
does not replace the paper's maximum by an operator norm.

## Mathematical correspondence with classical partials

For a function with the paper's continuous partials, continuous first coordinate
partials imply ordinary Fréchet differentiability in the open set `U`. One proof
telescopes the increment along coordinate segments and applies the one-dimensional
fundamental theorem of calculus. Subtracting
`sum_j partial_j f(x) h_j` leaves a remainder bounded by
`sum_j |h_j|` times the maximum oscillation of the partials near `x`.
Continuity makes that oscillation tend to zero; the finite-dimensional inequality
`sum_j |h_j| ≤ sqrt(d) norm(h)` gives the required small remainder. Applying this
argument to successive partial derivatives gives the ordinary interior derivative
tensors through order `k`. Equality of mixed partials follows from continuous
differentiability in the interior.

At each point of the closed cube assemble the continuous extended coefficients as

\[
 T_q(x)[v_1,\ldots,v_q]
 =\sum_{i_1,\ldots,i_q}
    D_{i_1}\cdots D_{i_q}f(x)
    \prod_{r=1}^{q}(v_r)_{i_r}.
\]

For `q=0` this is the value of `f`. The finite-coordinate reconstruction theorem
gives continuity of each `T_q` on `Q`. In the interior, the derivative of `T_q`
is the appropriate currying of `T_(q+1)` for `q<k`.

The cube is closed and convex, with dense nonempty interior. The Mathlib theorem
`hasFDerivWithinAt_closure_of_tendsto_fderiv` extends these identities to `Q`:
continuity of `T_q` supplies the function limits, and continuity of `T_(q+1)`
supplies the derivative limits. The explicit finite-jet theorem then gives
`ContDiffOn` and identifies every `T_q` with the existing within-cube derivative.

Conversely, `ContDiffOn` restricts to ordinary smoothness in `U`, and its iterated
within-cube derivatives are continuous on `Q` through order `k`. Their coordinate
evaluations are precisely the continuous extensions of the interior partials.
The existing [multi-index bridge](../RoughRegime/MultiIndexHolder.lean) identifies
ordered coordinate words and classical multi-indices using derivative symmetry.

All derivative values agree exactly. Norm equivalence is used only in proving
continuity and differentiability; it does not inflate the Hölder radius `H` or
change any rate, hypothesis, or conclusion. Integer `t` still means Lipschitz
derivatives of order `t-1`. In particular, for `0<t≤1`, `k=0` and the correspondence
already reduces exactly to continuity, without any positive-order conversion.

The pinned Mathlib boundary theorem is in
[FDeriv/Extend.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/FDeriv/Extend.lean).
No smooth global extension or Whitney extension theorem is used.

## Verification scope

These additions preserve the selected Challenge and Solution statements and the
supplied paper sources. The project axiom audit includes all their proof bodies.
The verifier's optional diagnostic also exports these specific bridge declarations
and checks them with Lean, NanoDa, and con-ron. As with the main Comparator diagnostic,
an unsandboxed result does not satisfy Palomar's protected verification requirement.
Actual check outcomes and the checked source fingerprint appear in
[verification.json](verification.json).

The remaining formal correspondence step is specifically the ordinary interior
coordinate-partial-to-Fréchet criterion in arbitrary dimension. It is not an extra
boundary hypothesis, a change of statistical model, or a mathematical obstruction
identified in the selected theorem. The mathematical argument above is an automated
assessment and does not assert human review.
