# Nearly minimax functional estimation under rough random design

Lean formalization of **Nearly Minimax Rates for Functional Estimation Under Rough Random Design**, by **P. M. Aronow, Nathan Kallus, and Patrick Lopatto**. The formalization authors and responsible maintainers are **P. M. Aronow and Patrick Lopatto**.

The project studies estimation of

\[
\psi(P)=E_P[W]+\lambda\int_{[0,1]^d}a(x)b(x)g(x)\,dx,
\qquad g(x)=w(x)p(x),
\]

where `w = E[D | X]`, `a = E[U | X] / w`, `b = E[V | X] / w`, the conditional ratios have Hölder smoothness `α, β`, and the weighted design density satisfies `g₋ ≤ g ≤ g₊`. The design density need not have a uniform smoothness bound.

## Results

[Challenge.lean](Challenge.lean) states the two parts of **Theorem 2.3** using concrete probability laws, conditional expectations, Hölder balls, iid experiments, and measurable randomized estimators. It imports only Mathlib. Its two intentional theorem placeholders specify the targets; [Solution.lean](Solution.lean) supplies the corresponding proofs from the substantive development.

Put `θ = (α + β) / d`, `ρ = (√g₊ − √g₋)/(√g₊ + √g₋)`, `τ = −log ρ`, and

\[
a_n=n^{-\theta}(\log n)^{\theta/2}
 \exp\{-2\sqrt{\theta(1-2\theta)\tau\log n}\}.
\]

The upper bound is `C n⁻¹ᐟ²` for `θ ≥ 1/2`, and `C aₙ (log n)^(ν/2 + 1/4)` for `0 < θ < 1/2`, where `ν` is the sum of the local polynomial dimensions. A finite-support interior nondegenerate baseline gives a lower bound `c n⁻¹ᐟ²` in the first regime and `c aₙ log n` in the second. The latter includes a minimax probability lower bound of `1/4` at error threshold `2c aₙ log n`. The lower constants precede every intermediate class containing the specified local neighborhood.

These are nearly minimax bounds. The remaining logarithmic factor `(log n)^(ν/2 − 3/4)` is unresolved; it is `(log n)^(1/4)` when `0 < α, β ≤ 1`. The formalization does not close that gap.

## Source map

| Path | Purpose |
| --- | --- |
| [paper/main.tex](paper/main.tex) and [paper/body.tex](paper/body.tex) | Attached Hexagon v1 paper, preserved as supplied |
| [Challenge.lean](Challenge.lean) | Independently readable statement of the selected results |
| [Solution.lean](Solution.lean) | Proved declarations with the same names and types |
| [RoughRegime/](RoughRegime/) and [RoughRegime.lean](RoughRegime.lean) | Full substantive proof development and umbrella imports |
| [NumberedClaims.lean](NumberedClaims.lean) | Explicit typed checks for selected numbered claims; [scope](docs/numbered-checks.md) |
| [comparator.json](comparator.json) | Exact statement/proof comparison and permitted axioms |
| [formalization.yaml](formalization.yaml) | Mathematical scope, provenance, attribution, automation, and review |
| [docs/coverage.md](docs/coverage.md) | Numbered paper claims and exact Lean endpoints |
| [docs/fidelity.md](docs/fidelity.md) | Definitions, hypotheses, quantifiers, and proof-route qualifications |
| [docs/boundary-regularity.md](docs/boundary-regularity.md) | Closed-cube convention, proved boundary bridge, and remaining interior translation |
| [docs/provenance.md](docs/provenance.md) | Source identities and separate AI contribution disclosures |
| [docs/verification.json](docs/verification.json) | Checks and source fingerprint for this prepared snapshot |

## Installation and verification

Use Linux with Git, Python 3.11 or later, Elan, and bubblewrap (`bwrap`). Install the Python dependencies from [scripts/requirements.txt](scripts/requirements.txt). Elan selects the exact release in [lean-toolchain](lean-toolchain): **Lean 4.35.0-rc2**. Mathlib is pinned to **065356127b1dc0016f66b7283ce0ce2c4055aa55**; [lake-manifest.json](lake-manifest.json) pins its full dependency closure.

```sh
python3 -m pip install --require-hashes -r scripts/requirements.txt
lake exe cache get
python3 scripts/verify.py --static
python3 scripts/verify.py
```

The verifier checks metadata and source limits, builds every submitted Lean source, checks the coverage endpoints, and audits transitive axiom dependencies. It runs the toolchain's Comparator with the bundled **NanoDa and con-ron** independent kernels enabled in a temporary protected configuration. Raw verification output is written outside the source tree. A failure or missing check returns a nonzero status; compilation alone is not a complete verification pass.

The [verification record](docs/verification.json) states which checks actually completed and identifies the exact checked source content. It supersedes verification claims in the input archive. Mechanical proof checks do not establish source fidelity or human mathematical review.

To compile the paper separately, run `latexmk -pdf main.tex` from `paper/` using a TeX installation with the packages named in its preamble.

## Scope and review

The selected Comparator results are exactly Theorem 2.3(a) and (b). The broader development retains analytic, statistical, local lower-bound, application, and causal-interpretation modules; its [coverage map](docs/coverage.md) distinguishes proved endpoints from definitions and conditional infrastructure. Cited background and literature claims are not advertised as independently formalized results.

Hölder smoothness uses order `ceil(t) − 1`, so integer smoothness means a Lipschitz highest derivative. Risk is represented in the extended nonnegative reals by the L2 norm. Randomization uses an independent uniform real seed; the development contains the bridge to real-output Markov estimators. Upper constants are uniform over observables with fixed magnitude bounds. Lower bounds retain the source's finite-support baseline, either nondegeneracy alternative, positive local radius, and class quantifiers. The positive `M0` parameter excludes inconsistent empty classes already ruled out by the source's nonempty-class condition.

Closed-cube derivatives are continuous extensions of interior derivatives. The [boundary bridge](docs/boundary-regularity.md) proves that continuous finite interior derivative jets yield exactly the encoded `ContDiffOn` regularity and within-cube coefficients, without changing the Hölder radius. Finite-coordinate reconstruction is also proved. The ordinary interior conversion from classical partials to Fréchet derivatives is mathematically explained but is not separately mechanized; full literal coordinate-definition equivalence is therefore not claimed as a completed Lean theorem.

Review recorded for this preparation is **automated review by Codex**. Authorship and maintenance responsibility do not imply human review, peer review, or endorsement of any verification claim.

## Attribution and licensing

**Sol 6.1 autoformalized the original development.** Subsequent **Codex preparation and compatibility work** and **Codex automated review** are disclosed separately in [docs/provenance.md](docs/provenance.md) and [formalization.yaml](formalization.yaml).

Original repository code and documentation are licensed under the **MIT License** in [LICENSE](LICENSE). The supplied paper remains attributed to its three authors; this repository does not change its publication rights. External dependencies and vendored verification tools retain their own licenses and notices, listed in [docs/licenses.md](docs/licenses.md).
