# Attribution and production provenance

The mathematical source is [**Nearly Minimax Rates for Functional Estimation Under Rough Random Design**](https://hexagonmath.org/2610.00157v1), Hexagon 2610.00157, version 1, by **P. M. Aronow, Nathan Kallus, and Patrick Lopatto**. The retained paper sources are unchanged from the supplied version. A source archive fetched from the version 1 Hexagon record on October 9, 2026 had byte-identical `main.tex` and `body.tex`. That record identifies the paper's license as [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), separate from the MIT license for original code and repository documentation. The selected claims are Theorem 2.3(a) and (b), stable label `thm:generic`.

The formalization authors and responsible maintainers are **P. M. Aronow and Patrick Lopatto**. This identifies credit and responsibility; it does not assert that either person reviewed the Lean code or checked the mathematical fidelity of this prepared snapshot.

## AI contributions

1. **Original autoformalization:** Sol 6.1 autoformalized the original development. This attribution is supplied by the responsible user. No unrecorded prompt history, effort, or review is reconstructed.
2. **Retained prior preparation and compatibility:** The supplied provenance attributes the standalone Challenge/Solution surface, the earlier toolchain port, and the finite-order boundary extension, exact coordinate reconstruction, ordinary-partial calculus criterion, and literal Hölder definition equivalence to subsequent Codex work. These bridge proofs in `BoundaryRegularity.lean`, `CoordinateJets.lean`, `ContinuousPartials.lean`, and `LiteralHolder.lean` were already present in the supplied development. Their attribution is retained separately from Sol 6.1's original autoformalization; this preparation does not reconstruct their production history.
3. **Current local preparation:** Codex reconciled the supplied source with the current paper and Palomar contract, refreshed public documentation and metadata, preserved licensing and scope disclosures, repaired local dependency-installation reproducibility, and prepared clean local repository and archive outputs. Existing mathematical statements and proof development were retained.
4. **Current automated review and verification:** Codex separately compared source statements and numbered claims, inspected mathematical scope and conditional premises, and ran the mechanical checks reported in [verification.json](verification.json). These are automated reviews, not human mathematical review or peer review. The record identifies completed checks and blockers; earlier supplied build reports are not current evidence.

The production roles are also recorded in [formalization.yaml](../formalization.yaml). Compilation and kernel checks are separate evidence from a semantic source comparison. Material scope qualifications are preserved in [fidelity](fidelity.md), [coverage](coverage.md), and [numbered-claim checks](numbered-checks.md).

The standalone Challenge clears Lean's local auxiliary-lemma naming cache between its inline rate and model definitions. This reproduces the original separate-module compilation boundary for Comparator's exact constant comparison; it changes no mathematical definition or proof.

## Reproducible identity

[docs/verification.json](verification.json) records the exact checked content fingerprint and completed checks. The associated [source manifest](source-manifest.json) enumerates the files to which that fingerprint applies. Any changed source or dependency pin requires new verification. Historical reports supplied with the development are not represented as a current pass. Git commit identity, when available, is supplementary: the content fingerprint identifies the checked public files even when operational files or later Git metadata differ.

The mathematical source files have SHA256 digests:

| File | SHA256 |
| --- | --- |
| `paper/main.tex` | `e2556479154b42ab457e29d931c998ce4dccd477109ebad29465fa71b028bc98` |
| `paper/body.tex` | `e2b0f98a4a9a799b68abb51049405967464300fc8ba1d43e91d2631c19f5b4b4` |

Exact dependency revisions are retained in `lake-manifest.json`. The supplied provenance records an original Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` development followed by a port to Lean 4.35.0-rc2 and canonical Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The prepared repository retains those latter pins, which meet the current source-module and Comparator requirements. Fresh verification applies to the retained pinned source, rather than certifying that earlier port history.

The source and metadata checks use unchanged selected validators from [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) at `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` (October 5, 2026), inspected on October 9, 2026. This implementation requires bundled Comparator with Lean, NanoDa, and con-ron and Lean 4.35.0-rc2 or later. The published [Palomar policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md) at `96b034cc31a72a63d4f4041911dce337a85c9a04` still describes earlier tooling; this repository follows the newer implementation while preserving the policy's authorship, licensing, and disclosure requirements. The [vendor provenance](../tools/vendor/palomar/PROVENANCE.md) identifies the exact retained validation files and their notices.
