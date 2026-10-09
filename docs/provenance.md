# Attribution and production provenance

The mathematical source is **Nearly Minimax Rates for Functional Estimation Under Rough Random Design**, Hexagon 2610.00157, version 1, by **P. M. Aronow, Nathan Kallus, and Patrick Lopatto**. The retained paper sources are unchanged from the supplied version. The selected claims are Theorem 2.3(a) and (b), stable label `thm:generic`.

The formalization authors and responsible maintainers are **P. M. Aronow and Patrick Lopatto**. This identifies credit and responsibility; it does not assert that either person reviewed the Lean code or checked the mathematical fidelity of this prepared snapshot.

## AI contributions

1. **Original autoformalization:** Sol 6.1 autoformalized the original development. This attribution is supplied by the responsible user. No unrecorded prompt history, effort, or review is reconstructed.
2. **Subsequent preparation and compatibility:** Codex prepared the standalone Challenge/Solution surface, metadata, public documentation, licensing, and verification tools, and ported the supplied development to the pinned release and its module-system requirements. The mathematical statements are preserved during compatibility work. Codex subsequently added the finite-order boundary extension and exact coordinate reconstruction proofs in `BoundaryRegularity.lean` and `CoordinateJets.lean`; these additions are separate from Sol 6.1's original autoformalization.
3. **Subsequent automated review:** Codex performed separate source-statement and numbered-claim reviews, inspected mathematical scope and conditional premises, and assessed the mechanical verification evidence. These are automated reviews, not human mathematical review or peer review.

The production roles are also recorded in `formalization.yaml`. Compilation and kernel checks are separate evidence from a semantic source comparison.

The standalone Challenge clears Lean's local auxiliary-lemma naming cache between its inline rate and model definitions. This reproduces the original separate-module compilation boundary for Comparator's exact constant comparison; it changes no mathematical definition or proof.

## Reproducible identity

`docs/verification.json` records the exact checked content fingerprint and completed checks. The associated source manifest enumerates the files to which that fingerprint applies. Any changed source or dependency pin requires new verification. Historical reports supplied with the development are not represented as a current pass.

The mathematical source files have SHA256 digests:

| File | SHA256 |
| --- | --- |
| `paper/main.tex` | `e2556479154b42ab457e29d931c998ce4dccd477109ebad29465fa71b028bc98` |
| `paper/body.tex` | `e2b0f98a4a9a799b68abb51049405967464300fc8ba1d43e91d2631c19f5b4b4` |

Exact dependency revisions are retained in `lake-manifest.json`. The original development used Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; the prepared project pins Lean 4.35.0-rc2 and canonical Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` to meet the current source-module and Comparator requirements. Compatibility changes and environment qualifications are reported with the fresh verification evidence.
