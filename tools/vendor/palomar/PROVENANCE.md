# Vendored validator provenance

These files are copied unchanged from
[PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission) at
commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, inspected on October 9,
2026 (UTC). They provide the mechanical formalization profile version 4 and
submitted-source requirements used by this package's local verifier.

The preserved import closure consists of `scripts/submission_contract.py`,
`scripts/source_requirements.py`, `scripts/orcid_validation.py`,
`scripts/verification_errors.py`, `scripts/__init__.py`, and the two taxonomy
snapshots. The local verifier calls metadata parsing and source inspection;
it does not call the ORCID helper's network functions.

Upstream's [MIT license](LICENSE) applies to its validation software.
Third-party taxonomy provenance and terms are preserved in
[taxonomies/README.md](taxonomies/README.md) and
[taxonomies/LICENSE.md](taxonomies/LICENSE.md); the MSC2020 data are subject
to CC BY-NC-SA 4.0, not the project's MIT grant. The arXiv taxonomy notice is
also retained. No PalomarTemplate implementation is included here.

The local `verify.py` reproduces the required functional Comparator
configuration fields and invokes the bundled toolchain. It is not a copy of
Palomar's complete protected verification service. Its plain-identifier
Comparator validation is deliberately narrower than upstream's general Lean
identifier grammar; all names used by this project satisfy it.
