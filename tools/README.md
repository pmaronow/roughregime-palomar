# Reproducible local verification

`scripts/verify.py` checks the current public source snapshot. It writes reports,
temporary Comparator configurations, and compiler transcripts to an external
directory. It does not publish, submit, or register anything.

Use Python 3.11 or later and the exact Lean toolchain in `lean-toolchain`:

```bash
python3 -m pip install --require-hashes -r scripts/requirements.txt
lake exe cache get
python3 scripts/verify.py --output ../verification-output
```

An optional `--static-only` run checks the source package without claiming a
build or kernel replay. Its report is explicitly `incomplete` for full
verification even when those static checks succeed. Full verification requires
`lake`, `lean`, and `bwrap` on `PATH`, plus the pinned toolchain's bundled
`leanexport`, `leanchecker`, `nanoda_bin`, and `con-ron` executables. Missing
executables or unavailable sandbox support are blockers, not passes.

The primary Comparator check first probes bubblewrap namespace creation with
a ten-second bound. A rejected probe records its exit status and transcript
and blocks that check before launching Lake. Passing this environment probe
does not establish proof verification. The explicitly requested supplementary
unsandboxed diagnostic skips the probe and cannot repair the primary status.

The checks cover:

- The exact vendored Palomar formalization metadata validator, module headers,
  the 10,000-line source limit, the Challenge limits, and the repository cap.
- Concrete Comparator configuration, absence of implementation proof holes and
  custom axioms, exact dependency pins, canonical mathlib's pinned manifest
  closure, clean matching dependency checkouts, and local file links.
- Compiler-parsed headers of every source and the Challenge's direct and
  transitive imports, resolved only to the pinned Lean core and canonical
  mathlib dependency closure.
- Explicit Lake build targets for every regular submitted Lean source,
  declaration coverage, any typed numbered-claim checks, and the transitive
  axiom inventory including selected Solution theorem aliases.
- Comparator using a temporary configuration that installs the toolchain's
  NanoDa and con-ron kernels alongside its Lean kernel. The submitted
  `comparator.json` never supplies `external_kernels`.

`--diagnostic-comparator` additionally requests Comparator's explicit
`--inadvisably-no-sandbox` mode. This is a supplementary local diagnostic,
clearly marked in its evidence; it cannot turn a failed or blocked primary
Comparator run into a successful verification report. Use it only when that
diagnostic is wanted. A local run does not reproduce Palomar's separate,
protected canonical-Challenge compilation and submission sandbox.

That option also exports the sixteen finite-order boundary and coordinate-jet
bridge theorems from `RoughRegime.BoundaryRegularity` and replays their dependencies
with Lean, NanoDa, and con-ron in `--verified` mode. This separate check is explicitly
unsandboxed and is not part of the two-theorem submitted Comparator interface.
Its export content hash and exact root declarations are recorded. It does not
cover the unmechanized ordinary interior coordinate-partial criterion.

The report records the exact source fingerprint, individual public file
hashes, the available Git revision, binary hashes, command exit statuses, and
external transcript hashes. The source fingerprint covers all public files
except `docs/source-manifest.json` and `docs/verification.json`, which are
derived evidence and cannot hash themselves. Operational `.git`, `.lake`,
Python caches, virtual environments, and verification output directories are
excluded. The tool rejects an output directory inside the public source tree
and checks that the source snapshot did not change during verification. Any
environment-specific `LD_PRELOAD` is recorded rather than silently omitted.

Mechanical checks do not establish mathematical equivalence to the paper or
human mathematical review. Numbered targets provide only the coverage their
exact typed declarations assert. See the project's coverage documentation.
The local Markdown check verifies file destinations; it does not fetch
external websites or validate fragment anchors.

Original verification code is MIT licensed. The selected upstream metadata
and source validators in `vendor/palomar` remain subject to their preserved
MIT license. Its taxonomy data carry separate notices and MSC2020 licensing;
see [vendor provenance](vendor/palomar/PROVENANCE.md) and
[taxonomy license](vendor/palomar/taxonomies/LICENSE.md).

## Recorded environment workaround

This preparation environment exposes `/proc/self/exe` but fails reads of the
numeric `/proc/<pid>/exe` path used by the toolchain to locate itself. The
small [readlink shim source](environment/proc-exe-shim.c) records the exact
workaround used for the local build. It redirects only that executable-path
lookup; it does not alter Lean, proof terms, or kernel logic. Its compiled
library and the toolchain are operational files outside the public source.
The verifier never installs this workaround automatically. Ordinary Linux
verification should use the unmodified toolchain without a preload.

The local evidence records the preload binary hash and this environmental
qualification. Bubblewrap namespace support remains a separate requirement;
this shim does not provide it or complete a protected Comparator check.
