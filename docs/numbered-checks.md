# Numbered target checks

[`NumberedClaims.lean`](../NumberedClaims.lean) supplies explicit typed proof assignments for Theorem
2.3(a,b), the rate parameter/scale definitions and exact logarithmic scale
identity, Lemma 4.1 (full generating identity and z=1 specialization), Lemma
4.6, Lemma 5.1, Lemma 6.1, and both risk conclusions of Proposition 7.1.
It imports the substantive development and Solution, and never imports
Challenge. Compilation checks each displayed expression by assigning a
proved declaration at that type. This is stronger evidence than a name-only
`#check`, while correspondence with the paper still requires statement review.

| Typed declarations | Paper correspondence and check scope |
| --- | --- |
| `theorem_2_3_a`, `theorem_2_3_b` | Theorem 2.3(a,b): both rate regimes, uniform constant order, intermediate classes, and rough quarter-tail conclusion. |
| `rho_formula`, `scale_formula` | Definitional rate normalization checks; no statistical risk theorem follows from these equalities alone. |
| `scale_logarithm` | Exact logarithm of the scale for `n>1`; this is not the asymptotic log-minimax-risk conclusion of Remark 2.4. |
| `lemma_4_1`, `lemma_4_1_at_one` | Lemma 4.1: complex generating identity and normalized reciprocal specialization. The separate angular formulation is listed in the coverage inventory. |
| `lemma_4_6` | Lemma 4.6: finite separated window sum with the literal numerical constant. |
| `lemma_5_1` | Lemma 5.1: affine probability-density path with the original conditional hypotheses; the formal endpoint also gives a quarter-tail conclusion. |
| `lemma_6_1` | Lemma 6.1: concrete sinc/lattice normalization, gate bounds, deficit, powers, and Fourier support with the bandwidth restriction. |
| `proposition_7_1_rough`, `proposition_7_1_parametric` | Proposition 7.1: risk conclusions for the supplied-score input package. The full prior-construction and arbitrary-smooth-function clauses are not separately expanded here. |

The selected Theorem 2.3 targets expand the uniform upper and intermediate
class lower conclusions instead of checking only `UniformUpperClaim` or
`MainLowerClaim` declaration existence. Proposition 7.1 retains its concrete
input structure, selected hard-law predicates, supplied-score path and full
family/constant/class/target/offset quantifier order. Those predicates name
concrete mathematical conditions; they are not assumptions of the desired
risk conclusion. The two rate-definition equalities check spelling
and normalization only and are classified separately from substantive
proof endpoints.

Conditional hypotheses remain conditional: Lemma 5.1 assumes a positive
bounded-slope affine density path and nonzero target derivative; Lemma 6.1
requires the original sinc/lattice bandwidth. The broader coverage map is
semantic statement inspection plus declaration existence checks, not a claim
that every supplementary row has a separately expanded machine-checked type.
[`coverage.json`](coverage.json) records the numbered correspondence and
distinguishes definition predicates from proof endpoints. Current compilation,
axiom and independent kernel status must be taken from
[`verification.json`](verification.json), not inferred from this source
file's existence. Comparator and its independent kernels cover the two
submission theorems; auxiliary typed checks are compiler-checked and included
in the separate project axiom audit unless a verification report expressly
records a broader kernel replay.
