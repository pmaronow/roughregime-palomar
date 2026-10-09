module

public import RoughRegime
public import Solution

@[expose] public section

/-!
# Explicit target checks for selected numbered paper claims

This module imports proved declarations and Solution, never Challenge. Each
check states its mathematical target explicitly and supplies the existing
proof at that type. It does not infer correctness from declaration names.

Mechanically checked scope: Theorem 2.3(a,b); rate formulas and their exact
logarithmic consequence; Lemma 4.1; Lemma 4.6; Lemma 5.1; Lemma 6.1; and the
rough/parametric risk conclusions of Proposition 7.1. This is a selected
subset of the broader semantic correspondence inventory.

Lemma 5.1 remains conditional on its density path and derivative hypotheses.
Proposition 7.1 uses the explicit finite-response/supplied-score StandingData
inputs. Its smooth-family/membership package and selected-hard-law predicates
are concrete definitions, not premises asserting the desired risk bound.
The exact target expression below retains those predicates and the original
constant and target-offset quantifier order.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff

namespace RoughRegimeVerification
universe u
open RoughRegime

/-- Theorem 2.3(a): expanded uniform constants and both rate regimes. -/
theorem theorem_2_3_a (A : Model.Parameters) (L MW : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ (Z : Type u) (mZ : MeasurableSpace Z) (F : @Model.Observables Z mZ A),
        |F.lam| = L → (∀ z, |F.W z| ≤ MW) →
        ∀ n : ℕ, n0 ≤ n → (Model.modelClass A F).Nonempty →
          (1 / 2 ≤ A.theta →
            Model.minimaxRMSE n (Model.target A F) (Model.modelClass A F) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
          (0 < A.theta ∧ A.theta < 1 / 2 →
            Model.minimaxRMSE n (Model.target A F) (Model.modelClass A F) ≤
              ENNReal.ofReal (C * Rates.subcriticalScale n A.theta
                (Rates.tau A.gminus A.gplus) *
                (Real.log n) ^ ((A.nu : ℝ) / 2 + 1 / 4))) := by
  exact RoughRegimeSubmission.mainUpper.{u} A L MW

/-- Theorem 2.3(b): expanded intermediate-class, RMSE and quarter-tail target. -/
theorem theorem_2_3_b (A : Model.Parameters) {Z : Type u} [MeasurableSpace Z]
    (F : Model.Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ) :
    Model.Nondegenerate A F π → 0 < r →
      ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
        ∀ C' : Set (ProbabilityMeasure (Model.Observation A Z)),
          Model.localClass A F π r ⊆ C' → C' ⊆ Model.modelClass A F →
          ∀ n : ℕ, n0 ≤ n →
            (1 / 2 ≤ A.theta →
              ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
                Model.minimaxRMSE n (Model.target A F) C') ∧
            (0 < A.theta ∧ A.theta < 1 / 2 →
              let a := Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)
              ENNReal.ofReal (c * a * Real.log n) ≤
                Model.minimaxRMSE n (Model.target A F) C' ∧
              (1 / 4 : ℝ≥0∞) ≤
                Model.minimaxTail n (Model.target A F) C' (2 * c * a * Real.log n)) := by
  exact RoughRegimeSubmission.mainLower A F π r

/-- Definition check for the paper's reciprocal interval ratio. -/
theorem rho_formula (lo hi : ℝ) :
    Rates.rho lo hi =
      (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo) := rfl

/-- Definition check for the paper's common subcritical scale. -/
theorem scale_formula (n θ τ : ℝ) :
    Rates.subcriticalScale n θ τ = n ^ (-θ) * (Real.log n) ^ (θ / 2) *
      Real.exp (-(2 * Real.sqrt (θ * (1 - 2 * θ) * τ)) *
        Real.sqrt (Real.log n)) := rfl

/-- Exact logarithmic rate identity; no asymptotic risk premise is assumed. -/
theorem scale_logarithm (n θ τ : ℝ) (hn : 1 < n) :
    Real.log (Rates.subcriticalScale n θ τ) =
      -θ * Real.log n + θ / 2 * Real.log (Real.log n) -
        (2 * Real.sqrt (θ * (1 - 2 * θ) * τ)) * Real.sqrt (Real.log n) := by
  exact Rates.log_scale n θ τ hn

/-- Lemma 4.1: explicit positive-integer Chebyshev series and rational target. -/
theorem lemma_4_1 (lo hi x : ℝ) (z : ℂ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Icc lo hi) (hz : ‖z‖ < (Upper.intervalRho lo hi)⁻¹) :
    (1 + 2 * ∑' k : ℕ,
      (-(Upper.intervalRho lo hi : ℂ) * z) ^ (k + 1) *
        (((Polynomial.Chebyshev.T ℝ (k + 1 : ℕ)).eval
          ((x - (hi + lo) / 2) / ((hi - lo) / 2)) : ℝ) : ℂ)) =
      (1 - (Upper.intervalRho lo hi : ℂ) ^ 2 * z ^ 2) /
      (1 + 2 * (Upper.intervalRho lo hi : ℂ) * z *
        (((x - (hi + lo) / 2) / ((hi - lo) / 2) : ℝ) : ℂ) +
        (Upper.intervalRho lo hi : ℂ) ^ 2 * z ^ 2) := by
  exact Upper.reciprocal_expansion lo hi x z hlo hlt hx hz

/-- Lemma 4.1 at z=1, including its exact geometric-mean normalization. -/
theorem lemma_4_1_at_one (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (hx : x ∈ Icc lo hi) :
    Upper.reciprocalSeries lo hi 1 x = (Real.sqrt (lo * hi) : ℂ) / (x : ℂ) := by
  exact Upper.reciprocal_expansion_at_one lo hi x hlo hlt hx

/-- Lemma 4.6 with the literal paper constant and separation condition. -/
theorem lemma_4_6 (S : Finset ℝ) (θ τ B X : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hX : 0 < X)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ X)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.log 2 ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-θ * x - τ * B / x)) ≤
      (2 + Real.sqrt (Real.pi * X / θ) / Real.log 2) *
        Real.exp (-2 * Real.sqrt (θ * τ * B)) := by
  exact Window.window_sum S θ τ B X hθ hτ hB hX hS hsep

/-- Lemma 5.1's literal affine-density-path hypotheses and randomized conclusion. -/
theorem lemma_5_1 {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : ℝ → GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ)
    (T : ProbabilityMeasure Ω → ℝ) (C : Set (ProbabilityMeasure Ω))
    (l r t₀ D cf Cf : ℝ) (ht₀ : t₀ ∈ Ioo l r)
    (hF : HasDerivAt (fun t => T (P t).probabilityMeasure) D t₀)
    (hD : D ≠ 0) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hdens : ∀ t ∈ Ioo l r, (P t).density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hpos : ∀ t ∈ Ioo l r, ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hscore : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf)
    (hclass : ∀ t ∈ Ioo l r, (P t).probabilityMeasure ∈ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C) ∧
      ((1 / 4 : ℝ≥0∞) ≤ Model.minimaxTail n T C (2 * c * (n : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  exact LowerMeasure.parametric_path_minimax_bound P f₀ f₁ T C l r t₀ D cf Cf
    ht₀ hF hD hcf hCf hdens hpos hscore hclass

/-- Lemma 6.1: original lattice normalization, deficit and support conclusions. -/
theorem lemma_6_1 (Q M : ℕ) (η lam : ℝ)
    (hQ : 2 ≤ Q) (hM : 2 ≤ M) (hη : 0 < η) (hlam : 1 ≤ lam)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    (∑' z : ℤ, LatticeFourier.latticeWeight Q M η z) = 1 ∧
    (∀ x : ℝ, 0 ≤ Lattice.gate Q (lam * η) x ∧
      Lattice.gate Q (lam * η) x ≤ 1) ∧
    (1 - (∑' z : ℤ, LatticeFourier.latticeWeight Q M η z *
      Lattice.gate Q (lam * η) (LatticeFourier.latticeStep M * z)) ≤
        (Q : ℝ) * LatticeFourier.sincSecondMoment Q / (3 * lam ^ 2)) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ (2 * Q : ℕ) - 2 → ∀ x : ℝ,
      Lattice.gate Q (lam * η) x * |x| ^ r ≤ (lam * η) ^ r) ∧
    (∀ w : ℝ, ‖LatticeFourier.latticeCharacteristic Q M η lam w‖ ≤ 1 ∧
      ((¬ ∃ l : ℤ, |w - (l : ℝ) * M| ≤ 6 * Q / η) →
        LatticeFourier.latticeCharacteristic Q M η lam w = 0)) := by
  exact LatticeFourier.gated_lattice_laws Q M η lam hQ hM hη hlam hband

open LocalLower LatticePriors Localization

/-- Proposition 7.1(a): family and constants precede every class/target/offset;
matching is required on the selected hard-law image only. -/
theorem proposition_7_1_rough {Z : Type u} [MeasurableSpace Z]
    {O : LocalLower.ResponseData Z} {π : ProbabilityMeasure Z}
    (S : LocalLower.StandingData O π) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {ι : Type*} [Fintype ι] (e : ι → SourceExtraCondition S.alpha S.beta)
    (hbase : ∀ i, (e i).condition.baselineAdmissible S.rminus S.rplus)
    (hrough : (S.parameters.withDimension S.dimensionPred).theta < 1 / 2) :
    ∃ F : S.SourceFamily, F.Localized ∧ F.scores = S.scores ∧
      F.rminus = S.rminus ∧ F.rplus = S.rplus ∧
      F.epsilonU + F.epsilonV ≤ epsilon ∧ S.SelectedExtras F e ∧
      ∃ c0 c : ℝ, 0 < c ∧
        ∀ (Cn : ℕ → Set (ProbabilityMeasure
          (Model.Observation (S.parameters.withDimension S.dimensionPred) Z)))
          (T : ProbabilityMeasure
            (Model.Observation (S.parameters.withDimension S.dimensionPred) Z) → ℝ)
          (tstar : ℝ),
          F.SelectedClassSequenceClaim (S.parameters.withDimension S.dimensionPred).theta
            (Rates.tau S.rminus S.rplus) c0 Cn →
          F.SelectedTargetOffsetClaim (S.parameters.withDimension S.dimensionPred).theta
            (Rates.tau S.rminus S.rplus) c0 T tstar →
          ∀ᶠ n : ℕ in atTop,
            ENNReal.ofReal (Real.sqrt (3 / 8) * c * Rates.subcriticalScale n
              (S.parameters.withDimension S.dimensionPred).theta
              (Rates.tau S.rminus S.rplus) * Real.log n) ≤
                Model.minimaxRMSE n T (Cn n) ∧
            (3 / 8 : ℝ≥0∞) ≤ Model.minimaxTail n T (Cn n)
              (c * Rates.subcriticalScale n (S.parameters.withDimension S.dimensionPred).theta
                (Rates.tau S.rminus S.rplus) * Real.log n) := by
  exact S.proposition15_rough epsilon hepsilon e hbase hrough

/-- Proposition 7.1(b): literal supplied-score path near zero and uniform
positive constant before all containing classes, targets and offsets. -/
theorem proposition_7_1_parametric {Z : Type u} [MeasurableSpace Z]
    {O : LocalLower.ResponseData Z} {π : ProbabilityMeasure Z}
    (S : LocalLower.StandingData O π) :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ S.parametricRadius,
      let P := fun t => AffineResponseLower.withDesign (π : Measure Z)
        (Model.cubeVolume (S.dimensionPred + 1))
        (AffineResponseLower.responseDensityLaw (π : Measure Z) S.scores.su S.scores.sv
          S.scores.measurableU S.scores.measurableV u S.parametricRadius S.scores.C
          S.parametricRadius_pos.le S.scores.nonnegativeC hu S.parametricRadius_small
          S.scores.boundU S.scores.boundV S.scores.meanU S.scores.meanV t)
      ∃ c : ℝ, 0 < c ∧
        ∀ (T : ProbabilityMeasure (Model.Covariate (S.dimensionPred + 1) × Z) → ℝ)
          (C : Set (ProbabilityMeasure (Model.Covariate (S.dimensionPred + 1) × Z)))
          (tstar : ℝ),
          (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
          ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
            fun t => Model.target (S.parameters.withDimension S.dimensionPred)
              S.observables (P t).probabilityMeasure + tstar) →
          ∀ᶠ n : ℕ in atTop,
            ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
              Model.minimaxRMSE n T C := by
  exact S.proposition15_parametric

end RoughRegimeVerification
