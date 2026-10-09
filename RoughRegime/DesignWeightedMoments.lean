module

public import RoughRegime.DesignReferenceMatrices


@[expose] public section
/-! Actual weighted Hilbert moments of the actual model responses. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.Model
open RoughRegime.HilbertGram

 theorem ModelWitness.weightedChildBasis_moments {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) (k : ℕ)
    (f : Covariate A.d → ℝ) (hf : Measurable f) (t : ℝ) (ht : f ∈ holderBall t A.H) :
    moments (W.weightedChildBasis k c) ((W.holder_memLp_cell c f hf t ht).toLp f) =
      designMoment (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity
        (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) f := by
  funext i
  change inner ℝ _ _ = _
  rw [L2.inner_def]
  calc
    _ = ∫ x, dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c i x * f x
        ∂W.cellDesignMeasure c := by
      apply integral_congr_ae
      filter_upwards [W.weightedChildBasis_ae k c i,
        (W.holder_memLp_cell c f hf t ht).coeFn_toLp] with x hzx hfx
      simp [hzx, hfx, mul_comm]
    _ = ∫ x, W.designDensity x *
        (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c i x * f x)
        ∂rectangleVolume (dyadicOrigin c) (dyadicSides c) :=
      weightedDesignMeasure_integral _ _ W.designDensity_measurable
        ((W.dyadic_density_bounds c).mono (fun _ hx => A.hgminus.le.trans hx.1)) _
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)

lemma ModelWitness.dyadicDesignMean_gram {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) (k : ℕ) :
    designMatrix (dyadicDesignMean A F P k c) = Matrix.gram ℝ (W.weightedChildBasis k c) := by
  rw [dyadicDesignMean_eq_population A F P W, packedDesignPopulation_gram, W.weightedChildBasis_gram]
  rfl

lemma ModelWitness.dyadicDesignMean_first {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) (k : ℕ) :
    designFirst (dyadicDesignMean A F P k c) =
      moments (W.weightedChildBasis k c) ((W.holder_memLp_cell c W.a W.measurableA A.α W.smoothA).toLp W.a) := by
  rw [dyadicDesignMean_eq_population A F P W, packedDesignPopulation_first, W.weightedChildBasis_moments c k W.a W.measurableA A.α W.smoothA]
  rfl

lemma ModelWitness.dyadicDesignMean_second {A : Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}
    (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) (k : ℕ) :
    designSecond (dyadicDesignMean A F P k c) =
      moments (W.weightedChildBasis k c) ((W.holder_memLp_cell c W.b W.measurableB A.β W.smoothB).toLp W.b) := by
  rw [dyadicDesignMean_eq_population A F P W, packedDesignPopulation_second, W.weightedChildBasis_moments c k W.b W.measurableB A.β W.smoothB]
  rfl

end RoughRegime.Model
