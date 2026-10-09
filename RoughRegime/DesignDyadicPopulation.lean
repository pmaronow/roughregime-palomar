module

public import RoughRegime.DesignPolynomial
public import RoughRegime.DyadicDesign


@[expose] public section
/-! The true packed observable mean belongs to one fixed bounded source domain
for every model, every dyadic level, and every cell. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.Model
open RoughRegime.ProjectionFrame

 def dyadicDesignMean (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (k : ℕ)
    {j : ℕ} (c : DyadicCell A.d j) :
    Fin (designMomentDimension (dyadicChildDimension A.d k)) → ℝ := fun i =>
  (∫ o, dyadicDesignStatistic A F k c o ∂(P : Measure (Observation A Z)))
    ((designMomentCoordinate (dyadicChildDimension A.d k)).symm i)

lemma dyadicDesignMean_eq_population (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    dyadicDesignMean A F P k c =
      packedDesignPopulation A (rectangleVolume (dyadicOrigin c) (dyadicSides c))
        (fun x => W.w x * W.p x) W.a W.b
        (dyadicFinChildBasisFunction (lt_of_lt_of_le Nat.zero_lt_one A.hd) k c) := by
  unfold dyadicDesignMean
  rw [dyadicDesignStatistic_integral A F P W]
  rfl

/-- Membership follows from the model's true density bounds and actual Bessel
moment bounds; it is not a supplied population-set condition. -/
theorem dyadicDesignMean_mem (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
    (k : ℕ) {j : ℕ} (c : DyadicCell A.d j) :
    dyadicDesignMean A F P k c ∈
      designMomentSet (dyadicChildDimension A.d k) A.gminus A.gplus (A.H * A.gplus) := by
  rw [dyadicDesignMean_eq_population A F P W]
  change spectrum ℝ (designMatrix _) ⊆ Set.Icc A.gminus A.gplus ∧
    ‖euclidean (designFirst _)‖ ≤ A.H * A.gplus ∧
    ‖euclidean (designSecond _)‖ ≤ A.H * A.gplus
  rw [packedDesignPopulation_gram, packedDesignPopulation_first, packedDesignPopulation_second]
  refine ⟨dyadicDesign_spectrum A F P W k c, ?_⟩
  exact dyadicDesign_moment_norms A F P W k c

end RoughRegime.Model
