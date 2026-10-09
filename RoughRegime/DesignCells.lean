module

public import RoughRegime.DesignHilbert
public import RoughRegime.DyadicParentSpaces


@[expose] public section
/-! Genuine weighted dyadic cells and Taylor approximations from ModelWitness. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
variable {A : Parameters} {Z : Type*} [MeasurableSpace Z]
  {F : Observables Z A} {P : ProbabilityMeasure (Observation A Z)}

def ModelWitness.designDensity (W : ModelWitness A F P) : Covariate A.d → ℝ := fun x => W.w x * W.p x

theorem ModelWitness.designDensity_measurable (W : ModelWitness A F P) :
    Measurable W.designDensity := W.measurableW.mul W.measurableP

theorem ModelWitness.dyadic_density_bounds (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),
      A.gminus ≤ W.designDensity x ∧ W.designDensity x ≤ A.gplus := by
  rw [dyadicRectangle_normalizedVolume (lt_of_lt_of_le Nat.zero_lt_one A.hd) c]
  exact Measure.ae_smul_measure (ae_restrict_of_ae W.densityBounds) _

def ModelWitness.cellDesignMeasure (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    Measure (Covariate A.d) := weightedDesignMeasure (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity

theorem ModelWitness.cellDesignMeasure_finite (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    IsFiniteMeasure (W.cellDesignMeasure c) := by
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  exact weightedDesignMeasure_finite _ _ A.gplus ((W.dyadic_density_bounds c).mono (fun _ hx => hx.2))

theorem ModelWitness.cellDesignMeasure_ac (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    W.cellDesignMeasure c ≪ rectangleVolume (dyadicOrigin c) (dyadicSides c) := weightedDesignMeasure_ac _ _

theorem ModelWitness.cellDesign_ae_rectangle (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j) :
    ∀ᵐ x ∂W.cellDesignMeasure c, x ∈ dyadicRectangle c := by
  exact (W.cellDesignMeasure_ac c).ae_le ((ae_rectangleVolume_mem (dyadicOrigin c) (dyadicSides c)).mono
    (fun x hx => by rwa [dyadicRectangle_eq_rectangle]))

theorem ModelWitness.holder_memLp_cell (W : ModelWitness A F P) {j : ℕ} (c : DyadicCell A.d j)
    (f : Covariate A.d → ℝ) (hf : Measurable f) (t : ℝ) (hh : f ∈ holderBall t A.H) :
    MemLp f 2 (W.cellDesignMeasure c) := by
  haveI := W.cellDesignMeasure_finite c
  apply MemLp.of_bound hf.aestronglyMeasurable A.H
  filter_upwards [W.cellDesign_ae_rectangle c] with x hx
  rw [Real.norm_eq_abs]
  exact holderNorm_bounds_values f t A.H A.hH.le hh x (dyadicRectangle_subset_cube c hx)

theorem uniform_model_cell_approximation (A : Parameters) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) [MeasurableSpace Z] (F : Observables Z A)
      (P : ProbabilityMeasure (Observation A Z)) (W : ModelWitness A F P)
      (j : ℕ) (c : DyadicCell A.d j) (f : Covariate A.d → ℝ)
      (hf : Measurable f) (hh : f ∈ holderBall t A.H),
      let q := holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)
      ∃ hq : MemLp (polynomialEvaluation q) 2 (W.cellDesignMeasure c),
        q.totalDegree ≤ holderOrder t ∧
        ‖(W.holder_memLp_cell c f hf t hh).toLp f - hq.toLp (polynomialEvaluation q)‖ ≤
          C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ t := by
  obtain ⟨C, hC, hb⟩ := dyadic_holder_polynomial_error (lt_of_lt_of_le Nat.zero_lt_one A.hd) t A.H A.hH.le
  refine ⟨Real.sqrt A.gplus * C, mul_pos (Real.sqrt_pos.mpr (A.hgminus.trans A.hgplus)) hC, ?_⟩
  intro Z _ F P W j c f hf hh
  dsimp only
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  haveI := W.cellDesignMeasure_finite c
  let q := holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)
  let E : ℝ := C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ t
  have hE : 0 ≤ E := by unfold E; positivity
  have he : ∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),
      |f x - polynomialEvaluation q x| ≤ E := by
    filter_upwards [ae_rectangleVolume_mem (dyadicOrigin c) (dyadicSides c)] with x hx
    exact hb j c f hh x (by rwa [dyadicRectangle_eq_rectangle])
  have hq : MemLp (polynomialEvaluation q) 2 (W.cellDesignMeasure c) := by
    apply MemLp.of_bound (polynomialEvaluation_continuous q).aestronglyMeasurable (A.H + E)
    filter_upwards [(W.cellDesignMeasure_ac c).ae_le he, W.cellDesign_ae_rectangle c] with x hx hr
    rw [Real.norm_eq_abs]
    have hval := holderNorm_bounds_values f t A.H A.hH.le hh x (dyadicRectangle_subset_cube c hr)
    calc
      _ ≤ |f x| + |f x - polynomialEvaluation q x| := by
        calc
          _ = |f x + (polynomialEvaluation q x - f x)| := by congr 1; ring
          _ ≤ |f x| + |polynomialEvaluation q x - f x| := by
            simpa only [Real.norm_eq_abs] using norm_add_le (f x) (polynomialEvaluation q x - f x)
          _ = _ := by rw [abs_sub_comm]
      _ ≤ _ := add_le_add hval hx
  refine ⟨hq, holderTaylorPolynomial_degree _ _ _, ?_⟩
  have hn := weightedLp_approximation (rectangleVolume (dyadicOrigin c) (dyadicSides c)) W.designDensity
    A.gplus (A.hgminus.trans A.hgplus).le ((W.dyadic_density_bounds c).mono (fun _ hx => hx.2))
    f (polynomialEvaluation q) E hE he (W.holder_memLp_cell c f hf t hh) hq
  exact hn.trans_eq (by dsimp only [E]; ring)

theorem ModelWitness.actual_holder_cell_approximation (W : ModelWitness A F P) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (c : DyadicCell A.d j) (f : Covariate A.d → ℝ)
      (hf : Measurable f) (hh : f ∈ holderBall t A.H),
      let q := holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)
      ∃ hq : MemLp (polynomialEvaluation q) 2 (W.cellDesignMeasure c),
        q.totalDegree ≤ holderOrder t ∧
        ‖(W.holder_memLp_cell c f hf t hh).toLp f - hq.toLp (polynomialEvaluation q)‖ ≤
          C * ((2 : ℝ) ^ (-(j : ℝ) / A.d)) ^ t := by
  obtain ⟨C, hC, hb⟩ := uniform_model_cell_approximation A t
  exact ⟨C, hC, hb Z F P W⟩

end RoughRegime.Model
