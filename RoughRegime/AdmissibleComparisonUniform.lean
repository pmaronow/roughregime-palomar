module

public import RoughRegime.AdmissiblePhaseComparison


@[expose] public section
/-! One physical comparison constant for every admissible normalization
between the fixed density bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair

 theorem comparisonStar_continuousOn (lo hi C0 scoreBound : ℝ) (hlo : 0<lo) :
    ContinuousOn (fun p:ℝ=>comparisonStar lo hi p C0 scoreBound) (Icc lo hi) := by
  unfold comparisonStar physicalComparisonConstant comparisonConstant normalizedBound rawBound
  intro p hp
  have hp0 : 0<p := hlo.trans_le hp.1
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

 theorem exists_uniform_comparisonStar (lo hi C0 scoreBound : ℝ) (hlo : 0<lo) :
    ∃Cstar:ℝ,1≤Cstar ∧ ∀p∈Icc lo hi,comparisonStar lo hi p C0 scoreBound≤Cstar := by
  obtain ⟨C,hC⟩:=isCompact_Icc.exists_bound_of_continuousOn
    (comparisonStar_continuousOn lo hi C0 scoreBound hlo)
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro p hp
  have he : |comparisonStar lo hi p C0 scoreBound|≤C := by simpa only [Real.norm_eq_abs] using hC p hp
  exact (le_abs_self _).trans (he.trans (le_max_right _ _))

 theorem mass_mem_density_bounds {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {lo hi barp C0 : ℝ}
    (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (q : H×ℝ) (hlo : 0<lo) (hhi : 0≤hi) : barp∈Icc lo hi := by
  have hm : Measurable (A.field.designDensity barp q) :=
    A.designDensity_measurable.comp (measurable_const.prodMk measurable_id)
  have hb : ∀x,|A.field.designDensity barp q x|≤hi := by
    intro x
    rw [abs_of_nonneg ((hlo.trans_le (A.densityBounds q x).1).le)]
    exact (A.densityBounds q x).2
  have hiF : Integrable (A.field.designDensity barp q) μ :=
    (integrable_const hi).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs,abs_of_nonneg hhi] using hb x))
  constructor
  · calc
      lo=∫_x,lo ∂μ := by simp
      _≤∫x,A.field.designDensity barp q x ∂μ := integral_mono
        (integrable_const lo) hiF
        (fun x=>(A.densityBounds q x).1)
      _=barp := A.constantMass q
  · calc
      barp=∫x,A.field.designDensity barp q x ∂μ := (A.constantMass q).symm
      _≤∫_x,hi ∂μ := integral_mono hiF
        (integrable_const hi) (fun x=>(A.densityBounds q x).2)
      _=hi := by simp

end RoughRegime.PoissonMeasure.AdmissiblePhasePair

namespace RoughRegime.LatticePriors

 theorem canonicalPoissonMajorant_mono_constant {C D CG CE R Λ Au Av : ℝ} (M : ℕ)
    (hC : 0≤C) (hCD : C≤D) (hCG : 0≤CG) (hΛ : 0≤Λ) (hR : 0<R) :
    canonicalPoissonMajorant C CG CE R Λ Au Av M≤
      canonicalPoissonMajorant D CG CE R Λ Au Av M := by
  unfold canonicalPoissonMajorant
  have hD : 0≤D := hC.trans hCD
  gcongr <;> positivity

end RoughRegime.LatticePriors
