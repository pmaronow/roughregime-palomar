module

public import RoughRegime.ModelUpper


@[expose] public section
/-! A deterministic measurable iid rule is an allowed randomized estimator.
 Its independent auxiliary seed leaves the actual L2 risk unchanged. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Model

def dataEstimator {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : (Fin n→Ω)→ℝ) (hE : Measurable E) : Estimator Ω n :=
  ⟨E∘Prod.fst,hE.comp measurable_fst⟩

theorem dataEstimator_eLpNorm_error {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (E : (Fin n→Ω)→ℝ) (hE : Measurable E) (P : ProbabilityMeasure Ω) (t : ℝ) :
    eLpNorm (fun q=>(dataEstimator n E hE).val q-t) 2 (randomizedExperiment n P)=
      eLpNorm (fun xs=>E xs-t) 2 (Measure.pi (fun _ : Fin n=>(P:Measure _))) := by
  change eLpNorm ((fun xs=>E xs-t)∘Prod.fst) 2
    ((Measure.pi (fun _ : Fin n=>(P:Measure _))).prod KernelSeedBridge.seedLaw)=_
  exact eLpNorm_comp_measurePreserving (hE.sub measurable_const).aestronglyMeasurable measurePreserving_fst

theorem minimaxRMSE_le_dataEstimator {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (E : (Fin n→Ω)→ℝ) (hE : Measurable E) (r : ℝ≥0∞)
    (hr : ∀ P ∈ C,eLpNorm (fun xs=>E xs-T P) 2
      (Measure.pi (fun _ : Fin n=>(P:Measure _)))≤r) :
    minimaxRMSE n T C≤r := by
  apply minimaxRMSE_le_fixed_estimator n T C (dataEstimator n E hE) r
  intro P hP
  rw [dataEstimator_eLpNorm_error]
  exact hr P hP

end RoughRegime.Model
