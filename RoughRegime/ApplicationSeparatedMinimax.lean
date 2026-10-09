module

public import RoughRegime.ApplicationSeparatedEstimator
public import RoughRegime.DeterministicEstimatorRisk
public import RoughRegime.PilotHalfSamples


@[expose] public section
/-! Optimization of the genuine pilot/estimation rule over the literal
 separated-density MAR class, including all measurable randomized rules. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RoughRegime.Applications.SeparatedMAR.PilotSetup
set_option backward.isDefEq.respectTransparency false
variable {A : Model.Parameters} {ζ : ℝ} {hζ : 0<ζ} {hζ1 : ζ<1} {hδ : A.δ≤1/2}

theorem parametricSplit_minimax_bound (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : 1/2≤S.parameters.theta) :
    ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ m : ℕ in atTop,∀ n : ℕ,n≠0→
      Model.minimaxRMSE (n+m) (target A.d) (modelClass A)≤
        ENNReal.ofReal (C/Real.sqrt m+Real.sqrt (S.c⁻¹*Real.exp (-S.c*n))) := by
  obtain ⟨Cv,C,hCv,hC,he⟩ := S.uniform_parametricSplitEstimate_risk hθ
  refine ⟨Cv,C,hCv,hC,?_⟩
  filter_upwards [he] with m hm
  intro n hn
  apply Model.minimaxRMSE_le_dataEstimator (n+m) (target A.d) (modelClass A)
    (S.parametricSplitEstimate Cv n m) (S.parametricSplitEstimate_measurable Cv n m)
  intro P hP
  obtain ⟨W⟩ := hP
  exact hm n hn P W

theorem subcriticalSplit_minimax_bound (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : S.parameters.theta<1/2) :
    ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ m : ℕ in atTop,∀ n : ℕ,n≠0→
      Model.minimaxRMSE (n+m) (target A.d) (modelClass A)≤
        ENNReal.ofReal (C*UpperSubcritical.rate m S.parameters.theta
          (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu+
            Real.sqrt (S.c⁻¹*Real.exp (-S.c*n))) := by
  obtain ⟨Cv,C,hCv,hC,he⟩ := S.uniform_subcriticalSplitEstimate_risk hθ
  refine ⟨Cv,C,hCv,hC,?_⟩
  filter_upwards [he] with m hm
  intro n hn
  apply Model.minimaxRMSE_le_dataEstimator (n+m) (target A.d) (modelClass A)
    (S.subcriticalSplitEstimate Cv n m) (S.subcriticalSplitEstimate_measurable Cv n m)
  intro P hP
  obtain ⟨W⟩ := hP
  exact hm n hn P W

theorem parametricHalf_minimax_bound (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : 1/2≤S.parameters.theta) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      Model.minimaxRMSE n (target A.d) (modelClass A)≤
        ENNReal.ofReal (C/Real.sqrt (n-n/2 : ℕ)+Real.sqrt (S.c⁻¹*Real.exp (-S.c*(n/2 : ℕ)))) := by
  obtain ⟨Cv,C,_hCv,hC,he⟩ := S.parametricSplit_minimax_bound hθ
  refine ⟨C,hC,?_⟩
  filter_upwards [estimationHalf_tendsto.eventually he,pilotHalf_tendsto.eventually (eventually_gt_atTop 0)]
    with n hn hp
  have hh := hn (n/2) (by omega)
  simpa only [halfSample_sum] using hh

theorem subcriticalHalf_minimax_bound (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : S.parameters.theta<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      Model.minimaxRMSE n (target A.d) (modelClass A)≤
        ENNReal.ofReal (C*UpperSubcritical.rate (n-n/2 : ℕ) S.parameters.theta
          (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu+
            Real.sqrt (S.c⁻¹*Real.exp (-S.c*(n/2 : ℕ)))) := by
  obtain ⟨Cv,C,_hCv,hC,he⟩ := S.subcriticalSplit_minimax_bound hθ
  refine ⟨C,hC,?_⟩
  filter_upwards [estimationHalf_tendsto.eventually he,pilotHalf_tendsto.eventually (eventually_gt_atTop 0)]
    with n hn hp
  have hh := hn (n/2) (by omega)
  simpa only [halfSample_sum] using hh

end RoughRegime.Applications.SeparatedMAR.PilotSetup
