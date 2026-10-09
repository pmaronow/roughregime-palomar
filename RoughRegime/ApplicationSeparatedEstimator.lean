module

public import RoughRegime.ApplicationSeparatedPilot
public import RoughRegime.NormalizedOrientedPilotEstimator
public import RoughRegime.ApplicationMARRange


@[expose] public section
/-! Actual clipped two-block estimators for separated-density MAR. The
 pilot and the estimation block are coordinates of the original iid data. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RoughRegime.Applications.SeparatedMAR.PilotSetup
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {A : Model.Parameters} {ζ : ℝ} {hζ : 0 < ζ} {hζ1 : ζ < 1} {hδ : A.δ ≤ 1/2}

def parametricRawEstimate (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    (Fin n→Model.Covariate A.d×Response)×(Fin m→Model.Covariate A.d×Response)→ℝ :=
  orientedParametricNormalizedEstimate S.parameters (S.pilot n) (S.measurable n)
    (pilotClip A) (pilotClip_pos A) (fun data x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq) Cv m

def subcriticalRawEstimate (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    (Fin n→Model.Covariate A.d×Response)×(Fin m→Model.Covariate A.d×Response)→ℝ :=
  orientedSubcriticalNormalizedEstimate S.parameters (S.pilot n) (S.measurable n)
    (pilotClip A) (pilotClip_pos A) (fun data x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq) Cv m

theorem parametricRawEstimate_measurable (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    Measurable (S.parametricRawEstimate Cv n m) :=
  orientedParametricNormalizedEstimate_measurable S.parameters (S.pilot n) (S.measurable n)
    (pilotClip A) (pilotClip_pos A) (fun data x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq) Cv m

theorem subcriticalRawEstimate_measurable (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    Measurable (S.subcriticalRawEstimate Cv n m) :=
  orientedSubcriticalNormalizedEstimate_measurable S.parameters (S.pilot n) (S.measurable n)
    (pilotClip A) (pilotClip_pos A) (fun data x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq) Cv m

def parametricSplitEstimate (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    (Fin (n+m)→Model.Covariate A.d×Response)→ℝ :=
  clipUnit ∘ S.parametricRawEstimate Cv n m ∘ splitIID n m

def subcriticalSplitEstimate (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    (Fin (n+m)→Model.Covariate A.d×Response)→ℝ :=
  clipUnit ∘ S.subcriticalRawEstimate Cv n m ∘ splitIID n m

theorem parametricSplitEstimate_measurable (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    Measurable (S.parametricSplitEstimate Cv n m) :=
  clipUnit_measurable.comp ((S.parametricRawEstimate_measurable Cv n m).comp (splitIID n m).measurable)

theorem subcriticalSplitEstimate_measurable (S : PilotSetup A ζ hζ hζ1 hδ) (Cv : ℝ) (n m : ℕ) :
    Measurable (S.subcriticalSplitEstimate Cv n m) :=
  clipUnit_measurable.comp ((S.subcriticalRawEstimate_measurable Cv n m).comp (splitIID n m).measurable)

theorem uniform_parametricSplitEstimate_risk (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : 1/2≤S.parameters.theta) :
    ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (n : ℕ), n≠0→∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (_W : Witness A P),
      eLpNorm (fun xs=>S.parametricSplitEstimate Cv n m xs-target A.d P) 2
        (Measure.pi (fun _ : Fin (n+m)=>(P:Measure _)))≤
          ENNReal.ofReal (C/Real.sqrt m+Real.sqrt (S.c⁻¹*Real.exp (-S.c*n))) := by
  obtain ⟨Cv,C,hCv,hC,he⟩ := uniform_orientedParametricNormalizedEstimate_risk S.parameters hθ
  refine ⟨Cv,C,hCv,hC,?_⟩
  filter_upwards [he] with m hm
  intro n hn P W
  apply clipped_conditional_iid_error (P:Measure _) n m (S.parametricRawEstimate Cv n m)
    (S.parametricRawEstimate_measurable Cv n m) {data | S.Good P W n data}
    (S.good_measurable P W n) (target A.d P) (C/Real.sqrt m) (S.c⁻¹*Real.exp (-S.c*n))
    (MAR.observedMean_mem_Icc A.d P) (div_nonneg hC.le (Real.sqrt_nonneg _))
    (mul_nonneg (inv_nonneg.mpr S.hc.le) (Real.exp_pos _).le) (S.bad_probability_bound P W n hn)
  intro data hgood
  have hh := hm P (S.pilot n data) ((S.smooth n data).continuous.measurable)
    (pilotClip A) (pilotClip_pos A) (fun x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq)
    (S.normalizedWitness P W n data hgood)
  rw [S.normalizedWitness_productTarget_eq_target P W n data hgood] at hh
  exact hh

theorem uniform_subcriticalSplitEstimate_risk (S : PilotSetup A ζ hζ hζ1 hδ)
    (hθ : S.parameters.theta<1/2) :
    ∃ Cv C : ℝ,1≤Cv ∧ 0<C ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (n : ℕ), n≠0→∀ (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (_W : Witness A P),
      eLpNorm (fun xs=>S.subcriticalSplitEstimate Cv n m xs-target A.d P) 2
        (Measure.pi (fun _ : Fin (n+m)=>(P:Measure _)))≤
          ENNReal.ofReal (C*UpperSubcritical.rate m S.parameters.theta
            (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu+
              Real.sqrt (S.c⁻¹*Real.exp (-S.c*n))) := by
  obtain ⟨Cv,C,hCv,hC,he⟩ := uniform_orientedSubcriticalNormalizedEstimate_risk S.parameters hθ
  refine ⟨Cv,C,hCv,hC,?_⟩
  filter_upwards [he,eventually_gt_atTop 1] with m hm hm1
  intro n hn P W
  have hr := UpperSubcritical.rate_positive m S.parameters.theta
    (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu (by exact_mod_cast hm1)
  apply clipped_conditional_iid_error (P:Measure _) n m (S.subcriticalRawEstimate Cv n m)
    (S.subcriticalRawEstimate_measurable Cv n m) {data | S.Good P W n data}
    (S.good_measurable P W n) (target A.d P)
    (C*UpperSubcritical.rate m S.parameters.theta (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu)
    (S.c⁻¹*Real.exp (-S.c*n)) (MAR.observedMean_mem_Icc A.d P) (mul_nonneg hC.le hr.le)
    (mul_nonneg (inv_nonneg.mpr S.hc.le) (Real.exp_pos _).le) (S.bad_probability_bound P W n hn)
  intro data hgood
  have hh := hm P (S.pilot n data) ((S.smooth n data).continuous.measurable)
    (pilotClip A) (pilotClip_pos A) (fun x=>(S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq)
    (S.normalizedWitness P W n data hgood)
  rw [S.normalizedWitness_productTarget_eq_target P W n data hgood] at hh
  exact hh

end RoughRegime.Applications.SeparatedMAR.PilotSetup
