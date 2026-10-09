module

public import RoughRegime.ApplicationTreatmentUpper


@[expose] public section
/-! The two-arm restrictions imply the stated bounds on the actual covariate density.
The witnesses may initially use different density and propensity versions. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.MAR

theorem arm_density_versions_eq (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (W0 : ArmWitness A false P)
    (W1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    W0.p =ᵐ[Model.cubeVolume A.d] W1.p := by
  have he := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.measurable_ofReal.comp W0.measurableP).aemeasurable
    (ENNReal.measurable_ofReal.comp W1.measurableP).aemeasurable).mp
      (W0.marginal.symm.trans W1.marginal)
  filter_upwards [he, W0.nonnegativeP, W1.nonnegativeP] with x hx h0 h1
  have ht := congrArg ENNReal.toReal hx
  dsimp only [Function.comp_apply] at ht
  simpa only [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1] using ht

theorem ArmWitness.density_positive (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (W : ArmWitness A j P) : ∀ᵐ x ∂Model.cubeVolume A.d, 0 < W.p x := by
  filter_upwards [W.nonnegativeP, W.densityBounds] with x hp hb
  have hn : W.p x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hb
    linarith [A.hgminus, hb.1]
  exact lt_of_le_of_ne hp (Ne.symm hn)

theorem arm_propensities_sum_one (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (W0 : ArmWitness A false P)
    (W1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    ∀ᵐ x ∂Model.cubeVolume A.d, W0.w x + W1.w x = 1 := by
  let μ : Measure (Model.Covariate A.d × TreatmentResponse) := P
  have hm : Model.covariateInformation A TreatmentResponse ≤
      (inferInstance : MeasurableSpace (Model.Covariate A.d × TreatmentResponse)) :=
    measurable_fst.comap_le
  have hs : (armIndicator false ∘ Prod.snd : Model.Covariate A.d × TreatmentResponse → ℝ) +
      armIndicator true ∘ Prod.snd = fun _ => 1 := by
    funext o
    dsimp only [Pi.add_apply, Function.comp_apply]
    rw [add_comm, armIndicator_partition]
  have hc := condExp_add (armIndicator_integrable A.d false P)
    (armIndicator_integrable A.d true P) (Model.covariateInformation A TreatmentResponse)
  rw [hs, condExp_const (μ := μ) hm (1 : ℝ)] at hc
  have ho : ∀ᵐ o ∂μ, W0.w o.1 + W1.w o.1 = 1 := by
    filter_upwards [hc, W0.momentD, W1.momentD] with o he h0 h1
    change 1 = μ[armIndicator false ∘ Prod.snd | Model.covariateInformation A TreatmentResponse] o +
      μ[armIndicator true ∘ Prod.snd | Model.covariateInformation A TreatmentResponse] o at he
    change μ[armIndicator false ∘ Prod.snd | Model.covariateInformation A TreatmentResponse] o = W0.w o.1 at h0
    change μ[armIndicator true ∘ Prod.snd | Model.covariateInformation A TreatmentResponse] o = W1.w o.1 at h1
    rw [h0, h1] at he
    exact he.symm
  have hmap : ∀ᵐ x ∂μ.map Prod.fst, W0.w x + W1.w x = 1 :=
    (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_eq_fun (W0.measurableW.add W1.measurableW) measurable_const)).mpr ho
  change ∀ᵐ x ∂(P : Measure (Model.Covariate A.d × TreatmentResponse)).map Prod.fst,
    W0.w x + W1.w x = 1 at hmap
  rw [W0.marginal, ae_withDensity_iff
    (f := fun x => ENNReal.ofReal (W0.p x))
    (ENNReal.measurable_ofReal.comp W0.measurableP)] at hmap
  filter_upwards [hmap, W0.density_positive A false P] with x hx hp
  exact hx (ENNReal.ofReal_ne_zero_iff.mpr hp)

theorem two_arm_density_bounds (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (W0 : ArmWitness A false P)
    (W1 : ArmWitness (parametersWithBeta A β1 hβ1) true P) :
    ∀ᵐ x ∂Model.cubeVolume A.d,
      2 * A.gminus ≤ W0.p x ∧ W0.p x ≤ 2 * A.gplus := by
  filter_upwards [W0.densityBounds, W1.densityBounds,
    arm_density_versions_eq A β1 hβ1 P W0 W1,
    arm_propensities_sum_one A β1 hβ1 P W0 W1] with x h0 h1 hp hw
  change A.gminus ≤ W1.w x * W1.p x ∧ W1.w x * W1.p x ≤ A.gplus at h1
  rw [← hp] at h1
  have hs : W0.w x * W0.p x + W1.w x * W0.p x = W0.p x := by
    rw [← add_mul, hw, one_mul]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

theorem treatmentClass_density_bounds (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1)
    (P : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse))
    (hP : P ∈ treatmentClass A β1 hβ1) :
    ∃ p : Model.Covariate A.d → ℝ, Measurable p ∧
      0 ≤ᵐ[Model.cubeVolume A.d] p ∧
      (P : Measure (Model.Covariate A.d × TreatmentResponse)).map Prod.fst =
        (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∀ᵐ x ∂Model.cubeVolume A.d, 2 * A.gminus ≤ p x ∧ p x ≤ 2 * A.gplus := by
  rcases hP with ⟨⟨W0⟩, ⟨W1⟩⟩
  exact ⟨W0.p, W0.measurableP, W0.nonnegativeP, W0.marginal,
    two_arm_density_bounds A β1 hβ1 P W0 W1⟩

theorem eta_treatment_density_bounds (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1 ≤ d)
    (hα : 0 < α) (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hH : 0 < H)
    (hη : 0 < η) (hηquarter : η < 1/4)
    (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse))
    (hP : P ∈ etaTreatmentClass d α β0 β1 H η hd hα hβ0 hβ1 hH hη hηquarter) :
    ∃ p : Model.Covariate d → ℝ, Measurable p ∧
      0 ≤ᵐ[Model.cubeVolume d] p ∧
      (P : Measure (Model.Covariate d × TreatmentResponse)).map Prod.fst =
        (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∀ᵐ x ∂Model.cubeVolume d, 2 * η ≤ p x ∧ p x ≤ 2 * η⁻¹ := by
  exact treatmentClass_density_bounds
    (etaParameters d α β0 H η hd hα hβ0 hH hη hηquarter) β1 hβ1 P hP

end RoughRegime.Applications.MAR
