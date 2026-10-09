module

public import RoughRegime.Model


@[expose] public section
/-! The genuine conditional-moment target on a product design and response law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications

/-- The response is independent of the design under the actual product probability law. -/
theorem conditional_snd_product {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (η : Measure X) (π : Measure Z) [IsProbabilityMeasure η] [IsProbabilityMeasure π]
    (f : Z → ℝ) (hf : Measurable f) :
    (η.prod π)[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[η.prod π]
      fun _ => ∫ z, f z ∂π := by
  have hs : StronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance]
      (f ∘ Prod.snd : X × Z → ℝ) :=
    hf.stronglyMeasurable.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  have hi : Indep (MeasurableSpace.comap Prod.snd inferInstance)
      (MeasurableSpace.comap Prod.fst inferInstance) (η.prod π) := by
    have hid := (indepFun_prod (μ := η) (ν := π) measurable_id measurable_id).symm
    exact (IndepFun_iff_Indep _ _ _).mp hid
  have he := condExp_indep_eq measurable_snd.comap_le measurable_fst.comap_le hs hi
  simpa only [Function.comp_def, integral_fun_snd, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using he

/-- Formula (8) on an actual product law, without assuming its conditional moments. -/
theorem target_product (A : RoughRegime.Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : RoughRegime.Model.Observables Z A)
    (η : Measure (RoughRegime.Model.Covariate A.d)) (π : Measure Z)
    [IsProbabilityMeasure η] [IsProbabilityMeasure π] :
    RoughRegime.Model.target A F ⟨η.prod π, inferInstance⟩ =
      (∫ z, F.W z ∂π) + F.lam *
        ((∫ z, F.U z ∂π) * (∫ z, F.V z ∂π) / (∫ z, F.D z ∂π)) := by
  have hU := conditional_snd_product η π F.U F.measurableU
  have hV := conditional_snd_product η π F.V F.measurableV
  have hD := conditional_snd_product η π F.D F.measurableD
  have hi : (∫ o, ((η.prod π)[F.U ∘ Prod.snd |
      RoughRegime.Model.covariateInformation A Z]) o *
      ((η.prod π)[F.V ∘ Prod.snd | RoughRegime.Model.covariateInformation A Z]) o /
      ((η.prod π)[F.D ∘ Prod.snd | RoughRegime.Model.covariateInformation A Z]) o ∂η.prod π) =
        (∫ z, F.U z ∂π) * (∫ z, F.V z ∂π) / (∫ z, F.D z ∂π) := by
    calc
      _ = ∫ _o, (∫ z, F.U z ∂π) * (∫ z, F.V z ∂π) / (∫ z, F.D z ∂π) ∂η.prod π := by
        apply integral_congr_ae
        filter_upwards [hU, hV, hD] with o hu hv hd
        rw [hu, hv, hd]
      _ = _ := by simp
  unfold RoughRegime.Model.target
  change (∫ o, F.W o.2 ∂η.prod π) + F.lam *
    (∫ o, ((η.prod π)[F.U ∘ Prod.snd | RoughRegime.Model.covariateInformation A Z]) o *
      ((η.prod π)[F.V ∘ Prod.snd | RoughRegime.Model.covariateInformation A Z]) o /
      ((η.prod π)[F.D ∘ Prod.snd | RoughRegime.Model.covariateInformation A Z]) o ∂η.prod π) = _
  rw [hi, integral_fun_snd]
  simp [measureReal_def]

end RoughRegime.Applications
