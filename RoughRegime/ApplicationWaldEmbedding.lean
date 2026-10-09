module

public import RoughRegime.ApplicationWald
public import RoughRegime.ModelLowerConsequences


@[expose] public section
/-! The actual A=Z deterministic Wald embedding. Its four conditional moments
and treatment-class membership are proved for every admissible input law. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.Wald
set_option maxHeartbeats 1000000

def copyResponse (z : MAR.TreatmentResponse) : MAR.TreatmentResponse := (z.1,MAR.bitOutcome z.1)
def copyMap (d : ℕ) (o : Model.Covariate d × MAR.TreatmentResponse) :
    Model.Covariate d × MAR.TreatmentResponse := (o.1,copyResponse o.2)
def embed (d : ℕ) (o : Model.Covariate d × MAR.TreatmentResponse) : Model.Covariate d × Response :=
  (o.1,(o.2.1,o.2.1,o.2.2))

theorem copyResponse_measurable : Measurable copyResponse :=
  measurable_fst.prodMk (bitOutcome_measurable.comp measurable_fst)
theorem copyMap_measurable (d : ℕ) : Measurable (copyMap d) :=
  measurable_fst.prodMk (copyResponse_measurable.comp measurable_snd)
theorem embed_measurable (d : ℕ) : Measurable (embed d) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))

def copyLaw (A : Model.Parameters) (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) :=
  P.map (copyMap A.d)
def embedLaw (A : Model.Parameters) (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) :=
  P.map (embed A.d)

theorem copy_conditional (d : ℕ) (μ : Measure (Model.Covariate d × MAR.TreatmentResponse))
    [IsProbabilityMeasure μ] (f : MAR.TreatmentResponse → ℝ) (hf : Measurable f)
    (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (fun o => f (copyResponse o.2)) μ)
    (hc : μ[(fun o => f (copyResponse o.2)) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      fun o => g o.1) :
    (μ.map (copyMap d))[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.map (copyMap d)]
      g ∘ Prod.fst := by
  have hinfo : MeasurableSpace.comap (copyMap d) (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d) MAR.TreatmentResponse) inferInstance := by
    rw [MeasurableSpace.comap_comp]
    rfl
  apply Applications.conditional_map μ (copyMap d) (copyMap_measurable d)
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (f ∘ Prod.snd) (g ∘ Prod.fst) (hf.comp measurable_snd)
    (hg.comp (measurable_iff_comap_le.mpr le_rfl)) hfi
  simpa only [hinfo,Function.comp_def,copyMap] using hc

theorem copy_indicator (j : Bool) (z : MAR.TreatmentResponse) :
    MAR.armIndicator j (copyResponse z) = MAR.armIndicator j z := rfl

theorem copy_outcome (j : Bool) (z : MAR.TreatmentResponse) :
    MAR.armOutcome j (copyResponse z) = ConditionalWald.bit j * MAR.armIndicator j z := by
  cases j <;> cases h : z.1 <;> simp [MAR.armOutcome,MAR.armIndicator,copyResponse,
    MAR.bitOutcome,ConditionalWald.bit,h]

def copiedWitness (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (W : MAR.ArmWitness A j P) (hH : 1 ≤ A.H) : MAR.ArmWitness A j (copyLaw A P) where
  p := W.p
  w := W.w
  b _ := ConditionalWald.bit j
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB := measurable_const
  nonnegativeP := W.nonnegativeP
  marginal := by
    change ((P : Measure _).map (copyMap A.d)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (copyMap_measurable A.d)]
    exact W.marginal
  momentD := by
    apply copy_conditional A.d (P : Measure _) _ (MAR.armIndicator_measurable j) W.w W.measurableW
    · apply Integrable.of_mem_Icc 0 1
      · exact ((MAR.armIndicator_measurable j).comp (copyResponse_measurable.comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => MAR.armIndicator_range j (copyResponse o.2))
    · simpa only [copy_indicator,Function.comp_def] using W.momentD
  momentV := by
    apply copy_conditional A.d (P : Measure _) _ (MAR.armOutcome_measurable j)
      (fun x => W.w x * ConditionalWald.bit j) (W.measurableW.mul measurable_const)
    · apply Integrable.of_mem_Icc 0 1
      · exact ((MAR.armOutcome_measurable j).comp (copyResponse_measurable.comp measurable_snd)).aemeasurable
      · exact Filter.Eventually.of_forall (fun o => MAR.armOutcome_range j (copyResponse o.2))
    · have he : (fun o : Model.Covariate A.d × MAR.TreatmentResponse => MAR.armOutcome j (copyResponse o.2)) =
          ConditionalWald.bit j • (MAR.armIndicator j ∘ Prod.snd) := by
        funext o
        exact copy_outcome j o.2
      rw [he]
      filter_upwards [condExp_smul (ConditionalWald.bit j) (MAR.armIndicator j ∘ Prod.snd)
        (m := MeasurableSpace.comap Prod.fst inferInstance),W.momentD] with o hs hd
      rw [hs]
      simp only [Pi.smul_apply,smul_eq_mul,Function.comp_apply,hd]
      ring
  overlap := W.overlap
  smoothInverse := W.smoothInverse
  smoothB := Model.const_mem_holderBall A.hβ (by
    have hb := ConditionalWald.bit_range j
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans hH)
  densityBounds := W.densityBounds

theorem copyLaw_mem (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (hP : P ∈ MAR.treatmentClass A A.β A.hβ) (hH : 1 ≤ A.H) :
    copyLaw A P ∈ MAR.treatmentClass A A.β A.hβ := by
  obtain ⟨⟨h0⟩,⟨h1⟩⟩ := hP
  exact ⟨⟨copiedWitness A false P h0 hH⟩,
    ⟨copiedWitness (MAR.parametersWithBeta A A.β A.hβ) true P h1 hH⟩⟩

theorem copyLaw_ate (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (hP : P ∈ MAR.treatmentClass A A.β A.hβ) (hH : 1 ≤ A.H) : MAR.ate A.d (copyLaw A P) = 1 := by
  obtain ⟨⟨h0⟩,⟨h1⟩⟩ := hP
  unfold MAR.ate
  rw [MAR.armMean_eq_mean (MAR.parametersWithBeta A A.β A.hβ) true _
      (copiedWitness _ true P h1 hH),
    MAR.armMean_eq_mean A false _ (copiedWitness A false P h0 hH)]
  norm_num [copiedWitness,ConditionalWald.bit]

theorem outcomeLaw_embedLaw (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) : outcomeLaw A (embedLaw A P) = P := by
  apply Subtype.ext
  change ((P : Measure _).map (embed A.d)).map (outcomeMap A.d) = _
  rw [Measure.map_map (outcomeMap_measurable A.d) (embed_measurable A.d)]
  have h : outcomeMap A.d ∘ embed A.d = id := rfl
  rw [h,Measure.map_id]
  rfl

theorem treatmentLaw_embedLaw (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse)) :
    treatmentLaw A (embedLaw A P) = copyLaw A P := by
  apply Subtype.ext
  change ((P : Measure _).map (embed A.d)).map (treatmentMap A.d) = _
  rw [Measure.map_map (treatmentMap_measurable A.d) (embed_measurable A.d)]
  rfl

theorem embedLaw_mem (A : Model.Parameters) (cW : ℝ) (hc1 : cW ≤ 1) (hH : 1 ≤ A.H)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (hP : P ∈ MAR.treatmentClass A A.β A.hβ) : embedLaw A P ∈ modelClass A cW := by
  refine ⟨?_,?_,?_⟩
  · rw [outcomeLaw_embedLaw]
    exact hP
  · rw [treatmentLaw_embedLaw]
    exact copyLaw_mem A P hP hH
  · change cW ≤ MAR.ate A.d (treatmentLaw A (embedLaw A P))
    rw [treatmentLaw_embedLaw,copyLaw_ate A P hP hH]
    exact hc1

theorem embedLaw_target (A : Model.Parameters) (hH : 1 ≤ A.H)
    (P : ProbabilityMeasure (Model.Covariate A.d × MAR.TreatmentResponse))
    (hP : P ∈ MAR.treatmentClass A A.β A.hβ) : target A (embedLaw A P) = MAR.ate A.d P := by
  unfold target numerator denominator
  rw [outcomeLaw_embedLaw,treatmentLaw_embedLaw,copyLaw_ate A P hP hH,div_one]

theorem lowerBracket_of_treatment (A : Model.Parameters) (cW : ℝ) (hc1 : cW ≤ 1) (hH : 1 ≤ A.H)
    (hlower : Model.LowerBracket (MAR.ate A.d) (MAR.treatmentClass A A.β A.hβ) A.bracketParameters) :
    Model.LowerBracket (target A) (modelClass A cW) A.bracketParameters := by
  let K := Kernel.deterministic (embed A.d) (embed_measurable A.d)
  have hK : ∀ P,Model.kernelLaw K P = embedLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (embed_measurable A.d)
  apply Model.lowerBracket_kernel K _ _ _ _ _ _ _ hlower
  · intro P hP
    rw [hK]
    exact embedLaw_mem A cW hc1 hH P hP
  · intro P hP
    rw [hK]
    exact embedLaw_target A hH P hP

end RoughRegime.Applications.Wald
