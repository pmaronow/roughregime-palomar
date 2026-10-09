module

public import RoughRegime.CausalIV


@[expose] public section
/-! The actual observed-law Wald ratio is the complier average effect under
binary consistency, conditional instrument randomization and monotonicity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal.IVData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

 theorem numerator_potential (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
       (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0) :
     Applications.Wald.numerator A (P.map D.observation)=
       ∫ ω,(D.potentialOutcome true ω:ℝ)-(D.potentialOutcome false ω:ℝ) ∂(P:Measure Ω) := by
   have hmap : Applications.Wald.outcomeLaw A (P.map D.observation)=
       P.map (treatmentObservation A.d D.X D.Z D.observedOutcome) := by
     unfold Applications.Wald.outcomeLaw
     rw [probabilityMap_comp P D.observation (Applications.Wald.outcomeMap A.d)
       D.observation_measurable (Applications.Wald.outcomeMap_measurable A.d)]
     rfl
   have hi (j : Bool) : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le
       D.Z (D.potentialOutcome j) (P:Measure Ω) := hex.comp measurable_id (latentOutcome_measurable j)
   have hc (j : Bool) : ∀ᵐ ω ∂(P:Measure Ω),D.Z ω=j→D.observedOutcome ω=D.potentialOutcome j ω :=
     Eventually.of_forall (fun ω=>D.outcome_consistency j ω)
   unfold Applications.Wald.numerator
   rw [hmap]
   unfold Applications.MAR.ate
   rw [armMean_potential_identification A.d P true D.X D.Z D.observedOutcome (D.potentialOutcome true)
       D.hX D.hZ D.observedOutcome_measurable (D.potentialOutcome_measurable true) (hc true) (hi true) (hpositive true),
     armMean_potential_identification A.d P false D.X D.Z D.observedOutcome (D.potentialOutcome false)
       D.hX D.hZ D.observedOutcome_measurable (D.potentialOutcome_measurable false) (hc false) (hi false) (hpositive false)]
   have hp (j : Bool) : Integrable (fun ω=>(D.potentialOutcome j ω:ℝ)) (P:Measure Ω) :=
     Integrable.of_mem_Icc 0 1 (measurable_subtype_coe.comp (D.potentialOutcome_measurable j)).aemeasurable
       (Eventually.of_forall (fun ω=>(D.potentialOutcome j ω).property))
   exact (integral_sub (hp true) (hp false)).symm

 theorem denominator_potential (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
       (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0) :
     Applications.Wald.denominator A (P.map D.observation)=
       ∫ ω,(Applications.MAR.bitOutcome (D.potentialTreatment true ω):ℝ)-
         (Applications.MAR.bitOutcome (D.potentialTreatment false ω):ℝ) ∂(P:Measure Ω) := by
   let y := Applications.MAR.bitOutcome∘D.observedTreatment
   let p (j : Bool) := Applications.MAR.bitOutcome∘D.potentialTreatment j
   have hy : Measurable y := (measurable_of_countable Applications.MAR.bitOutcome).comp D.observedTreatment_measurable
   have hp (j : Bool) : Measurable (p j) :=
     (measurable_of_countable Applications.MAR.bitOutcome).comp (D.potentialTreatment_measurable j)
   have hmap : Applications.Wald.treatmentLaw A (P.map D.observation)=P.map (treatmentObservation A.d D.X D.Z y) := by
     unfold Applications.Wald.treatmentLaw
     rw [probabilityMap_comp P D.observation (Applications.Wald.treatmentMap A.d)
       D.observation_measurable (Applications.Wald.treatmentMap_measurable A.d)]
     rfl
   have hi (j : Bool) : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le
       D.Z (p j) (P:Measure Ω) :=
     hex.comp measurable_id ((measurable_of_countable Applications.MAR.bitOutcome).comp (latentTreatment_measurable j))
   have hc (j : Bool) : ∀ᵐ ω ∂(P:Measure Ω),D.Z ω=j→y ω=p j ω :=
     Eventually.of_forall (fun ω h=>congrArg Applications.MAR.bitOutcome (D.treatment_consistency j ω h))
   unfold Applications.Wald.denominator
   rw [hmap]
   unfold Applications.MAR.ate
   rw [armMean_potential_identification A.d P true D.X D.Z y (p true) D.hX D.hZ hy (hp true)
       (hc true) (hi true) (hpositive true),
     armMean_potential_identification A.d P false D.X D.Z y (p false) D.hX D.hZ hy (hp false)
       (hc false) (hi false) (hpositive false)]
   have hip (j : Bool) : Integrable (fun ω=>(p j ω:ℝ)) (P:Measure Ω) :=
     Integrable.of_mem_Icc 0 1 (measurable_subtype_coe.comp (hp j)).aemeasurable
       (Eventually.of_forall (fun ω=>(p j ω).property))
   exact (integral_sub (hip true) (hip false)).symm

 theorem numerator_complier (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
       (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0)
     (hmonotone : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω) :
     Applications.Wald.numerator A (P.map D.observation)=∫ ω in D.complierSet,D.effect ω ∂(P:Measure Ω) := by
   rw [D.numerator_potential A P hex hpositive]
   have he := hmonotone.mono (fun ω h=>D.monotone_outcome_difference ω h)
   rw [integral_congr_ae he,integral_indicator D.complierSet_measurable]

 theorem denominator_complier (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
       (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0)
     (hmonotone : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω) :
     Applications.Wald.denominator A (P.map D.observation)=(P:Measure Ω).real D.complierSet := by
   rw [D.denominator_potential A P hex hpositive]
   have he := hmonotone.mono (fun ω h=>D.monotone_treatment_difference ω h)
   rw [integral_congr_ae he]
   simpa only [Pi.one_def] using integral_indicator_one (μ:=(P:Measure Ω)) D.complierSet_measurable

 theorem wald_identification (A : Model.Parameters) (P : ProbabilityMeasure Ω) (D : IVData A.d Ω)
     (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P:Measure Ω))
     (hpositive : ∀ j : Bool,∀ᵐ ω ∂(P:Measure Ω),
       (P:Measure Ω)[binaryIndicator j∘D.Z|MeasurableSpace.comap D.X inferInstance] ω≠0)
     (hmonotone : ∀ᵐ ω ∂(P:Measure Ω),D.A0 ω≤D.A1 ω)
     (_hcomplier : (P:Measure Ω) D.complierSet≠0) :
     Applications.Wald.target A (P.map D.observation)=∫ ω,D.effect ω ∂(ProbabilityTheory.cond (P:Measure Ω) D.complierSet) := by
   unfold Applications.Wald.target
   rw [D.numerator_complier A P hex hpositive hmonotone,D.denominator_complier A P hex hpositive hmonotone]
   rw [ProbabilityTheory.cond,integral_smul_measure]
   simp only [ENNReal.toReal_inv,smul_eq_mul,Measure.real,div_eq_mul_inv,mul_comm]

end RoughRegime.Causal.IVData
