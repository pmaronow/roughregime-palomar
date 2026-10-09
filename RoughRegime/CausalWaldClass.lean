module

public import RoughRegime.CausalRealIV


@[expose] public section
/-! The source observed-law Wald class itself supplies instrument positivity
and positive complier mass; these are derived rather than separate premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Causal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem armClass_selector_positive {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (A : Model.Parameters) (P : ProbabilityMeasure Ω) (j : Bool)
    (X : Ω → Model.Covariate A.d) (Z : Ω → Bool) (Y : Ω → Applications.MAR.Outcome)
    (hX : Measurable X) (hZ : Measurable Z) (hY : Measurable Y)
    (hclass : P.map (treatmentObservation A.d X Z Y) ∈ Applications.MAR.armClass A j) :
    ∀ᵐ ω ∂(P : Measure Ω),
      (P : Measure Ω)[binaryIndicator j ∘ Z | MeasurableSpace.comap X inferInstance] ω ≠ 0 := by
  obtain ⟨W⟩ := hclass
  let μ := (P : Measure Ω)
  let T := treatmentObservation A.d X Z Y
  let m := MeasurableSpace.comap (Prod.fst : Model.Covariate A.d × Applications.MAR.TreatmentResponse → _) inferInstance
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace (Model.Covariate A.d × Applications.MAR.TreatmentResponse) :=
    (inferInstance : MeasurableSpace (Model.Covariate A.d)).prod
      (inferInstance : MeasurableSpace Applications.MAR.TreatmentResponse)
  have hT : Measurable T := treatmentObservation_measurable A.d X Z Y hX hZ hY
  have hi : Integrable ((Applications.MAR.armIndicator j ∘ Prod.snd) ∘ T) μ := by
    apply Integrable.of_mem_Icc 0 1
      (((Applications.MAR.armIndicator_measurable j).comp measurable_snd).comp hT).aemeasurable
    exact Eventually.of_forall (fun ω => binaryIndicator_range j (Z ω))
  have hp := condExp_map_pullback μ T hT m measurable_fst.comap_le
    (Applications.MAR.armIndicator j ∘ Prod.snd)
    ((Applications.MAR.armIndicator_measurable j).comp measurable_snd) hi
  have hinfo : MeasurableSpace.comap T m = MeasurableSpace.comap X inferInstance := by
    rw [MeasurableSpace.comap_comp]
    rfl
  have hsel : (Applications.MAR.armIndicator j ∘ Prod.snd) ∘ T = binaryIndicator j ∘ Z := rfl
  rw [hinfo,hsel] at hp
  have hm : (fun ω => ((μ.map T)[Applications.MAR.armIndicator j ∘ Prod.snd|m]) (T ω)) =ᵐ[μ]
      W.w ∘ X := ae_of_ae_map hT.aemeasurable W.momentD
  have ho : ∀ᵐ ω ∂μ, A.δ ≤ W.w (X ω) :=
    ae_of_ae_map hT.aemeasurable ((W.overlap_on_observations A j (P.map T)).mono (fun _ h => h.1))
  filter_upwards [hp,hm,ho] with ω hp hm ho
  simp only [Function.comp_apply] at hp hm ⊢
  rw [←hp,hm]
  exact ne_of_gt (A.hδ.trans_le ho)

namespace RealIVData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem class_instrument_positive (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : RealIVData A.d Ω) (cW : ℝ)
    (hclass : P.map D.observation ∈ Applications.Wald.modelClass A cW) :
    ∀ j : Bool, ∀ᵐ ω ∂(P : Measure Ω),
      (P : Measure Ω)[binaryIndicator j ∘ D.Z | MeasurableSpace.comap D.X inferInstance] ω ≠ 0 := by
  have hmap : Applications.Wald.outcomeLaw A (P.map D.observation) =
      P.map (treatmentObservation A.d D.X D.Z D.Y) := by
    unfold Applications.Wald.outcomeLaw
    rw [probabilityMap_comp P D.observation (Applications.Wald.outcomeMap A.d)
      D.observation_measurable (Applications.Wald.outcomeMap_measurable A.d)]
    rfl
  have hclasses := hclass.1
  rw [hmap] at hclasses
  intro j
  apply armClass_selector_positive A P j D.X D.Z D.Y D.hX D.hZ D.hY
  cases j
  · exact hclasses.1
  · simpa only [Applications.MAR.parametersWithBeta] using hclasses.2

variable [StandardBorelSpace Ω]

theorem class_complier_mass_positive (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : RealIVData A.d Ω) (cW : ℝ) (hcW : 0 < cW)
    (hc : ∀ᵐ ω ∂(P : Measure Ω), (D.Y ω : ℝ) = if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P : Measure Ω))
    (hmono : ∀ᵐ ω ∂(P : Measure Ω), D.A0 ω ≤ D.A1 ω)
    (hclass : P.map D.observation ∈ Applications.Wald.modelClass A cW) :
    (P : Measure Ω) D.complierSet ≠ 0 := by
  have he := D.bounded.denominator_complier A P (D.bounded_exchangeable P hex)
    (D.class_instrument_positive A P cW hclass) hmono
  rw [D.bounded_law_eq P hc] at he
  change Applications.Wald.denominator A (P.map D.observation) = (P : Measure Ω).real D.complierSet at he
  have hp : 0 < (P : Measure Ω).real D.complierSet := by
    rw [←he]
    exact hcW.trans_le hclass.2.2
  intro hz
  simp only [Measure.real,hz,ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

theorem class_wald_identification (A : Model.Parameters) (P : ProbabilityMeasure Ω)
    (D : RealIVData A.d Ω) (cW : ℝ) (hcW : 0 < cW)
    (hc : ∀ᵐ ω ∂(P : Measure Ω), (D.Y ω : ℝ) = if D.treatment ω then D.Y1 ω else D.Y0 ω)
    (hex : CondIndepFun (MeasurableSpace.comap D.X inferInstance) D.hX.comap_le D.Z D.latent (P : Measure Ω))
    (hmono : ∀ᵐ ω ∂(P : Measure Ω), D.A0 ω ≤ D.A1 ω)
    (hclass : P.map D.observation ∈ Applications.Wald.modelClass A cW) :
    Applications.Wald.target A (P.map D.observation) =
      ∫ ω, D.effect ω ∂(cond (P : Measure Ω) D.complierSet) := by
  exact D.wald_identification A P hc hex (D.class_instrument_positive A P cW hclass) hmono
    (D.class_complier_mass_positive A P cW hcW hc hex hmono hclass)

end RealIVData
end RoughRegime.Causal
