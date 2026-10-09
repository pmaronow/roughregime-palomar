module

public import RoughRegime.ApplicationTrial
public import RoughRegime.ProductBrackets
public import RoughRegime.KernelTransfers


@[expose] public section
/-! Actual trial class preservation in both directions and minimax transfer
through the paper's real forward map and independent fair-coin kernel. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Trial

structure Witness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) where
  p : Model.Covariate A.d → ℝ
  f : Model.Covariate A.d → ℝ
  measurableP : Measurable p
  measurableF : Measurable f
  nonnegativeP : 0 ≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P : Measure (Model.Observation A Response)).map Prod.fst =
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  fair : (P : Measure (Model.Observation A Response))[MAR.armIndicator true ∘ Prod.snd |
    Model.covariateInformation A Response] =ᵐ[(P : Measure (Model.Observation A Response))]
      fun _ => (1 / 2 : ℝ)
  moment : (P : Measure (Model.Observation A Response))[
    ((fun z => (transformedResponse z : ℝ)) ∘ Prod.snd) |
      Model.covariateInformation A Response] =ᵐ[(P : Measure (Model.Observation A Response))] f ∘ Prod.fst
  smooth : f ∈ Model.holderBall A.α A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus ≤ p x ∧ p x ≤ A.gplus

def modelClass (A : Model.Parameters) : Set (ProbabilityMeasure (Model.Observation A Response)) :=
  {P | Nonempty (Witness A P)}

def forwardLaw (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) :
    ProbabilityMeasure (Model.Observation A Products.BoundedResponse) :=
  ProbabilityMeasure.map P (forward A.d)

@[simp] theorem forwardLaw_measure (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) :
    (forwardLaw A P : Measure (Model.Observation A Products.BoundedResponse)) =
      (P : Measure (Model.Observation A Response)).map (forward A.d) := rfl

def reverseLaw (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Products.BoundedResponse)) :
    ProbabilityMeasure (Model.Observation A Response) := Model.kernelLaw (reverseKernel A.d) P

@[simp] theorem reverseLaw_measure (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Products.BoundedResponse)) :
    (reverseLaw A P : Measure (Model.Observation A Response)) =
      reverseKernel A.d ∘ₘ (P : Measure (Model.Observation A Products.BoundedResponse)) := rfl

theorem forwardLaw_reverseLaw (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Products.BoundedResponse)) :
    forwardLaw A (reverseLaw A P) = P := by
  apply Subtype.ext
  exact forward_reverseKernel_law A.d (P : Measure (Model.Observation A Products.BoundedResponse))

theorem Witness.forward_conditional (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Response)) (W : Witness A P) :
    (forwardLaw A P : Measure (Model.Observation A Products.BoundedResponse))[
      (Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd |
        Model.covariateInformation A Products.BoundedResponse] =ᵐ[
          (forwardLaw A P : Measure (Model.Observation A Products.BoundedResponse))] W.f ∘ Prod.fst := by
  have hinfo : MeasurableSpace.comap (forward A.d) (Model.covariateInformation A Products.BoundedResponse) =
      Model.covariateInformation A Response := by
    rw [Model.covariateInformation, MeasurableSpace.comap_comp]
    rfl
  have hi : Integrable ((fun z => (transformedResponse z : ℝ)) ∘ Prod.snd)
      (P : Measure (Model.Observation A Response)) :=
    Integrable.of_mem_Icc (-1) 1
      ((measurable_subtype_coe.comp transformedResponse_measurable).comp measurable_snd).aemeasurable
      (Filter.Eventually.of_forall (fun o => (transformedResponse o.2).property))
  have hfm : @Measurable (Model.Observation A Products.BoundedResponse) ℝ
      (Model.covariateInformation A Products.BoundedResponse) inferInstance (W.f ∘ Prod.fst) :=
    W.measurableF.comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map (P : Measure (Model.Observation A Response)) (forward A.d)
    (forward_measurable A.d) (Model.covariateInformation A Products.BoundedResponse)
    measurable_fst.comap_le ((Subtype.val : Products.BoundedResponse → ℝ) ∘ Prod.snd)
    (W.f ∘ Prod.fst) (measurable_subtype_coe.comp measurable_snd) hfm hi
  simpa only [hinfo, Function.comp_def, forward] using W.moment

def Witness.forwardWitness (A : Model.Parameters) (hab : A.α = A.β)
    (P : ProbabilityMeasure (Model.Observation A Response)) (W : Witness A P) :
    Products.Witness A (Subtype.val : Products.BoundedResponse → ℝ) Subtype.val (forwardLaw A P) where
  p := W.p
  mU := W.f
  mV := W.f
  measurableP := W.measurableP
  measurableU := W.measurableF
  measurableV := W.measurableF
  nonnegativeP := W.nonnegativeP
  marginal := by
    rw [forwardLaw_measure, Measure.map_map measurable_fst (forward_measurable A.d)]
    exact W.marginal
  momentU := W.forward_conditional A P
  momentV := W.forward_conditional A P
  smoothU := W.smooth
  smoothV := by simpa only [← hab] using W.smooth
  densityBounds := W.densityBounds

def reverseWitness (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Products.BoundedResponse))
    (W : Products.Witness A (Subtype.val : Products.BoundedResponse → ℝ) Subtype.val P) :
    Witness A (reverseLaw A P) where
  p := W.p
  f := W.mU
  measurableP := W.measurableP
  measurableF := W.measurableU
  nonnegativeP := W.nonnegativeP
  marginal := by rw [reverseLaw_measure, reverseKernel_marginal]; exact W.marginal
  fair := reverse_fair_moment A.d (P : Measure (Model.Observation A Products.BoundedResponse))
  moment := reverse_preserved_moment A.d (P : Measure (Model.Observation A Products.BoundedResponse))
    W.mU W.measurableU W.momentU
  smooth := W.smoothU
  densityBounds := W.densityBounds

theorem forwardLaw_mem (A : Model.Parameters) (hab : A.α = A.β)
    (P : ProbabilityMeasure (Model.Observation A Response)) (hP : P ∈ modelClass A) :
    forwardLaw A P ∈ Products.quadraticClass A :=
  ⟨hP.some.forwardWitness A hab P⟩

theorem reverseLaw_mem (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Observation A Products.BoundedResponse))
    (hP : P ∈ Products.quadraticClass A) : reverseLaw A P ∈ modelClass A :=
  ⟨reverseWitness A P hP.some⟩

def quadraticTarget (A : Model.Parameters) (P : ProbabilityMeasure (Model.Observation A Response)) : ℝ :=
  Products.quadraticTarget A (forwardLaw A P)

theorem forward_quadratic_risk_transfer (A : Model.Parameters) (hab : A.α = A.β)
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (quadraticTarget A) (modelClass A) t ≤
      Model.minimaxTail n (Products.quadraticTarget A) (Products.quadraticClass A) t ∧
    Model.minimaxRMSE n (quadraticTarget A) (modelClass A) ≤
      Model.minimaxRMSE n (Products.quadraticTarget A) (Products.quadraticClass A) := by
  let K := Kernel.deterministic (forward A.d) (forward_measurable A.d)
  have hK : ∀ P, Model.kernelLaw K P = forwardLaw A P := by
    intro P
    apply Subtype.ext
    exact Measure.deterministic_comp_eq_map (forward_measurable A.d)
  apply Model.kernel_reduction n K (quadraticTarget A) (Products.quadraticTarget A)
    (modelClass A) (Products.quadraticClass A)
  · intro P hP
    rw [hK]
    exact forwardLaw_mem A hab P hP
  · intro P _
    rw [hK]
    rfl

theorem reverse_quadratic_risk_transfer (A : Model.Parameters) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Products.quadraticTarget A) (Products.quadraticClass A) t ≤
      Model.minimaxTail n (quadraticTarget A) (modelClass A) t ∧
    Model.minimaxRMSE n (Products.quadraticTarget A) (Products.quadraticClass A) ≤
      Model.minimaxRMSE n (quadraticTarget A) (modelClass A) := by
  apply Model.kernel_reduction n (reverseKernel A.d) (Products.quadraticTarget A) (quadraticTarget A)
    (Products.quadraticClass A) (modelClass A)
  · exact reverseLaw_mem A
  · intro P _
    dsimp only [quadraticTarget]
    rw [← reverseLaw, forwardLaw_reverseLaw]

end RoughRegime.Applications.Trial
