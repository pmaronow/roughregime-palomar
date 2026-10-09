module

public import RoughRegime.ApplicationEffects
public import RoughRegime.AffineRisk


@[expose] public section
open MeasureTheory Set

noncomputable section

namespace RoughRegime.Applications.MAR

local instance (d : ℕ) (j : Bool) : ProbabilityTheory.IsMarkovKernel (augmentationKernel d j) :=
  augmentationKernel_markov d j

/-- The two literal inverse-propensity and weighted-density restrictions
needed to put the augmented MAR law in both treatment-arm classes. -/
def augmentableClass (A : Model.Parameters) :
    Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | ∃ h : Witness A P,
    (fun x => (1 - h.w x)⁻¹) ∈ Model.holderBall A.α A.H ∧
    ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1 - h.w x) * h.p x ∧ (1 - h.w x) * h.p x ≤ A.gplus}

def selectedTreatmentClass (A : Model.Parameters) (j : Bool) (βother : ℝ)
    (hβother : 0 < βother) :
    Set (ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse)) :=
  armClass A j ∩ armClass (parametersWithBeta A βother hβother) (!j)

theorem augmentationLaw_eq_kernelLaw (A : Model.Parameters) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) :
    augmentationLaw A j P = Model.kernelLaw (augmentationKernel A.d j) P := rfl

/-- The actual independent-coin augmentation transfers both minimax losses
from a MAR mean to ATE, with separate smoothness indices for the two arms. -/
theorem augmentation_ate_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother) (hH : 1 / 2 ≤ A.H)
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A) t ≤
      Model.minimaxTail n (ate A.d) (selectedTreatmentClass A j βother hβother) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A) ≤
      Model.minimaxRMSE n (ate A.d) (selectedTreatmentClass A j βother hβother) := by
  let S : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) → ℝ :=
    fun Q => armSign j * ate A.d Q + 1 / 2
  have hs : |armSign j| = 1 := by cases j <;> norm_num [armSign]
  have heq := Model.sign_affine_risks_eq n (ate A.d) S
    (selectedTreatmentClass A j βother hβother) (armSign j) (1 / 2) t hs
    (fun _ _ => rfl)
  rw [← heq.1, ← heq.2]
  apply Model.kernel_reduction n (augmentationKernel A.d j)
    (Model.target A (observables A hM)) S (augmentableClass A)
    (selectedTreatmentClass A j βother hβother)
  · rintro P ⟨h, hInv, hDensity⟩
    rw [← augmentationLaw_eq_kernelLaw]
    exact ⟨⟨h.augmentationSelectedWitness A j P⟩,
      ⟨h.augmentationOtherWitnessBeta A βother hβother j P hH hInv hDensity⟩⟩
  · rintro P ⟨h, hInv, hDensity⟩
    rw [← augmentationLaw_eq_kernelLaw]
    dsimp only [S]
    rw [augmentation_ate A hM j P h hH hInv hDensity]
    cases j <;> simp [armSign]

/-- Keeping either arm gives its actual minimax upper bound on the treatment
class with distinct regression smoothness indices. -/
theorem treatment_arm_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (n : ℕ) (t : ℝ) :
    (Model.minimaxTail n (armMean A.d false) (treatmentClass A β1 hβ1) t ≤
      Model.minimaxTail n (Model.target A (observables A hM))
        (Model.modelClass A (observables A hM)) t ∧
    Model.minimaxRMSE n (armMean A.d false) (treatmentClass A β1 hβ1) ≤
      Model.minimaxRMSE n (Model.target A (observables A hM))
        (Model.modelClass A (observables A hM))) ∧
    (Model.minimaxTail n (armMean A.d true) (treatmentClass A β1 hβ1) t ≤
      Model.minimaxTail n (Model.target (parametersWithBeta A β1 hβ1)
          (observables (parametersWithBeta A β1 hβ1) hM))
        (Model.modelClass (parametersWithBeta A β1 hβ1)
          (observables (parametersWithBeta A β1 hβ1) hM)) t ∧
    Model.minimaxRMSE n (armMean A.d true) (treatmentClass A β1 hβ1) ≤
      Model.minimaxRMSE n (Model.target (parametersWithBeta A β1 hβ1)
          (observables (parametersWithBeta A β1 hβ1) hM))
        (Model.modelClass (parametersWithBeta A β1 hβ1)
          (observables (parametersWithBeta A β1 hβ1) hM))) := by
  have h0 : treatmentClass A β1 hβ1 ⊆ armClass A false := fun _ h => h.1
  have h1 : treatmentClass A β1 hβ1 ⊆ armClass (parametersWithBeta A β1 hβ1) true :=
    fun _ h => h.2
  have k0 := keepArm_risk_transfer A hM false n t
  have k1 := keepArm_risk_transfer (parametersWithBeta A β1 hβ1) hM true n t
  exact ⟨⟨(Model.minimaxTail_mono_class n _ t h0).trans k0.1,
      (Model.minimaxRMSE_mono_class n _ h0).trans k0.2⟩,
    ⟨(Model.minimaxTail_mono_class n _ t h1).trans k1.1,
      (Model.minimaxRMSE_mono_class n _ h1).trans k1.2⟩⟩

end RoughRegime.Applications.MAR
