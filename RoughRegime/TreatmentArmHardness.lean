module

public import RoughRegime.TreatmentATELower


@[expose] public section
/-! Genuine 3/8 rough hardness of each arm mean on the original treatment
class, retaining enough probability for the true empirical pilot transfer. -/
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000
local instance (d : ℕ) (j : Bool) : IsMarkovKernel (augmentationKernel d j) := augmentationKernel_markov d j

theorem augmentation_armMean_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother) (hH : 1/2 ≤ A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A) t ≤
      Model.minimaxTail n (armMean A.d j) (selectedTreatmentClass A j βother hβother) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A) ≤
      Model.minimaxRMSE n (armMean A.d j) (selectedTreatmentClass A j βother hβother) := by
  apply Model.kernel_reduction n (augmentationKernel A.d j) _ _ _ _
  · rintro P ⟨W,hInv,hD⟩
    exact ⟨⟨W.augmentationSelectedWitness A j P⟩,
      ⟨W.augmentationOtherWitnessBeta A βother hβother j P hH hInv hD⟩⟩
  · rintro P ⟨W,_hInv,_hD⟩
    exact augmentation_selected_armMean A hM j P W

theorem selected_armMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤
      Model.minimaxTail n (armMean A.d j) (selectedTreatmentClass A j βother hβother)
        (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,n0,_hn0,hb⟩ := augmentable_rough_lower A hM hlo hhi hH hrough
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have h := (hb n hn).2.trans (augmentation_armMean_risk_transfer A hM j βother hβother
    (by linarith) n (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n)).1
  simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc] using h

theorem selectedTreatmentClass_true_eq (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) :
    selectedTreatmentClass (parametersWithBeta A β1 hβ1) true A.β A.hβ=treatmentClass A β1 hβ1 := by
  have hr : armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false=armClass A false := by
    cases A
    rfl
  change armClass (parametersWithBeta A β1 hβ1) true ∩
    armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false=
    armClass A false ∩ armClass (parametersWithBeta A β1 hβ1) true
  rw [hr]
  exact Set.inter_comm _ _

theorem treatment_controlMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤ Model.minimaxTail n (armMean A.d false)
      (treatmentClass A β1 hβ1) (2*c*Model.lowerBracketScale A.bracketParameters n) :=
  selected_armMean_rough_hardness A hM false β1 hβ1 hlo hhi hH hrough

theorem treatment_treatedMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H)
    (hrough : (parametersWithBeta A β1 hβ1).theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤ Model.minimaxTail n (armMean A.d true)
      (treatmentClass A β1 hβ1) (2*c*Model.lowerBracketScale (parametersWithBeta A β1 hβ1).bracketParameters n) := by
  have h := selected_armMean_rough_hardness (parametersWithBeta A β1 hβ1) hM true A.β A.hβ hlo hhi hH hrough
  rw [selectedTreatmentClass_true_eq] at h
  exact h

end RoughRegime.Applications.MAR
