module

public import RoughRegime.MARSmoothLower
public import RoughRegime.TreatmentFullBrackets


@[expose] public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1500000
local instance (d : ℕ) (j : Bool) : IsMarkovKernel (augmentationKernel d j) := augmentationKernel_markov d j

theorem smooth_augmentation_ate_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother) (hH : 1 / 2 ≤ A.H)
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n (ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n (ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) := by
  let S : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) → ℝ :=
    fun Q => armSign j * ate A.d Q + 1 / 2
  have hs : |armSign j| = 1 := by cases j <;> norm_num [armSign]
  have heq := Model.sign_affine_risks_eq n (ate A.d) S
    (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) (armSign j) (1 / 2) t hs
    (fun _ _ => rfl)
  rw [← heq.1, ← heq.2]
  apply Model.kernel_reduction n (augmentationKernel A.d j)
    (Model.target A (observables A hM)) S (augmentableClass A ∩ Model.smoothDensityClass A.d Response)
    (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse)
  · rintro P ⟨⟨h,hInv,hDensity⟩,hSmooth⟩
    rw [← augmentationLaw_eq_kernelLaw]
    exact ⟨⟨⟨h.augmentationSelectedWitness A j P⟩,
      ⟨h.augmentationOtherWitnessBeta A βother hβother j P hH hInv hDensity⟩⟩,
      augmentationLaw_mem_smoothDensityClass A j P hSmooth⟩
  · rintro P ⟨⟨h,hInv,hDensity⟩,hSmooth⟩
    rw [← augmentationLaw_eq_kernelLaw]
    dsimp only [S]
    rw [augmentation_ate A hM j P h hH hInv hDensity]
    cases j <;> simp [armSign]

theorem smooth_augmentation_armMean_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother) (hH : 1/2 ≤ A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n (armMean A.d j) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n (armMean A.d j) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse) := by
  apply Model.kernel_reduction n (augmentationKernel A.d j) _ _ _ _
  · rintro P ⟨⟨W,hInv,hD⟩,hSmooth⟩
    exact ⟨⟨⟨W.augmentationSelectedWitness A j P⟩,
      ⟨W.augmentationOtherWitnessBeta A βother hβother j P hH hInv hD⟩⟩,
      augmentationLaw_mem_smoothDensityClass A j P hSmooth⟩
  · rintro P ⟨⟨W,_hInv,_hD⟩,_hSmooth⟩
    exact augmentation_selected_armMean A hM j P W

theorem smooth_selected_armMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (j : Bool) (βother : ℝ) (hβother : 0 < βother)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤
      Model.minimaxTail n (armMean A.d j) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d TreatmentResponse)
        (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,n0,_hn0,hb⟩ := smooth_augmentable_rough_lower A hM hlo hhi hH hrough
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have h := (hb n hn).2.trans (smooth_augmentation_armMean_risk_transfer A hM j βother hβother
    (by linarith) n (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n)).1
  simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc] using h

theorem smooth_selectedTreatmentClass_true_eq (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0 < β1) :
    selectedTreatmentClass (parametersWithBeta A β1 hβ1) true A.β A.hβ=treatmentClass A β1 hβ1 := by
  have hr : armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false=armClass A false := by
    cases A
    rfl
  change armClass (parametersWithBeta A β1 hβ1) true ∩
    armClass (parametersWithBeta (parametersWithBeta A β1 hβ1) A.β A.hβ) false=
    armClass A false ∩ armClass (parametersWithBeta A β1 hβ1) true
  rw [hr]
  exact Set.inter_comm _ _

theorem smooth_treatment_controlMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1)
    (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤ Model.minimaxTail n (armMean A.d false)
      (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (2*c*Model.lowerBracketScale A.bracketParameters n) :=
  smooth_selected_armMean_rough_hardness A hM false β1 hβ1 hlo hhi hH hrough

theorem smooth_treatment_treatedMean_rough_hardness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hlo : max A.δ A.gminus<1/2) (hhi : 1/2<A.gplus) (hH : 2<A.H)
    (hrough : (parametersWithBeta A β1 hβ1).theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞) ≤ Model.minimaxTail n (armMean A.d true)
      (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (2*c*Model.lowerBracketScale (parametersWithBeta A β1 hβ1).bracketParameters n) := by
  have h := smooth_selected_armMean_rough_hardness (parametersWithBeta A β1 hβ1) hM true A.β A.hβ hlo hhi hH hrough
  rw [smooth_selectedTreatmentClass_true_eq] at h
  exact h

theorem smooth_constant_effect_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hH : 1/2 ≤ A.H)
    (T : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) → ℝ)
    (hT : ∀ P (W : Witness A P) c, (∀ x,W.b x=c) →
      (fun x=>(1-W.w x)⁻¹) ∈ Model.holderBall A.α A.H →
      (∀ᵐ x ∂Model.cubeVolume A.d,A.gminus ≤ (1-W.w x)*W.p x ∧ (1-W.w x)*W.p x ≤ A.gplus) →
      T (augmentationLaw A false P) = -1*(Model.target A (observables A hM) P-1/2))
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n T (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n T (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) := by
  let S := fun Q=> -1*T Q+1/2
  have heq := Model.sign_affine_risks_eq n T S (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) (-1) (1/2) t
    (by norm_num) (fun _ _=>rfl)
  rw [←heq.1,←heq.2]
  apply Model.kernel_reduction n (augmentationKernel A.d false) _ S _ _
  · rintro P ⟨⟨W,c,hc,hInv,hD⟩,hSmooth⟩
    exact ⟨augmentation_false_mem_treatmentClass A β1 hβ1 P W hH hInv hD,
      augmentationLaw_mem_smoothDensityClass A false P hSmooth⟩
  · rintro P ⟨⟨W,c,hc,hInv,hD⟩,hSmooth⟩
    change -1*T (augmentationLaw A false P)+1/2=Model.target A (observables A hM) P
    rw [hT P W c hc hInv hD]
    ring

theorem smooth_treatment_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (ate A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (att A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (atu A.d) (treatmentClass A β1 hβ1 ∩ Model.smoothDensityClass A.d TreatmentResponse) := by
  obtain ⟨c,hc,he⟩ := smooth_constantAugmentable_parametric_lower A hM hδ hg hH
  have hHalf : 1/2 ≤ A.H := by linarith
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with n hn
  have hATE := smooth_constant_effect_risk_transfer A hM β1 hβ1 hHalf (ate A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).1) n 0
  have hATT := smooth_constant_effect_risk_transfer A hM β1 hβ1 hHalf (att A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).2 true) n 0
  have hATU := smooth_constant_effect_risk_transfer A hM β1 hβ1 hHalf (atu A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).2 false) n 0
  exact ⟨hn.1.trans hATE.2,hn.1.trans hATT.2,hn.1.trans hATU.2⟩

end RoughRegime.Applications.MAR
