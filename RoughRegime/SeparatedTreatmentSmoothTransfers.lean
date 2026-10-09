module

public import RoughRegime.SeparatedTreatmentRisk
public import RoughRegime.SeparatedTreatmentParametric
public import RoughRegime.SeparatedMARSmoothLower


@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance (d : ℕ) (j : Bool) : IsMarkovKernel (MAR.augmentationKernel d j) := MAR.augmentationKernel_markov d j

theorem smooth_augmentation_ate_risk_transfer (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hH : 1/2≤A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n (MAR.ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) t ∧
    Model.minimaxRMSE n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n (MAR.ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) := by
  let T := fun Q=>MAR.armSign j*MAR.ate A.d Q+1/2
  have he := Model.sign_affine_risks_eq n (MAR.ate A.d) T (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse)
    (MAR.armSign j) (1/2) t (by cases j <;> norm_num [MAR.armSign]) (fun _ _=>rfl)
  rw [←he.1,←he.2]
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d j) _ T _ _
  · exact fun P hP=>⟨augmentation_mem_selected A j βother hβother hH P hP.1,
      MAR.augmentationLaw_mem_smoothDensityClass A j P hP.2⟩
  · rintro P ⟨⟨W,hother⟩,_hSmooth⟩
    change MAR.armSign j*MAR.ate A.d (MAR.augmentationLaw A j P)+1/2=target A.d P
    rw [augmentation_ate A j βother hβother P W hH hother]
    cases j <;> simp [MAR.armSign]

theorem smooth_augmentation_armMean_risk_transfer (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hH : 1/2≤A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n (MAR.armMean A.d j) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) t ∧
    Model.minimaxRMSE n (target A.d) (augmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n (MAR.armMean A.d j) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) := by
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d j) _ _ _ _
  · exact fun P hP=>⟨augmentation_mem_selected A j βother hβother hH P hP.1,
      MAR.augmentationLaw_mem_smoothDensityClass A j P hP.2⟩
  · rintro P ⟨⟨W,_⟩,_hSmooth⟩
    exact augmentation_selected_armMean A j P W

theorem smooth_selected_ate_lowerBracket (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.ate A.d) (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := smooth_augmentable_lowerBracket A hδ hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have hr := smooth_augmentation_ate_risk_transfer A j βother hβother (by linarith) n
    (2*c*Model.lowerBracketScale A.bracketParameters n)
  exact ⟨(hbound n hn).1.trans hr.2,fun hθ=>(hbound n hn).2 hθ |>.trans hr.1⟩

theorem smooth_selected_armMean_rough_hardness (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (MAR.armMean A.d j)
      (selectedTreatmentClass A j βother hβother ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,n0,_hn0,hb⟩ := smooth_augmentable_rough_lower A hδ hlo hhi hH hrough
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have h := (hb n hn).2.trans (smooth_augmentation_armMean_risk_transfer A j βother hβother
    (by linarith) n (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n)).1
  simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc] using h

theorem smooth_constant_effect_risk_transfer (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hH : 1/2≤A.H) (k : Option Bool) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response) t ≤
      Model.minimaxTail n (effectTarget A.d k) (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) t ∧
    Model.minimaxRMSE n (target A.d) (constantAugmentableClass A ∩ Model.smoothDensityClass A.d Response) ≤
      Model.minimaxRMSE n (effectTarget A.d k) (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) := by
  let T := fun Q=> -1*effectTarget A.d k Q+1/2
  have he := Model.sign_affine_risks_eq n (effectTarget A.d k) T (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse)
    (-1) (1/2) t (by norm_num) (fun _ _=>rfl)
  rw [←he.1,←he.2]
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d false) _ T _ _
  · rintro P ⟨⟨W,c,hc,hother⟩,hSmooth⟩
    exact ⟨⟨W.falseTreatment A β1 hβ1 P hH hother⟩,
      MAR.augmentationLaw_mem_smoothDensityClass A false P hSmooth⟩
  · rintro P ⟨⟨W,c,hc,hother⟩,hSmooth⟩
    have ht : target A.d P=c := by
      rw [W.target_eq_mean A P]
      simp only [hc,integral_const,probReal_univ,one_smul]
    have h := augmentation_constant_effects A false β1 hβ1 P W hH hother c hc
    have heff : effectTarget A.d k (MAR.augmentationLaw A false P)= -(c-1/2) := by
      cases k with
      | none=>simpa only [effectTarget,MAR.armSign,Bool.false_eq_true,ite_false,neg_one_mul] using h.1
      | some j=>simpa only [effectTarget,MAR.armSign,Bool.false_eq_true,ite_false,neg_one_mul] using h.2 j
    change -1*effectTarget A.d k (MAR.augmentationLaw A false P)+1/2=target A.d P
    rw [heff,ht]
    ring

theorem smooth_treatment_parametric_lower (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ≤1/2) (hg : A.gminus≤1 ∧ 1≤A.gplus) (hH : 1≤A.H) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.ate A.d) (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.att A.d) (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.atu A.d) (SeparatedTreatment.modelClass A β1 hβ1 ∩ Model.smoothDensityClass A.d MAR.TreatmentResponse) := by
  obtain ⟨c,hc,he⟩ := smooth_constantAugmentable_parametric_lower A hδ hg hH
  refine ⟨c,hc,he.mono ?_⟩
  intro n hn
  exact ⟨hn.1.trans (smooth_constant_effect_risk_transfer A β1 hβ1 (by linarith) none n 0).2,
    hn.1.trans (smooth_constant_effect_risk_transfer A β1 hβ1 (by linarith) (some true) n 0).2,
    hn.1.trans (smooth_constant_effect_risk_transfer A β1 hβ1 (by linarith) (some false) n 0).2⟩

end RoughRegime.Applications.SeparatedMAR
