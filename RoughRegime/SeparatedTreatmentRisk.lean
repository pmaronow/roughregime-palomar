module

public import RoughRegime.SeparatedTreatmentConstant
public import RoughRegime.SeparatedMARLower
public import RoughRegime.AffineRisk


@[expose] public section
/-! Genuine sharp lower transfers from the separated MAR hard class to the
literal treatment laws, via the actual fair-coin augmentation kernel. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance (d : ℕ) (j : Bool) : IsMarkovKernel (MAR.augmentationKernel d j) := MAR.augmentationKernel_markov d j

def selectedTreatmentClass (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother) :=
  if j then SeparatedTreatment.modelClass (MAR.parametersWithBeta A βother hβother) A.β A.hβ
  else SeparatedTreatment.modelClass A βother hβother

theorem augmentation_mem_selected (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hH : 1/2≤A.H) (P : ProbabilityMeasure (Model.Covariate A.d×Response))
    (hP : P∈augmentableClass A) :
    MAR.augmentationLaw A j P∈selectedTreatmentClass A j βother hβother := by
  obtain ⟨W,hother⟩ := hP
  cases j
  · exact ⟨W.falseTreatment A βother hβother P hH hother⟩
  · exact ⟨W.trueTreatment A βother hβother P hH hother⟩

theorem augmentation_ate (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P)
    (hH : 1/2≤A.H) (hother : (fun x=>1-W.w x)∈Model.holderBall A.α A.H) :
    MAR.ate A.d (MAR.augmentationLaw A j P)=MAR.armSign j*(target A.d P-1/2) := by
  have hs := augmentation_selected_armMean A j P W
  have ho := augmentation_other_armMean A j βother hβother P W hH hother
  cases j <;> simp only [Bool.not_false,Bool.not_true] at ho <;>
    simp [MAR.ate,MAR.armSign,hs,ho]

theorem augmentation_ate_risk_transfer (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hH : 1/2≤A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (augmentableClass A) t ≤
      Model.minimaxTail n (MAR.ate A.d) (selectedTreatmentClass A j βother hβother) t ∧
    Model.minimaxRMSE n (target A.d) (augmentableClass A) ≤
      Model.minimaxRMSE n (MAR.ate A.d) (selectedTreatmentClass A j βother hβother) := by
  let T := fun Q=>MAR.armSign j*MAR.ate A.d Q+1/2
  have he := Model.sign_affine_risks_eq n (MAR.ate A.d) T (selectedTreatmentClass A j βother hβother)
    (MAR.armSign j) (1/2) t (by cases j <;> norm_num [MAR.armSign]) (fun _ _=>rfl)
  rw [←he.1,←he.2]
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d j) _ T _ _
  · exact fun P hP=>augmentation_mem_selected A j βother hβother hH P hP
  · rintro P ⟨W,hother⟩
    change MAR.armSign j*MAR.ate A.d (MAR.augmentationLaw A j P)+1/2=target A.d P
    rw [augmentation_ate A j βother hβother P W hH hother]
    cases j <;> simp [MAR.armSign]

theorem augmentation_armMean_risk_transfer (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hH : 1/2≤A.H) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (augmentableClass A) t ≤
      Model.minimaxTail n (MAR.armMean A.d j) (selectedTreatmentClass A j βother hβother) t ∧
    Model.minimaxRMSE n (target A.d) (augmentableClass A) ≤
      Model.minimaxRMSE n (MAR.armMean A.d j) (selectedTreatmentClass A j βother hβother) := by
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d j) _ _ _ _
  · exact fun P hP=>augmentation_mem_selected A j βother hβother hH P hP
  · rintro P ⟨W,_⟩
    exact augmentation_selected_armMean A j P W

theorem selected_ate_lowerBracket (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Model.LowerBracket (MAR.ate A.d) (selectedTreatmentClass A j βother hβother) A.bracketParameters := by
  obtain ⟨c,hc,n0,hn0,hbound⟩ := augmentable_lowerBracket A hδ hlo hhi hH
  refine ⟨c,hc,n0,hn0,?_⟩
  intro n hn
  have hr := augmentation_ate_risk_transfer A j βother hβother (by linarith) n
    (2*c*Model.lowerBracketScale A.bracketParameters n)
  exact ⟨(hbound n hn).1.trans hr.2,fun hθ=>(hbound n hn).2 hθ |>.trans hr.1⟩

theorem selected_armMean_rough_hardness (A : Model.Parameters) (j : Bool) (βother : ℝ) (hβother : 0<βother)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n (MAR.armMean A.d j)
      (selectedTreatmentClass A j βother hβother) (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  obtain ⟨c,hc,n0,_hn0,hb⟩ := augmentable_rough_lower A hδ hlo hhi hH hrough
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have h := (hb n hn).2.trans (augmentation_armMean_risk_transfer A j βother hβother
    (by linarith) n (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n)).1
  simpa only [Model.lowerBracketScale,Model.Parameters.bracketParameters,ite_true,hrough,mul_assoc] using h

end RoughRegime.Applications.SeparatedMAR
