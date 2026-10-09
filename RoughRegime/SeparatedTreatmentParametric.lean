module

public import RoughRegime.SeparatedTreatmentConstant
public import RoughRegime.SeparatedMARPath
public import RoughRegime.AffineRisk


@[expose] public section
/-! The true constant-regression MAR path transfers to all three literal
separated treatment effects with root-n loss. -/
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option maxHeartbeats 1500000
local instance (d : ℕ) : IsMarkovKernel (MAR.augmentationKernel d false) := MAR.augmentationKernel_markov d false

def effectTarget (d : ℕ) (k : Option Bool) :=
  match k with | none=>MAR.ate d | some j=>MAR.conditionalEffect d j

theorem constant_effect_risk_transfer (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hH : 1/2≤A.H) (k : Option Bool) (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (target A.d) (constantAugmentableClass A) t ≤
      Model.minimaxTail n (effectTarget A.d k) (SeparatedTreatment.modelClass A β1 hβ1) t ∧
    Model.minimaxRMSE n (target A.d) (constantAugmentableClass A) ≤
      Model.minimaxRMSE n (effectTarget A.d k) (SeparatedTreatment.modelClass A β1 hβ1) := by
  let T := fun Q=> -1*effectTarget A.d k Q+1/2
  have he := Model.sign_affine_risks_eq n (effectTarget A.d k) T (SeparatedTreatment.modelClass A β1 hβ1)
    (-1) (1/2) t (by norm_num) (fun _ _=>rfl)
  rw [←he.1,←he.2]
  apply Model.kernel_reduction n (MAR.augmentationKernel A.d false) _ T _ _
  · rintro P ⟨W,c,hc,hother⟩
    exact ⟨W.falseTreatment A β1 hβ1 P hH hother⟩
  · rintro P ⟨W,c,hc,hother⟩
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

theorem treatment_parametric_lower (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ≤1/2) (hg : A.gminus≤1 ∧ 1≤A.gplus) (hH : 1≤A.H) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.ate A.d) (SeparatedTreatment.modelClass A β1 hβ1) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.att A.d) (SeparatedTreatment.modelClass A β1 hβ1) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤Model.minimaxRMSE n (MAR.atu A.d) (SeparatedTreatment.modelClass A β1 hβ1) := by
  obtain ⟨c,hc,he⟩ := constantAugmentable_parametric_lower A hδ hg hH
  refine ⟨c,hc,he.mono ?_⟩
  intro n hn
  exact ⟨hn.1.trans (constant_effect_risk_transfer A β1 hβ1 (by linarith) none n 0).2,
    hn.1.trans (constant_effect_risk_transfer A β1 hβ1 (by linarith) (some true) n 0).2,
    hn.1.trans (constant_effect_risk_transfer A β1 hβ1 (by linarith) (some false) n 0).2⟩

end RoughRegime.Applications.SeparatedMAR
