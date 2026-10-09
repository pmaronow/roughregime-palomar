module

public import RoughRegime.MARConstantPath
public import RoughRegime.ApplicationTreatmentUpper


@[expose] public section
/-! Genuine root-n lower bounds for all three treatment targets, from the
actual bounded affine MAR family and the independent-coin augmentation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000
local instance (d : ℕ) : ProbabilityTheory.IsMarkovKernel (augmentationKernel d false) := augmentationKernel_markov d false

def constantAugmentableClass (A : Model.Parameters) :
    Set (ProbabilityMeasure (Model.Covariate A.d × Response)) :=
  {P | ∃ W : Witness A P, ∃ c : ℝ, (∀ x,W.b x=c) ∧
    (fun x => (1-W.w x)⁻¹) ∈ Model.holderBall A.α A.H ∧
    ∀ᵐ x ∂Model.cubeVolume A.d,A.gminus ≤ (1-W.w x)*W.p x ∧ (1-W.w x)*W.p x ≤ A.gplus}

theorem parametricLaw_mem_constantAugmentable (A : Model.Parameters)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) (t : ℝ) :
    (parametricLaw A t).probabilityMeasure ∈ constantAugmentableClass A := by
  rw [parametricLaw_eq_product]
  exact ⟨constantPathWitness A hδ hg hH t,1/2+AffineResponseLower.clip (1/8) t,
    fun _=>rfl,constantPath_otherInverse A hδ hg hH t,constantPath_otherDensity A hδ hg hH t⟩

theorem constantAugmentable_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤
        Model.minimaxRMSE n (Model.target A (observables A hM)) (constantAugmentableClass A) ∧
      (1/4:ℝ≥0∞) ≤ Model.minimaxTail n (Model.target A (observables A hM))
        (constantAugmentableClass A) (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  have hderiv : HasDerivAt (fun t => Model.target A (observables A hM) (parametricLaw A t).probabilityMeasure)
      1 0 := by
    apply ((hasDerivAt_id (0:ℝ)).const_add (1/2)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1/8:ℝ)<0) (by norm_num : (0:ℝ)<1/8)] with t ht
    rw [parametricLaw_target,AffineResponseLower.clip_eq ht]
    rfl
  apply LowerMeasure.parametric_path_minimax_bound (parametricLaw A) (fun _=>1)
    (fun o=>regressionScore o.2) (Model.target A (observables A hM)) (constantAugmentableClass A)
    (-(1/8)) (1/8) 0 1 (1/2) 2 (by norm_num) hderiv one_ne_zero (by norm_num) (by norm_num)
  · intro t ht
    apply Eventually.of_forall
    intro o
    change 1+0*0+AffineResponseLower.clip (1/8) t*regressionScore o.2=1+t*regressionScore o.2
    rw [AffineResponseLower.clip_eq ht]
    ring
  · intro t ht
    apply Eventually.of_forall
    intro o
    have h := AffineResponseLower.affine_density_lower (fun _ : Response=>0) regressionScore
      0 (1/8) 2 t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _=>by norm_num) regressionScore_bound o.2
    simpa only [zero_mul,add_zero,AffineResponseLower.clip_eq ht] using h
  · exact Eventually.of_forall (fun o=>regressionScore_bound o.2)
  · intro t _
    exact parametricLaw_mem_constantAugmentable A hδ hg hH t

theorem constant_effect_risk_transfer (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hH : 1/2 ≤ A.H)
    (T : ProbabilityMeasure (Model.Covariate A.d × TreatmentResponse) → ℝ)
    (hT : ∀ P (W : Witness A P) c, (∀ x,W.b x=c) →
      (fun x=>(1-W.w x)⁻¹) ∈ Model.holderBall A.α A.H →
      (∀ᵐ x ∂Model.cubeVolume A.d,A.gminus ≤ (1-W.w x)*W.p x ∧ (1-W.w x)*W.p x ≤ A.gplus) →
      T (augmentationLaw A false P) = -1*(Model.target A (observables A hM) P-1/2))
    (n : ℕ) (t : ℝ) :
    Model.minimaxTail n (Model.target A (observables A hM)) (constantAugmentableClass A) t ≤
      Model.minimaxTail n T (treatmentClass A β1 hβ1) t ∧
    Model.minimaxRMSE n (Model.target A (observables A hM)) (constantAugmentableClass A) ≤
      Model.minimaxRMSE n T (treatmentClass A β1 hβ1) := by
  let S := fun Q=> -1*T Q+1/2
  have heq := Model.sign_affine_risks_eq n T S (treatmentClass A β1 hβ1) (-1) (1/2) t
    (by norm_num) (fun _ _=>rfl)
  rw [←heq.1,←heq.2]
  apply Model.kernel_reduction n (augmentationKernel A.d false) _ S _ _
  · rintro P ⟨W,c,hc,hInv,hD⟩
    exact augmentation_false_mem_treatmentClass A β1 hβ1 P W hH hInv hD
  · rintro P ⟨W,c,hc,hInv,hD⟩
    change -1*T (augmentationLaw A false P)+1/2=Model.target A (observables A hM) P
    rw [hT P W c hc hInv hD]
    ring

theorem treatment_parametric_lower (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (β1 : ℝ) (hβ1 : 0 < β1) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (ate A.d) (treatmentClass A β1 hβ1) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (att A.d) (treatmentClass A β1 hβ1) ∧
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n (atu A.d) (treatmentClass A β1 hβ1) := by
  obtain ⟨c,hc,he⟩ := constantAugmentable_parametric_lower A hM hδ hg hH
  have hHalf : 1/2 ≤ A.H := by linarith
  refine ⟨c,hc,?_⟩
  filter_upwards [he] with n hn
  have hATE := constant_effect_risk_transfer A hM β1 hβ1 hHalf (ate A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).1) n 0
  have hATT := constant_effect_risk_transfer A hM β1 hβ1 hHalf (att A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).2 true) n 0
  have hATU := constant_effect_risk_transfer A hM β1 hβ1 hHalf (atu A.d)
    (fun P W c hc hInv hD => by
      simpa only [armSign,Bool.false_eq_true,ite_false] using
        (augmentation_constant_effects A hM false P W hHalf hInv hD c hc).2 false) n 0
  exact ⟨hn.1.trans hATE.2,hn.1.trans hATT.2,hn.1.trans hATU.2⟩

end RoughRegime.Applications.MAR
