module

public import RoughRegime.SeparatedMARSource
public import RoughRegime.MARConstantPath
public import RoughRegime.ProductBrackets


@[expose] public section
/-! The genuine constant-regression affine path in every literal separated
class of radius H0 > 1. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.SeparatedMAR
set_option maxHeartbeats 1500000

def constantPathWitness (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) (t : ℝ) :
    Witness A (MAR.parametricLaw (lowerParameters A) t).probabilityMeasure where
  p _ := 1
  w _ := 1/2
  b _ := 1/2+AffineResponseLower.clip (1/8) t
  measurableP := measurable_const
  measurableW := measurable_const
  measurableB := measurable_const
  nonnegativeP := Eventually.of_forall (fun _=>by norm_num)
  marginal := by
    rw [MAR.parametricLaw_eq_product]
    change ((Model.cubeVolume A.d).prod (MAR.responsePath t).measure).map Prod.fst = _
    simp
  momentD := by
    have h := Applications.conditional_snd_product (Model.cubeVolume A.d)
      (MAR.responsePath t).measure MAR.observed MAR.observed_measurable
    rw [MAR.parametricLaw_eq_product]
    change ((Model.cubeVolume A.d).prod (MAR.responsePath t).measure)[MAR.observed ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[((Model.cubeVolume A.d).prod (MAR.responsePath t).measure)] fun _=>1/2
    simpa only [(MAR.responsePath_moments t).1,Function.comp_def] using h
  momentV := by
    have h := Applications.conditional_snd_product (Model.cubeVolume A.d)
      (MAR.responsePath t).measure MAR.observedOutcome MAR.observedOutcome_measurable
    rw [MAR.parametricLaw_eq_product]
    filter_upwards [h] with o ho
    change ((Model.cubeVolume A.d).prod (MAR.responsePath t).measure)[MAR.observedOutcome ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] o=(1/2)*(1/2+AffineResponseLower.clip (1/8) t)
    rw [ho,(MAR.responsePath_moments t).2]
    ring
  overlap := Eventually.of_forall (fun _=>⟨hδ,by linarith⟩)
  smoothW := Model.const_mem_holderBall A.hα (by norm_num; linarith)
  smoothB := by
    apply Model.const_mem_holderBall A.hβ
    have hb := AffineResponseLower.clip_abs_le (by norm_num : (0:ℝ)≤1/8) t
    have he := abs_add_le (1/2:ℝ) (AffineResponseLower.clip (1/8) t)
    norm_num at he
    linarith
  densityBounds := Eventually.of_forall (fun _=>hg)

theorem parametricLaw_mem_augmentable (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) (t : ℝ) :
    (MAR.parametricLaw (lowerParameters A) t).probabilityMeasure ∈ augmentableClass A := by
  refine ⟨constantPathWitness A hδ hg hH t,?_⟩
  change (fun _ : Model.Covariate A.d=>1-(1/2:ℝ)) ∈ Model.holderBall A.α A.H
  apply Model.const_mem_holderBall A.hα
  norm_num
  linarith

def constantAugmentableClass (A : Model.Parameters) :
    Set (ProbabilityMeasure (Model.Covariate A.d×Response)) :=
  {P | ∃ W : Witness A P, ∃ c : ℝ, (∀x,W.b x=c) ∧
    (fun x=>1-W.w x) ∈ Model.holderBall A.α A.H}

theorem constantAugmentable_subset (A : Model.Parameters) :
    constantAugmentableClass A ⊆ augmentableClass A := by
  rintro P ⟨W,c,_hc,hother⟩
  exact ⟨W,hother⟩

theorem parametricLaw_mem_constantAugmentable (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) (t : ℝ) :
    (MAR.parametricLaw (lowerParameters A) t).probabilityMeasure ∈ constantAugmentableClass A := by
  refine ⟨constantPathWitness A hδ hg hH t,1/2+AffineResponseLower.clip (1/8) t,fun _=>rfl,?_⟩
  change (fun _ : Model.Covariate A.d=>1-(1/2:ℝ)) ∈ Model.holderBall A.α A.H
  apply Model.const_mem_holderBall A.hα
  norm_num
  linarith

theorem constantAugmentable_parametric_lower (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤
        Model.minimaxRMSE n (target A.d) (constantAugmentableClass A) ∧
      (1/4:ℝ≥0∞) ≤ Model.minimaxTail n (target A.d) (constantAugmentableClass A)
        (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  let G := lowerParameters A
  have hG : 1≤G.M0 := le_rfl
  have htarget : Model.target G (MAR.observables G hG) = target A.d :=
    funext (MAR.generic_target_eq_observedMean G hG)
  have hderiv : HasDerivAt (fun t=>target A.d (MAR.parametricLaw G t).probabilityMeasure) 1 0 := by
    rw [←htarget]
    apply ((hasDerivAt_id (0:ℝ)).const_add (1/2)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1/8:ℝ)<0) (by norm_num : (0:ℝ)<1/8)] with t ht
    rw [MAR.parametricLaw_target G hG t,AffineResponseLower.clip_eq ht]
    rfl
  apply LowerMeasure.parametric_path_minimax_bound (MAR.parametricLaw G) (fun _=>1)
    (fun o=>MAR.regressionScore o.2) (target A.d) (constantAugmentableClass A)
    (-(1/8)) (1/8) 0 1 (1/2) 2 (by norm_num) hderiv one_ne_zero (by norm_num) (by norm_num)
  · intro t ht
    apply Eventually.of_forall
    intro o
    change 1+0*0+AffineResponseLower.clip (1/8) t*MAR.regressionScore o.2=1+t*MAR.regressionScore o.2
    rw [AffineResponseLower.clip_eq ht]
    ring
  · intro t ht
    apply Eventually.of_forall
    intro o
    have h := AffineResponseLower.affine_density_lower (fun _ : Response=>0) MAR.regressionScore
      0 (1/8) 2 t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun _=>by norm_num) MAR.regressionScore_bound o.2
    simpa only [zero_mul,add_zero,AffineResponseLower.clip_eq ht] using h
  · exact Eventually.of_forall (fun o=>MAR.regressionScore_bound o.2)
  · intro t _
    exact parametricLaw_mem_constantAugmentable A hδ hg hH t

theorem augmentable_parametric_lower (A : Model.Parameters) (hδ : A.δ ≤ 1/2)
    (hg : A.gminus ≤ 1 ∧ 1 ≤ A.gplus) (hH : 1 ≤ A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤
        Model.minimaxRMSE n (target A.d) (augmentableClass A) ∧
      (1/4:ℝ≥0∞) ≤ Model.minimaxTail n (target A.d) (augmentableClass A)
        (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  obtain ⟨c,hc,he⟩ := constantAugmentable_parametric_lower A hδ hg hH
  refine ⟨c,hc,he.mono ?_⟩
  intro n hn
  exact ⟨hn.1.trans (Model.minimaxRMSE_mono_class n _ (constantAugmentable_subset A)),
    hn.2.trans (Model.minimaxTail_mono_class n _ _ (constantAugmentable_subset A))⟩

end RoughRegime.Applications.SeparatedMAR
