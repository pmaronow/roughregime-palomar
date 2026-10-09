module

public import RoughRegime.MARParametric
public import RoughRegime.LowerMeasure


@[expose] public section
/-! A genuine constant-regression affine MAR path satisfying both inverse
propensity and weighted-density restrictions used by treatment augmentation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

def constantPathWitness (A : Model.Parameters)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) (t : ℝ) :
    Witness A (Model.productLaw A (responsePath t).probabilityMeasure) where
  p _ := 1
  w _ := 1/2
  b _ := 1/2+AffineResponseLower.clip (1/8) t
  measurableP := measurable_const
  measurableW := measurable_const
  measurableB := measurable_const
  nonnegativeP := Eventually.of_forall (fun _ => by norm_num)
  marginal := by
    change ((Model.cubeVolume A.d).prod (responsePath t).measure).map Prod.fst = _
    simp
  momentD := by
    have h := Applications.conditional_snd_product (Model.cubeVolume A.d)
      (responsePath t).measure observed observed_measurable
    change ((Model.cubeVolume A.d).prod (responsePath t).measure)[observed ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[((Model.cubeVolume A.d).prod (responsePath t).measure)] fun _ => 1/2
    simpa only [(responsePath_moments t).1,Function.comp_def] using h
  momentV := by
    have h := Applications.conditional_snd_product (Model.cubeVolume A.d)
      (responsePath t).measure observedOutcome observedOutcome_measurable
    filter_upwards [h] with o ho
    change ((Model.cubeVolume A.d).prod (responsePath t).measure)[observedOutcome ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] o = (1/2)*(1/2+AffineResponseLower.clip (1/8) t)
    rw [ho,(responsePath_moments t).2]
    ring
  overlap := Eventually.of_forall (fun _ => ⟨hδ,by linarith⟩)
  smoothInverse := by
    change (fun _ : Model.Covariate A.d => (1/2:ℝ)⁻¹) ∈ Model.holderBall A.α A.H
    apply Model.const_mem_holderBall A.hα
    norm_num
    exact hH
  smoothB := by
    apply Model.const_mem_holderBall A.hβ
    have hb := AffineResponseLower.clip_abs_le (by norm_num : (0:ℝ)≤1/8) t
    have he := abs_add_le (1/2:ℝ) (AffineResponseLower.clip (1/8) t)
    norm_num at he
    linarith
  densityBounds := Eventually.of_forall (fun _ => by simpa only [mul_one] using hg)

theorem constantPath_otherInverse (A : Model.Parameters)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) (t : ℝ) :
    (fun x => (1-(constantPathWitness A hδ hg hH t).w x)⁻¹) ∈ Model.holderBall A.α A.H := by
  change (fun _ : Model.Covariate A.d => (1-(1/2:ℝ))⁻¹) ∈ Model.holderBall A.α A.H
  apply Model.const_mem_holderBall A.hα
  norm_num
  exact hH

theorem constantPath_otherDensity (A : Model.Parameters)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) (t : ℝ) :
    ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus ≤ (1-(constantPathWitness A hδ hg hH t).w x)*(constantPathWitness A hδ hg hH t).p x ∧
      (1-(constantPathWitness A hδ hg hH t).w x)*(constantPathWitness A hδ hg hH t).p x ≤ A.gplus := by
  apply Eventually.of_forall
  intro x
  change A.gminus ≤ (1-1/2)*1 ∧ (1-1/2)*1 ≤ A.gplus
  norm_num
  exact hg

theorem parametricLaw_mem_augmentable (A : Model.Parameters)
    (hδ : A.δ ≤ 1/2) (hg : A.gminus ≤ 1/2 ∧ 1/2 ≤ A.gplus) (hH : 2 ≤ A.H) (t : ℝ) :
    (parametricLaw A t).probabilityMeasure ∈ augmentableClass A := by
  rw [parametricLaw_eq_product]
  exact ⟨constantPathWitness A hδ hg hH t,constantPath_otherInverse A hδ hg hH t,
    constantPath_otherDensity A hδ hg hH t⟩

end RoughRegime.Applications.MAR
