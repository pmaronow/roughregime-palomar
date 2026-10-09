module

public import RoughRegime.SourceUniversalExtras
public import RoughRegime.MARSourceMoments


@[expose] public section
/-! The literal finite smooth germs for MAR-to-treatment hard-law membership.
All functions are actual inverse propensities and actual affine regressions. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.Applications.MAR
open RoughRegime.Localization RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false

def propensityGerm : SmoothGerm where
  K z := (1-z.1)/2
  domain := univ
  open_domain := isOpen_univ
  origin_mem := mem_univ _
  smooth := by fun_prop

def otherPropensityGerm : SmoothGerm where
  K z := (1+z.1)/2
  domain := univ
  open_domain := isOpen_univ
  origin_mem := mem_univ _
  smooth := by fun_prop

def inversePropensityGerm : SmoothGerm where
  K z := 2/(1-z.1)
  domain := {z | 1-z.1≠0}
  open_domain := isOpen_ne.preimage (by fun_prop : Continuous (fun z : ℝ×ℝ=>1-z.1))
  origin_mem := by norm_num
  smooth := contDiffOn_const.div (by fun_prop) (fun _ hz=>hz)

def otherInverseGerm : SmoothGerm where
  K z := 2/(1+z.1)
  domain := {z | 1+z.1≠0}
  open_domain := isOpen_ne.preimage (by fun_prop : Continuous (fun z : ℝ×ℝ=>1+z.1))
  origin_mem := by norm_num
  smooth := contDiffOn_const.div (by fun_prop) (fun _ hz=>hz)

def regressionGerm : SmoothGerm where
  K z := 1/2+2*z.2/(1-z.1)
  domain := {z | 1-z.1≠0}
  open_domain := inversePropensityGerm.open_domain
  origin_mem := inversePropensityGerm.origin_mem
  smooth := contDiffOn_const.add ((contDiffOn_const.mul contDiffOn_snd).div
    (by fun_prop) (fun _ hz=>hz))

def treatmentExtraConditions (A : Model.Parameters) : Fin 6→SourceExtraCondition A.α A.β :=
  ![⟨.holder inversePropensityGerm A.α A.H,.first,
      by intro v _; norm_num [Condition.germ,inversePropensityGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.holder regressionGerm A.β A.H,.second,
      by intro u _; simp [Condition.germ,regressionGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.holder otherInverseGerm A.α A.H,.first,
      by intro v _; norm_num [Condition.germ,otherInverseGerm,SmoothGerm.baseline],le_rfl⟩,
    ⟨.interval propensityGerm A.δ (1-A.δ),.first,
      by intro v _; norm_num [Condition.germ,propensityGerm,SmoothGerm.baseline],trivial⟩,
    ⟨.weighted propensityGerm A.gminus A.gplus,.first,
      by intro v _; norm_num [Condition.germ,propensityGerm,SmoothGerm.baseline],trivial⟩,
    ⟨.weighted otherPropensityGerm A.gminus A.gplus,.first,
      by intro v _; norm_num [Condition.germ,otherPropensityGerm,SmoothGerm.baseline],trivial⟩]

theorem treatmentExtra_baseline (A0 : Model.Parameters) (D : ℕ) (hM : 1 ≤ A0.M0)
    (F : SourceModelFamily A0 D (observables (A0.withDimension D) hM) baseline)
    (hδ : A0.δ < 1/2) (hH : 2 < A0.H) :
    ∀ i,(treatmentExtraConditions A0 i).condition.baselineAdmissible F.rminus F.rplus := by
  have hrm : F.rminus*(1/2)=A0.gminus := by
    unfold SourceModelFamily.rminus
    rw [(baseline_ratios (A0.withDimension D) hM).1]
    ring
  have hrp : F.rplus*(1/2)=A0.gplus := by
    unfold SourceModelFamily.rplus
    rw [(baseline_ratios (A0.withDimension D) hM).1]
    ring
  intro i
  fin_cases i
  · change 0<A0.α ∧ |2/(1-0)|<A0.H
    norm_num
    exact ⟨A0.hα,hH⟩
  · change 0<A0.β ∧ |1/2+2*0/(1-0)|<A0.H
    norm_num
    exact ⟨A0.hβ,by linarith⟩
  · change 0<A0.α ∧ |2/(1+0)|<A0.H
    norm_num
    exact ⟨A0.hα,hH⟩
  · change A0.δ<(1-0)/2 ∧ (1-0)/2<1-A0.δ
    constructor <;> linarith
  · change 0<(1-0)/2 ∧ A0.gminus≤F.rminus*((1-0)/2) ∧ F.rplus*((1-0)/2)≤A0.gplus
    norm_num
    exact ⟨hrm.ge,hrp.le⟩
  · change 0<(1+0)/2 ∧ A0.gminus≤F.rminus*((1+0)/2) ∧ F.rplus*((1+0)/2)≤A0.gplus
    norm_num
    exact ⟨hrm.ge,hrp.le⟩

end RoughRegime.Applications.MAR
