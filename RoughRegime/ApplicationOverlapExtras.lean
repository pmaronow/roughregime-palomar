module

public import RoughRegime.ApplicationOverlapSpatial
public import RoughRegime.ApplicationOverlapFamilies
public import RoughRegime.SourceSelectedExtras


@[expose] public section
/-! Literal finite smooth-germ restrictions preserving the overlap class
along both actual source constructions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace RoughRegime.Applications.Overlap
open RoughRegime.Localization RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false

 def firstMean : SmoothGerm where
  K p:=1/2+p.1
  domain:=univ
  open_domain:=isOpen_univ
  origin_mem:=mem_univ _
  smooth:=by fun_prop
 def secondMean : SmoothGerm where
  K p:=1/2+p.2
  domain:=univ
  open_domain:=isOpen_univ
  origin_mem:=mem_univ _
  smooth:=by fun_prop
 def diagonalMean : SmoothGerm where
  K p:=1/2+p.1+p.2
  domain:=univ
  open_domain:=isOpen_univ
  origin_mem:=mem_univ _
  smooth:=by fun_prop
 def unitGerm : SmoothGerm where
  K _:=1
  domain:=univ
  open_domain:=isOpen_univ
  origin_mem:=mem_univ _
  smooth:=contDiffOn_const

 def independentExtras (A : Model.Parameters) (ε : ℝ) : Fin 4→SourceExtraCondition A.α A.β :=
  ![⟨.holder firstMean A.α A.H,.first,by intro v _;rfl,le_refl _⟩,
    ⟨.holder secondMean A.β A.H,.second,by intro u _;rfl,le_refl _⟩,
    ⟨.interval firstMean ε (1-ε),.first,by intro v _;rfl,trivial⟩,
    ⟨.weighted unitGerm A.gminus A.gplus,.unrestricted,trivial,trivial⟩]
 def diagonalExtras (A : Model.Parameters) (ε : ℝ) : Fin 3→SourceExtraCondition A.α A.α :=
  ![⟨.holder diagonalMean A.α A.H,.unrestricted,trivial,by simp [GermMode.exponent]⟩,
    ⟨.interval diagonalMean ε (1-ε),.unrestricted,trivial,trivial⟩,
    ⟨.weighted unitGerm A.gminus A.gplus,.unrestricted,trivial,trivial⟩]

 theorem independent_extras_baseline (A : Model.Parameters) (ε : ℝ) (hε : ε<1/2)
    (hH : 1/2<A.H) :
    ∀ i,((independentExtras A ε i).condition).baselineAdmissible A.gminus A.gplus := by
  intro i;fin_cases i
  · exact ⟨A.hα,by simpa [SmoothGerm.baseline,firstMean] using hH⟩
  · exact ⟨A.hβ,by simpa [SmoothGerm.baseline,secondMean] using hH⟩
  · simpa [independentExtras,Condition.baselineAdmissible,SmoothGerm.baseline,firstMean] using
      (show ε<1/2 ∧ (1/2:ℝ)<1-ε from ⟨hε,by linarith⟩)
  · exact ⟨zero_lt_one,by simp [unitGerm,SmoothGerm.baseline]⟩
 theorem diagonal_extras_baseline (A : Model.Parameters) (ε : ℝ) (hε : ε<1/2)
    (hH : 1/2<A.H) :
    ∀ i,((diagonalExtras A ε i).condition).baselineAdmissible A.gminus A.gplus := by
  intro i;fin_cases i
  · exact ⟨A.hα,by simpa [SmoothGerm.baseline,diagonalMean] using hH⟩
  · simpa [diagonalExtras,Condition.baselineAdmissible,SmoothGerm.baseline,diagonalMean] using
      (show ε<1/2 ∧ (1/2:ℝ)<1-ε from ⟨hε,by linarith⟩)
  · exact ⟨zero_lt_one,by simp [unitGerm,SmoothGerm.baseline]⟩

 theorem independent_extras_law_mem (A : Model.Parameters) (ε c : ℝ) (hc : |c|≤1/4)
    (F : SpatialAffine.Field (Model.cubeVolume A.d))
    (hsmall : F.epsilon*(scores c hc).C≤1/4)
    (he : ∀ i,(independentExtras A ε i).condition.Holds F.p F.u F.v) :
    (SpatialAffine.law (scores c hc) F hsmall).probabilityMeasure∈modelClass A ε := by
  apply independent_law_mem A ε c hc F hsmall
  · exact he 0
  · exact he 1
  · filter_upwards [ae_restrict_mem (Model.measurableSet_cube A.d)] with x hx
    simpa [independentExtras,Condition.Holds,unitGerm] using he 3 x hx
  · filter_upwards [ae_restrict_mem (Model.measurableSet_cube A.d)] with x hx
    exact he 2 x hx
 theorem diagonal_extras_law_mem (A : Model.Parameters) (ε : ℝ) (hH : 1/2≤A.H)
    (F : SpatialAffine.Field (Model.cubeVolume A.d))
    (hsmall : F.epsilon*diagonalScores.C≤1/4)
    (he : ∀ i,(diagonalExtras A ε i).condition.Holds F.p F.u F.v) :
    (SpatialAffine.law diagonalScores F hsmall).probabilityMeasure∈modelClass A ε := by
  apply diagonal_law_mem A ε hH F hsmall
  · exact he 0
  · filter_upwards [ae_restrict_mem (Model.measurableSet_cube A.d)] with x hx
    simpa [diagonalExtras,Condition.Holds,unitGerm] using he 2 x hx
  · filter_upwards [ae_restrict_mem (Model.measurableSet_cube A.d)] with x hx
    exact he 1 x hx

end RoughRegime.Applications.Overlap
