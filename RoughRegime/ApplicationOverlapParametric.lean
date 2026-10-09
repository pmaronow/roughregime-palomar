module

public import RoughRegime.ApplicationOverlapAffine
public import RoughRegime.ApplicationOverlapBounds
public import RoughRegime.ParametricBaselineLower


@[expose] public section
/-! The actual correlated Bernoulli response path has fixed propensity and
regression means and gives the overlap effect itself as its parameter. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 def correlationScore (z : Response) : ℝ:=signA z*signY z
 theorem correlationScore_measurable : Measurable correlationScore:=signA_measurable.mul signY_measurable
 theorem correlationScore_bound (z : Response) : |correlationScore z|≤1 := by
  rw [correlationScore,abs_mul,signA_abs,one_mul];exact signY_bound z
 theorem correlation_score_moments :
    (∫ z,correlationScore z ∂(baseline 0 (by norm_num):Measure Response))=0 ∧
    (∫ z,treatment z*correlationScore z ∂(baseline 0 (by norm_num):Measure Response))=0 ∧
    (∫ z,outcome z*correlationScore z ∂(baseline 0 (by norm_num):Measure Response))=0 ∧
    (∫ z,(treatment z*outcome z)*correlationScore z ∂(baseline 0 (by norm_num):Measure Response))=1/4 := by
  rw [baseline_integral 0 (by norm_num) correlationScore correlationScore_measurable,
    baseline_integral 0 (by norm_num) (fun z=>treatment z*correlationScore z) (treatment_measurable.mul correlationScore_measurable),
    baseline_integral 0 (by norm_num) (fun z=>outcome z*correlationScore z) (outcome_measurable.mul correlationScore_measurable),
    baseline_integral 0 (by norm_num) (fun z=>(treatment z*outcome z)*correlationScore z)
      ((treatment_measurable.mul outcome_measurable).mul correlationScore_measurable)]
  norm_num [correlationScore,signA,signY,binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome,RoughRegime.Lower.sign]
 def correlationScores : Scores (baseline 0 (by norm_num):Measure Response) where
  su _:=0
  sv:=correlationScore
  measurableU:=measurable_const
  measurableV:=correlationScore_measurable
  C:=1
  nonnegativeC:=zero_le_one
  boundU _:=by norm_num
  boundV:=correlationScore_bound
  meanU:=by simp
  meanV:=correlation_score_moments.1
 def correlationField (d : ℕ) (t : ℝ) : Field (Model.cubeVolume d) where
  p _:=1
  u _:=0
  v _:=AffineResponseLower.clip (1/4) t
  measurableP:=measurable_const
  measurableU:=measurable_const
  measurableV:=measurable_const
  P:=1
  nonnegativeP:=zero_le_one
  densityBounds _:=⟨zero_le_one,le_refl _⟩
  integralP:=by simp
  epsilon:=1/4
  nonnegativeEpsilon:=by norm_num
  boundU _:=by norm_num
  boundV _:=AffineResponseLower.clip_abs_le (by norm_num) _
 def correlationLaw (A : Model.Parameters) (t : ℝ) :
    GeneralTesting.DensityLaw ((Model.cubeVolume A.d).prod (baseline 0 (by norm_num):Measure Response)) :=
  law correlationScores (correlationField A.d t) (by norm_num [correlationField,correlationScores])

 theorem correlation_affine_means (u v : ℝ) :
    affineMean (baseline 0 (by norm_num)) correlationScores (fun _=>1) u v=1 ∧
    affineMean (baseline 0 (by norm_num)) correlationScores treatment u v=1/2 ∧
    affineMean (baseline 0 (by norm_num)) correlationScores outcome u v=1/2 ∧
    affineMean (baseline 0 (by norm_num)) correlationScores (fun z=>treatment z*outcome z) u v=(1+v)/4 := by
  simp only [affineMean,correlationScores,mul_zero,integral_zero,add_zero,one_mul,integral_const,
    probReal_univ,smul_eq_mul]
  rw [correlation_score_moments.1,(baseline_moments 0 (by norm_num)).1,
    (baseline_moments 0 (by norm_num)).2.1,(baseline_moments 0 (by norm_num)).2.2,
    correlation_score_moments.2.1,correlation_score_moments.2.2.1,correlation_score_moments.2.2.2]
  and_intros <;> ring

 theorem correlationLaw_mem (A : Model.Parameters) (ε t : ℝ) (hε : ε≤1/2)
    (hlo : A.gminus≤1) (hhi : 1≤A.gplus) (hH : 1/2≤A.H) :
    (correlationLaw A t).probabilityMeasure∈modelClass A ε := by
  let F:=correlationField A.d t
  have hs : F.epsilon*correlationScores.C≤1/4:=by norm_num [F,correlationField,correlationScores]
  refine ⟨{
    p:=fun _=>1
    mU:=fun _=>1/2
    mV:=fun _=>1/2
    measurableP:=measurable_const
    measurableU:=measurable_const
    measurableV:=measurable_const
    nonnegativeP:=ae_of_all _ fun _=>zero_le_one
    marginal:=law_marginal correlationScores F hs
    smoothU:=Model.const_mem_holderBall A.hα (by simpa using hH)
    smoothV:=Model.const_mem_holderBall A.hβ (by simpa using hH)
    densityBounds:=ae_of_all _ fun _=>⟨hlo,hhi⟩
    overlap:=ae_of_all _ fun _=>⟨hε,by linarith⟩
    momentU:=?_
    momentV:=?_}⟩
  · have he:=law_conditional_snd correlationScores F hs treatment treatment_measurable 1 zero_le_one treatment_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F treatment o.1=1/2
    rw [bounded_responseMoment_eq_affineMean A _ correlationScores F treatment treatment_measurable 1
      zero_le_one treatment_bound,(correlation_affine_means _ _).2.1]
  · have he:=law_conditional_snd correlationScores F hs outcome outcome_measurable 1 zero_le_one outcome_bound
    refine he.trans (ae_of_all _ fun o=>?_)
    change responseMoment _ F outcome o.1=1/2
    rw [bounded_responseMoment_eq_affineMean A _ correlationScores F outcome outcome_measurable 1
      zero_le_one outcome_bound,(correlation_affine_means _ _).2.2.1]

 theorem correlationLaw_effect (A : Model.Parameters) (hM : 1≤A.M0) (t : ℝ) :
    effect A.d (correlationLaw A t).probabilityMeasure=AffineResponseLower.clip (1/4) t := by
  let F:=correlationField A.d t
  have hs : F.epsilon*correlationScores.C≤1/4:=by norm_num [F,correlationField,correlationScores]
  have hn : numerator A.d (correlationLaw A t).probabilityMeasure=AffineResponseLower.clip (1/4) t/4 := by
    rw [← numerator_target A hM]
    change Model.target A _ (law correlationScores F hs).probabilityMeasure=_
    rw [model_target_integral A (numeratorObservables A hM) _ correlationScores F hs
      (by rw [baselineW_one _ _ rfl];norm_num)]
    have he (u v : ℝ) : affineIntegrand A (numeratorObservables A hM) _ correlationScores u v=v/4 := by
      change affineMean _ _ (fun z=>treatment z*outcome z) u v+(-1)*
        (affineMean _ _ treatment u v*affineMean _ _ outcome u v/affineMean _ _ (fun _=>1) u v)=_
      rw [(correlation_affine_means _ _).1,(correlation_affine_means _ _).2.1,
        (correlation_affine_means _ _).2.2.1,(correlation_affine_means _ _).2.2.2];ring
    simp_rw [he]
    simp [F,correlationField]
  have hd : denominator A.d (correlationLaw A t).probabilityMeasure=1/4 := by
    rw [← denominator_target A hM]
    change Model.target (diagonalParameters A) _ (law correlationScores F hs).probabilityMeasure=_
    rw [model_target_integral (diagonalParameters A) (denominatorObservables A hM) _ correlationScores F hs
      (by rw [baselineW_one _ _ rfl];norm_num)]
    have he (u v : ℝ) : affineIntegrand (diagonalParameters A) (denominatorObservables A hM) _ correlationScores u v=1/4 := by
      have hx : (fun z=>treatment z*treatment z)=treatment:=by funext z;simpa only [pow_two] using treatment_sq z
      change affineMean _ _ (fun z=>treatment z*treatment z) u v+(-1)*
        (affineMean _ _ treatment u v*affineMean _ _ treatment u v/affineMean _ _ (fun _=>1) u v)=_
      rw [hx,(correlation_affine_means _ _).1,(correlation_affine_means _ _).2.1];ring
    simp_rw [he]
    simp [F,correlationField]
  rw [effect,hn,hd];ring

 theorem parametric_lower (A : Model.Parameters) (ε : ℝ) (hε : ε<1/2)
    (hM : 1≤A.M0) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ)))≤ Model.minimaxRMSE n (effect A.d) (modelClass A ε) ∧
      (1/4:ℝ≥0∞)≤ Model.minimaxTail n (effect A.d) (modelClass A ε) (2*c*(n:ℝ)^(-(1/2:ℝ))) := by
  have he (t : ℝ) (ht : t∈Ioo (-1/4:ℝ) (1/4)) :
      AffineResponseLower.clip (1/4) t=t := AffineResponseLower.clip_eq_of_abs_le (abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩)
  have htarg : (fun t=>effect A.d (correlationLaw A t).probabilityMeasure)=ᶠ[𝓝 (0:ℝ)] id := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1/4:ℝ)<0) (by norm_num : (0:ℝ)<1/4)] with t ht
    rw [correlationLaw_effect A hM t,he t ht];rfl
  apply LowerMeasure.parametric_path_minimax_bound (correlationLaw A) (fun _=>1)
    (fun o=>correlationScore o.2) (effect A.d) (modelClass A ε)
    (-1/4) (1/4) 0 1 (1/2) 1 (by norm_num)
    ((hasDerivAt_id (0:ℝ)).congr_of_eventuallyEq htarg) (by norm_num) (by norm_num) zero_le_one
  · intro t ht
    exact ae_of_all _ fun o=>by
      change 1*(1+0*0+AffineResponseLower.clip (1/4) t*correlationScore o.2)=1+t*correlationScore o.2
      rw [he t ht];ring
  · intro t ht
    exact ae_of_all _ fun o=>by
      have hq:=correlationScore_bound o.2
      have ht' : |t|≤1/4:=abs_le.mpr ⟨by linarith [ht.1],ht.2.le⟩
      have hprod:=mul_le_mul ht' hq (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
      rw [← abs_mul] at hprod
      linarith [neg_le_abs (t*correlationScore o.2)]
  · exact ae_of_all _ fun o=>correlationScore_bound o.2
  · intro t _;exact correlationLaw_mem A ε t hε.le hlo.le hhi.le hH.le

end RoughRegime.Applications.Overlap
