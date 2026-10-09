module

public import RoughRegime.ApplicationOverlapBaseline
public import RoughRegime.SpatialScores


@[expose] public section
/-! Literal affine conditional moments and targets of the two overlap-effect
hard families. The equations come from their actual four-atom response laws. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 theorem affineMean_one (c : ℝ) (hc : |c|≤1/4) (u v : ℝ) :
    affineMean (baseline c hc) (scores c hc) (fun _=>1) u v=1 := by
  simp [affineMean,scores,(baseline_score_moments c hc).1,(baseline_score_moments c hc).2.1]
 theorem affineMean_treatment (c : ℝ) (hc : |c|≤1/4) (u v : ℝ) :
    affineMean (baseline c hc) (scores c hc) treatment u v=1/2+u := by
  rw [affineMean]
  simp only [scores,(baseline_moments c hc).1,(baseline_score_moments c hc).2.2.1,
    (baseline_score_moments c hc).2.2.2.1,mul_one,mul_zero,add_zero]
 theorem affineMean_outcome (c : ℝ) (hc : |c|≤1/4) (u v : ℝ) :
    affineMean (baseline c hc) (scores c hc) outcome u v=1/2+v := by
  rw [affineMean]
  simp only [scores,(baseline_moments c hc).2.1,(baseline_score_moments c hc).2.2.2.2.1,
    (baseline_score_moments c hc).2.2.2.2.2.1,mul_one,mul_zero,add_zero]
 theorem affineMean_product (c : ℝ) (hc : |c|≤1/4) (u v : ℝ) :
    affineMean (baseline c hc) (scores c hc) (fun z=>treatment z*outcome z) u v=
      (1+c)/4+(u+v)/2 := by
  rw [affineMean]
  simp only [scores,(baseline_moments c hc).2.2,(baseline_score_moments c hc).2.2.2.2.2.2.1,
    (baseline_score_moments c hc).2.2.2.2.2.2.2]
  ring
 theorem independent_integrand (A : Model.Parameters) (hM : 1≤A.M0)
    (c : ℝ) (hc : |c|≤1/4) (u v : ℝ) :
    affineIntegrand A (numeratorObservables A hM) (baseline c hc) (scores c hc) u v=c/4-u*v := by
  change affineMean (baseline c hc) (scores c hc) (fun z=>treatment z*outcome z) u v+
    (-1)*(affineMean (baseline c hc) (scores c hc) treatment u v*
      affineMean (baseline c hc) (scores c hc) outcome u v/
      affineMean (baseline c hc) (scores c hc) (fun _=>1) u v)=_
  rw [affineMean_product,affineMean_treatment,affineMean_outcome,affineMean_one]
  ring

 theorem diagonal_affine_means (u v : ℝ) :
    affineMean (baseline (1/4) (by norm_num)) diagonalScores (fun _=>1) u v=1 ∧
    affineMean (baseline (1/4) (by norm_num)) diagonalScores treatment u v=1/2+u+v ∧
    affineMean (baseline (1/4) (by norm_num)) diagonalScores outcome u v=1/2 ∧
    affineMean (baseline (1/4) (by norm_num)) diagonalScores (fun z=>treatment z*outcome z) u v=5/16+(u+v)/2 := by
  simp only [affineMean,diagonalScores,one_mul,integral_const,smul_eq_mul]
  simp only [probReal_univ,one_mul]
  rw [(baseline_score_moments (1/4) (by norm_num)).1,
    (baseline_moments (1/4) (by norm_num)).1,(baseline_moments (1/4) (by norm_num)).2.1,
    (baseline_moments (1/4) (by norm_num)).2.2,
    (baseline_score_moments (1/4) (by norm_num)).2.2.1,
    (baseline_score_moments (1/4) (by norm_num)).2.2.2.2.1,
    (baseline_score_moments (1/4) (by norm_num)).2.2.2.2.2.2.1]
  and_intros <;> ring

 theorem diagonal_numerator_integrand (A : Model.Parameters) (hM : 1≤A.M0) (u v : ℝ) :
    affineIntegrand A (numeratorObservables A hM) (baseline (1/4) (by norm_num)) diagonalScores u v=1/16 := by
  change affineMean _ _ (fun z=>treatment z*outcome z) u v+
    (-1)*(affineMean _ _ treatment u v*affineMean _ _ outcome u v/affineMean _ _ (fun _=>1) u v)=_
  rw [(diagonal_affine_means u v).1,(diagonal_affine_means u v).2.1,
    (diagonal_affine_means u v).2.2.1,(diagonal_affine_means u v).2.2.2]
  ring
 theorem diagonal_denominator_integrand (A : Model.Parameters) (hM : 1≤A.M0) (u v : ℝ) :
    affineIntegrand (diagonalParameters A) (denominatorObservables A hM)
      (baseline (1/4) (by norm_num)) diagonalScores u v=1/4-(u+v)^2 := by
  have hs : (fun z=>treatment z*treatment z)=treatment := by
    funext z; simpa only [pow_two] using treatment_sq z
  change affineMean _ _ (fun z=>treatment z*treatment z) u v+
    (-1)*(affineMean _ _ treatment u v*affineMean _ _ treatment u v/affineMean _ _ (fun _=>1) u v)=_
  rw [hs,(diagonal_affine_means u v).1,(diagonal_affine_means u v).2.1]
  ring

 theorem baselineW_one (A : Model.Parameters) (O : Model.Observables Response A)
    (hD : O.D=fun _=>1) (c : ℝ) (hc : |c|≤1/4) : Model.baselineW A O (baseline c hc)=1 := by
  rw [Model.baselineW,hD];simp
 theorem independent_numerator_integral (A : Model.Parameters) (hM : 1≤A.M0)
    (c : ℝ) (hc : |c|≤1/4) (F : Field (Model.cubeVolume A.d))
    (hsmall : F.epsilon*(scores c hc).C≤1/4) :
    numerator A.d (law (scores c hc) F hsmall).probabilityMeasure=
      ∫ x,F.p x*(c/4-F.u x*F.v x) ∂Model.cubeVolume A.d := by
  rw [← numerator_target A hM,model_target_integral A (numeratorObservables A hM) (baseline c hc) (scores c hc) F hsmall
    (by rw [baselineW_one A _ rfl];norm_num)]
  simp_rw [independent_integrand]
 theorem diagonal_numerator (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*diagonalScores.C≤1/4) :
    numerator A.d (law diagonalScores F hsmall).probabilityMeasure=1/16 := by
  rw [← numerator_target A hM,model_target_integral A (numeratorObservables A hM) _ diagonalScores F hsmall
    (by rw [baselineW_one A _ rfl];norm_num)]
  simp_rw [diagonal_numerator_integrand,mul_comm _ (1/16:ℝ)]
  rw [integral_const_mul,F.integralP,mul_one]
 theorem diagonal_denominator_integral (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*diagonalScores.C≤1/4) :
    denominator A.d (law diagonalScores F hsmall).probabilityMeasure=
      ∫ x,F.p x*(1/4-(F.u x+F.v x)^2) ∂Model.cubeVolume A.d := by
  rw [← denominator_target A hM,model_target_integral (diagonalParameters A) (denominatorObservables A hM)
    _ diagonalScores F hsmall (by rw [baselineW_one _ _ rfl];norm_num)]
  simp_rw [diagonal_denominator_integrand]

end RoughRegime.Applications.Overlap
