module

public import RoughRegime.SpatialContrast
public import RoughRegime.ProductMoments
public import RoughRegime.SpatialAffineLaw


@[expose] public section
/-! A genuine spatial affine-density path for explained variance and related
quadratic targets, on the literal bounded-response experiment. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal ContDiff Topology
namespace RoughRegime.Applications.Products

 def firstCoordinate (A : Model.Parameters) : Fin A.d := ⟨0,by have:=A.hd; omega⟩

 structure SineSetup (A : Model.Parameters) where
   eta : ℝ
   positive : 0<eta
   small : eta≤1/4
   holder : sineContrast (firstCoordinate A) eta∈Model.holderBall A.α (A.H/2)

 def sineSetup (A : Model.Parameters) : SineSetup A := by
   let h := exists_sine_contrast (firstCoordinate A) A.α A.H A.hα A.hH
   exact ⟨h.choose,h.choose_spec.1,h.choose_spec.2.1,h.choose_spec.2.2.1⟩

 def clampedParameter (t : ℝ) : ℝ := Set.projIcc (-1) 1 (by norm_num) t

 theorem clampedParameter_bound (t : ℝ) : |clampedParameter t|≤1 :=
   abs_le.mpr (Set.projIcc (-1) 1 (by norm_num) t).property

 theorem clampedParameter_eq (t : ℝ) (ht : t∈Icc (-1) 1) : clampedParameter t=t := by
   unfold clampedParameter
   rw [Set.projIcc_of_mem _ ht]

 def diagonalScores : SpatialAffine.Scores (boundedDiagonalBaseline:Measure BoundedResponse) where
   su := Subtype.val
   sv := Subtype.val
   measurableU := measurable_subtype_coe
   measurableV := measurable_subtype_coe
   C := 1
   nonnegativeC := by norm_num
   boundU := response_bound
   boundV := response_bound
   meanU := by rw [boundedDiagonalBaseline_integral _ measurable_subtype_coe]; norm_num [signPoint,sign]
   meanV := by rw [boundedDiagonalBaseline_integral _ measurable_subtype_coe]; norm_num [signPoint,sign]

 namespace SineSetup
 variable {A : Model.Parameters} (S : SineSetup A)

 def phi : Model.Covariate A.d→ℝ := sineContrast (firstCoordinate A) S.eta

 theorem phi_smooth : ContDiff ℝ ∞ S.phi := sineContrast_smooth _ _
 theorem phi_bound (x : Model.Covariate A.d) : |S.phi x|≤S.eta := sineContrast_bound _ _ S.positive.le x
 theorem phi_mean : (∫x,S.phi x ∂Model.cubeVolume A.d)=0 := sineContrast_mean _ _
 theorem phi_square : (∫x,S.phi x^2 ∂Model.cubeVolume A.d)=S.eta^2/2 := sineContrast_square _ _
 theorem phi_square_positive : 0<(∫x,S.phi x^2 ∂Model.cubeVolume A.d) := by rw [S.phi_square]; have := S.positive; positivity

 def field (t : ℝ) : SpatialAffine.Field (Model.cubeVolume A.d) where
   p := fun _=>1
   u := fun x=>clampedParameter t*S.phi x
   v := fun _=>0
   measurableP := measurable_const
   measurableU := measurable_const.mul S.phi_smooth.continuous.measurable
   measurableV := measurable_const
   P := 1
   nonnegativeP := by norm_num
   densityBounds := fun _=>by norm_num
   integralP := by simp
   epsilon := S.eta
   nonnegativeEpsilon := S.positive.le
   boundU := fun x=>by
     rw [abs_mul]
     exact (mul_le_mul (clampedParameter_bound t) (S.phi_bound x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
   boundV := fun _=>by simpa using S.positive.le

 theorem field_small (t : ℝ) : (S.field t).epsilon*diagonalScores.C≤1/4 := by
   simpa only [field,diagonalScores,mul_one] using S.small

 def densityLaw (t : ℝ) : GeneralTesting.DensityLaw
     ((Model.cubeVolume A.d).prod (boundedDiagonalBaseline:Measure BoundedResponse)) :=
   SpatialAffine.law diagonalScores (S.field t) (S.field_small t)

 def probabilityLaw (t : ℝ) : ProbabilityMeasure (Model.Observation A BoundedResponse) :=
   (S.densityLaw t).probabilityMeasure

 theorem density_apply (t : ℝ) (o : Model.Observation A BoundedResponse) :
     (S.densityLaw t).density o=1+clampedParameter t*(o.2:ℝ)*S.phi o.1 := by
   change 1*(1+clampedParameter t*S.phi o.1*(o.2:ℝ)+0*(o.2:ℝ))=_
   ring

 theorem responseMoment_mean (t : ℝ) (x : Model.Covariate A.d) :
     SpatialAffine.responseMoment diagonalScores (S.field t) (Subtype.val : BoundedResponse→ℝ) x=
       clampedParameter t*S.phi x := by
   unfold SpatialAffine.responseMoment
   rw [boundedDiagonalBaseline_integral _ (by unfold SpatialAffine.responseFactor diagonalScores; fun_prop)]
   norm_num [SpatialAffine.responseFactor,diagonalScores,field,signPoint,sign]

 theorem responseMoment_square (t : ℝ) (x : Model.Covariate A.d) :
     SpatialAffine.responseMoment diagonalScores (S.field t) (fun z : BoundedResponse=>(z:ℝ)^2) x=1 := by
   unfold SpatialAffine.responseMoment
   rw [boundedDiagonalBaseline_integral _ (by unfold SpatialAffine.responseFactor diagonalScores; fun_prop)]
   norm_num [SpatialAffine.responseFactor,diagonalScores,field,signPoint,sign]
   ring

 theorem conditional_mean (t : ℝ) :
     (S.probabilityLaw t:Measure (Model.Observation A BoundedResponse))[
       ((Subtype.val:BoundedResponse→ℝ)∘Prod.snd) | Model.covariateInformation A BoundedResponse] =ᵐ[
         (S.probabilityLaw t:Measure (Model.Observation A BoundedResponse))]
         fun o=>clampedParameter t*S.phi o.1 := by
   have he := SpatialAffine.law_conditional_snd diagonalScores (S.field t) (S.field_small t)
     (Subtype.val:BoundedResponse→ℝ) measurable_subtype_coe 1 (by norm_num) response_bound
   simpa only [responseMoment_mean,Function.comp_def,probabilityLaw,densityLaw,
     GeneralTesting.DensityLaw.probabilityMeasure,ProbabilityMeasure.coe_mk,Model.covariateInformation] using he

 theorem responseMean_zero (t : ℝ) : responseMean A (S.probabilityLaw t)=0 := by
   have he := SpatialAffine.law_integral_snd diagonalScores (S.field t) (S.field_small t)
     (Subtype.val:BoundedResponse→ℝ) measurable_subtype_coe 1 response_bound univ MeasurableSet.univ
   simp only [responseMoment_mean,preimage_univ,Measure.restrict_univ] at he
   simpa only [field,one_mul,integral_const_mul,S.phi_mean,mul_zero,
     probabilityLaw,densityLaw,GeneralTesting.DensityLaw.probabilityMeasure,
     ProbabilityMeasure.coe_mk,responseMean,responseSecondMoment] using he

 theorem responseSecondMoment_one (t : ℝ) : responseSecondMoment A (S.probabilityLaw t)=1 := by
   have hb (z : BoundedResponse) : |(z:ℝ)^2|≤1 := by
     have hz:=response_bound z
     rw [abs_of_nonneg (sq_nonneg _)]
     nlinarith [abs_le.mp hz]
   have he := SpatialAffine.law_integral_snd diagonalScores (S.field t) (S.field_small t)
     (fun z : BoundedResponse=>(z:ℝ)^2) (measurable_subtype_coe.pow_const 2) 1 hb univ MeasurableSet.univ
   simp only [responseMoment_square,preimage_univ,Measure.restrict_univ] at he
   simpa only [field,one_mul,integral_const,probReal_univ,one_smul,
     probabilityLaw,densityLaw,GeneralTesting.DensityLaw.probabilityMeasure,
     ProbabilityMeasure.coe_mk,responseMean,responseSecondMoment] using he

 theorem responseVariance_one (t : ℝ) : responseVariance A (S.probabilityLaw t)=1 := by
   rw [responseVariance_identity,S.responseSecondMoment_one,S.responseMean_zero]
   norm_num

 theorem quadraticTarget_value (t : ℝ) : quadraticTarget A (S.probabilityLaw t)=
     (clampedParameter t)^2*S.eta^2/2 := by
   unfold quadraticTarget
   have hs := S.conditional_mean t
   have hs2 := hs.fun_comp (fun y : ℝ=>y^2)
   simp only [Function.comp_def] at hs2 ⊢
   rw [integral_congr_ae hs2]
   have he := SpatialAffine.law_integral_fst diagonalScores (S.field t) (S.field_small t)
     (fun x=> (clampedParameter t*S.phi x)^2) ((measurable_const.mul S.phi_smooth.continuous.measurable).pow_const 2) univ MeasurableSet.univ
   simp only [preimage_univ,Measure.restrict_univ] at he
   change (∫ o,(clampedParameter t*S.phi o.1)^2 ∂(SpatialAffine.law diagonalScores (S.field t) (S.field_small t)).measure) = ∫ x,1*(clampedParameter t*S.phi x)^2 ∂Model.cubeVolume A.d at he
   simp only [one_mul] at he
   change (∫ o, (clampedParameter t*S.phi o.1)^2 ∂(SpatialAffine.law diagonalScores (S.field t) (S.field_small t)).measure)=_
   rw [he]
   simp_rw [mul_pow]
   rw [integral_const_mul,S.phi_square]
   ring

 theorem explainedTarget_value (t : ℝ) : explainedTarget A (S.probabilityLaw t)=
     (clampedParameter t)^2*S.eta^2/2 := by
   rw [explainedTarget_identity,S.quadraticTarget_value,S.responseMean_zero]
   simp

 theorem scaled_holder (t : ℝ) :
     (fun x=>clampedParameter t*S.phi x)∈Model.holderBall A.α A.H := by
   have he := Model.holderNorm_const_mul_le S.phi A.α (A.H/2) (clampedParameter t)
     A.hα (by have:=A.hH; positivity) S.phi_smooth S.holder
   have hb : 2*|clampedParameter t| *(A.H/2)≤A.H := by
     have hp:=clampedParameter_bound t
     have hH:=A.hH
     nlinarith
   exact he.trans (ENNReal.ofReal_le_ofReal hb)

 theorem quadraticClass_member (hab : A.α=A.β) (hlo : A.gminus≤1) (hhi : 1≤A.gplus) (t : ℝ) :
     S.probabilityLaw t∈quadraticClass A := by
   refine ⟨{
     p:=fun _=>1
     mU:=fun x=>clampedParameter t*S.phi x
     mV:=fun x=>clampedParameter t*S.phi x
     measurableP:=measurable_const
     measurableU:=measurable_const.mul S.phi_smooth.continuous.measurable
     measurableV:=measurable_const.mul S.phi_smooth.continuous.measurable
     nonnegativeP:=ae_of_all _ (fun _=>zero_le_one)
     marginal:=SpatialAffine.law_marginal diagonalScores (S.field t) (S.field_small t)
     momentU:=S.conditional_mean t
     momentV:=S.conditional_mean t
     smoothU:=S.scaled_holder t
     smoothV:=by rw [←hab]; exact S.scaled_holder t
     densityBounds:=ae_of_all _ (fun _=>⟨hlo,hhi⟩) }⟩

 end SineSetup
end RoughRegime.Applications.Products
