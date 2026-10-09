module

public import RoughRegime.ApplicationOverlapBounds
public import RoughRegime.ApplicationOverlapAffine
public import RoughRegime.ModelReverseRisk


@[expose] public section
/-! Actual target identities and quantitative reverse maps for the overlap
hard families. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Overlap
open RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

 theorem weighted_product_integrable (A : Model.Parameters) (F : Field (Model.cubeVolume A.d))
    (f g : Model.Covariate A.d→ℝ) (hf : Measurable f) (hg : Measurable g)
    (U V : ℝ) (hU : 0≤U) (_hV : 0≤V) (hu : ∀ x,|f x|≤U) (hv : ∀ x,|g x|≤V) :
    Integrable (fun x=>F.p x*f x*g x) (Model.cubeVolume A.d) := by
  apply Integrable.of_bound ((F.measurableP.mul hf).mul hg).aestronglyMeasurable (F.P*U*V)
  filter_upwards [] with x
  change |F.p x*f x*g x|≤_
  rw [abs_mul,abs_mul,abs_of_nonneg (F.densityBounds x).1]
  exact mul_le_mul (mul_le_mul (F.densityBounds x).2 (hu x) (abs_nonneg _) F.nonnegativeP)
    (hv x) (abs_nonneg _) (mul_nonneg F.nonnegativeP hU)
 theorem weighted_product_bound (A : Model.Parameters) (F : Field (Model.cubeVolume A.d))
    (f g : Model.Covariate A.d→ℝ) (hf : Measurable f) (hg : Measurable g)
    (U V : ℝ) (hU : 0≤U) (hV : 0≤V) (hu : ∀ x,|f x|≤U) (hv : ∀ x,|g x|≤V) :
    |∫ x,F.p x*f x*g x ∂Model.cubeVolume A.d|≤U*V := by
  have hp : Integrable F.p (Model.cubeVolume A.d) :=
    AffineResponseLower.score_integrable _ F.p F.measurableP F.P fun x=>by
      rw [abs_of_nonneg (F.densityBounds x).1];exact (F.densityBounds x).2
  have hi := weighted_product_integrable A F f g hf hg U V hU hV hu hv
  calc
    _ ≤ ∫ x,|F.p x*f x*g x| ∂Model.cubeVolume A.d := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>F.p x*f x*g x)
    _ ≤ ∫ x,F.p x*(U*V) ∂Model.cubeVolume A.d := integral_mono hi.abs (hp.mul_const _) fun x=>by
      rw [abs_mul,abs_mul,abs_of_nonneg (F.densityBounds x).1]
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul (hu x) (hv x) (abs_nonneg _) hU) (F.densityBounds x).1]
    _ = _ := by rw [integral_mul_const,F.integralP,one_mul]
 theorem constant_sub_integral (A : Model.Parameters) (F : Field (Model.cubeVolume A.d))
    (a : ℝ) (f : Model.Covariate A.d→ℝ)
    (hi : Integrable (fun x=>F.p x*f x) (Model.cubeVolume A.d)) :
    (∫ x,F.p x*(a-f x) ∂Model.cubeVolume A.d)=a-∫ x,F.p x*f x ∂Model.cubeVolume A.d := by
  have hp : Integrable F.p (Model.cubeVolume A.d) :=
    AffineResponseLower.score_integrable _ F.p F.measurableP F.P fun x=>by
      rw [abs_of_nonneg (F.densityBounds x).1];exact (F.densityBounds x).2
  simp_rw [mul_sub]
  rw [integral_sub (hp.mul_const _) hi,integral_mul_const,F.integralP,one_mul]

 theorem independent_denominator_integral (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*(scores 0 (by norm_num)).C≤1/4) :
    denominator A.d (law (scores 0 (by norm_num)) F hsmall).probabilityMeasure=
      1/4-∫ x,F.p x*(F.u x)^2 ∂Model.cubeVolume A.d := by
  rw [← denominator_target A hM,model_target_integral (diagonalParameters A) (denominatorObservables A hM)
    _ (scores 0 (by norm_num)) F hsmall (by rw [baselineW_one _ _ rfl];norm_num)]
  have hs : (fun z=>treatment z*treatment z)=treatment := by
    funext z;simpa only [pow_two] using treatment_sq z
  have he (u v : ℝ) : affineIntegrand (diagonalParameters A) (denominatorObservables A hM)
      (baseline 0 (by norm_num)) (scores 0 (by norm_num)) u v=1/4-u^2 := by
    change affineMean _ _ (fun z=>treatment z*treatment z) u v+
      (-1)*(affineMean _ _ treatment u v*affineMean _ _ treatment u v/affineMean _ _ (fun _=>1) u v)=_
    rw [hs,affineMean_treatment,affineMean_one];ring
  simp_rw [he]
  apply constant_sub_integral
  simpa only [pow_two,mul_assoc] using weighted_product_integrable A F F.u F.u F.measurableU F.measurableU
    F.epsilon F.epsilon F.nonnegativeEpsilon F.nonnegativeEpsilon F.boundU F.boundU

 theorem independent_numerator_zero (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*(scores 0 (by norm_num)).C≤1/4) :
    numerator A.d (law (scores 0 (by norm_num)) F hsmall).probabilityMeasure=
      -(∫ x,F.p x*F.u x*F.v x ∂Model.cubeVolume A.d) := by
  rw [independent_numerator_integral A hM 0]
  simp only [zero_div,zero_sub,mul_neg,← mul_assoc,integral_neg]

 theorem diagonal_denominator_exact (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*diagonalScores.C≤1/4) :
    denominator A.d (law diagonalScores F hsmall).probabilityMeasure=
      1/4-∫ x,F.p x*(F.u x+F.v x)^2 ∂Model.cubeVolume A.d := by
  rw [diagonal_denominator_integral A hM]
  apply constant_sub_integral
  simpa only [pow_two,mul_assoc,Pi.add_apply] using weighted_product_integrable A F (F.u+F.v) (F.u+F.v)
    (F.measurableU.add F.measurableV) (F.measurableU.add F.measurableV) (2*F.epsilon) (2*F.epsilon)
    (mul_nonneg (by norm_num) F.nonnegativeEpsilon) (mul_nonneg (by norm_num) F.nonnegativeEpsilon)
    (fun x=>(abs_add_le _ _).trans (by linarith [F.boundU x,F.boundV x]))
    (fun x=>(abs_add_le _ _).trans (by linarith [F.boundU x,F.boundV x]))
 theorem independent_denominator_lower (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*(scores 0 (by norm_num)).C≤1/4)
    (U : ℝ) (hU : 0≤U) (hUs : U≤1/4) (hu : ∀ x,|F.u x|≤U) :
    3/16≤denominator A.d (law (scores 0 (by norm_num)) F hsmall).probabilityMeasure := by
  rw [independent_denominator_integral A hM]
  have hb := weighted_product_bound A F F.u F.u F.measurableU F.measurableU U U hU hU hu hu
  simp only [mul_assoc,← pow_two] at hb
  nlinarith [le_abs_self (∫ x,F.p x*(F.u x)^2 ∂Model.cubeVolume A.d)]
 theorem diagonal_denominator_bounds (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*diagonalScores.C≤1/4)
    (hu : ∀ x,|F.u x+F.v x|≤1/4) :
    denominator A.d (law diagonalScores F hsmall).probabilityMeasure∈Icc (3/16) (1/4) := by
  rw [diagonal_denominator_exact A hM]
  have hb := weighted_product_bound A F (F.u+F.v) (F.u+F.v)
    (F.measurableU.add F.measurableV) (F.measurableU.add F.measurableV) (1/4) (1/4)
    (by norm_num) (by norm_num) hu hu
  have hn : 0≤∫ x,F.p x*(F.u x+F.v x)^2 ∂Model.cubeVolume A.d :=
    integral_nonneg fun x=>mul_nonneg (F.densityBounds x).1 (sq_nonneg _)
  have he : (fun x=>F.p x*(F.u x+F.v x)^2)=(fun x=>F.p x*(F.u+F.v) x*(F.u+F.v) x) := by
    funext x;simp only [Pi.add_apply];ring
  rw [← he] at hb
  constructor <;> nlinarith [le_abs_self (∫ x,F.p x*(F.u x+F.v x)^2 ∂Model.cubeVolume A.d)]

 theorem independent_error_scalar (N I D U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (hN : |N|≤U*V) (hI : |I|≤U^2) (hD : 1/8≤D) (he : D=1/4-I) :
    |N-(N/D)/4|≤8*U^3*V := by
  have hd : 0<D := by linarith
  have hde : N-(N/D)/4=-(N*I)/D := by
    field_simp [ne_of_gt hd]
    rw [he];ring
  rw [hde,abs_div,abs_neg,abs_mul,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hp := mul_le_mul hN hI (abs_nonneg _) (mul_nonneg hU hV)
  have hm := mul_le_mul_of_nonneg_left hD (show 0≤8*U^3*V by positivity)
  nlinarith only [hp,hm]

 theorem independent_effect_error (A : Model.Parameters) (hM : 1≤A.M0)
    (F : Field (Model.cubeVolume A.d)) (hsmall : F.epsilon*(scores 0 (by norm_num)).C≤1/4)
    (U V : ℝ) (hU : 0≤U) (hV : 0≤V) (hUs : U≤1/4)
    (hu : ∀ x,|F.u x|≤U) (hv : ∀ x,|F.v x|≤V) :
    |numerator A.d (law (scores 0 (by norm_num)) F hsmall).probabilityMeasure-
      effect A.d (law (scores 0 (by norm_num)) F hsmall).probabilityMeasure/4|≤8*U^3*V := by
  have hn := weighted_product_bound A F F.u F.v F.measurableU F.measurableV U V hU hV hu hv
  have hi := weighted_product_bound A F F.u F.u F.measurableU F.measurableU U U hU hU hu hu
  have hl := independent_denominator_lower A hM F hsmall U hU hUs hu
  apply independent_error_scalar _ (∫ x,F.p x*(F.u x)^2 ∂Model.cubeVolume A.d) _ U V hU hV
  · rw [independent_numerator_zero A hM,abs_neg];exact hn
  · simpa only [pow_two,mul_assoc] using hi
  · linarith
  · exact independent_denominator_integral A hM F hsmall

 theorem diagonal_effect_scalar (D γ : ℝ) (hD : 3/16≤D) (hD' : D≤1/4)
    (hγ : γ=(1/16)/D) : γ∈Icc (1/4) (1/3) ∧ D=1/(16*γ) := by
  have hd : 0<D := by linarith
  constructor
  · rw [hγ]
    constructor
    · apply (le_div_iff₀ hd).mpr;linarith
    · apply (div_le_iff₀ hd).mpr;linarith
  · rw [hγ];field_simp
 theorem reciprocal_lipschitz (a b : Icc (1/4:ℝ) (1/3)) :
    |1/(16*(a:ℝ))-1/(16*(b:ℝ))|≤|(a:ℝ)-b| := by
  have ha : 0<(a:ℝ) := by linarith [a.property.1]
  have hb : 0<(b:ℝ) := by linarith [b.property.1]
  have he : 1/(16*(a:ℝ))-1/(16*(b:ℝ))=((b:ℝ)-a)/(16*(a:ℝ)*b) := by field_simp
  rw [he,abs_div,abs_of_pos (by positivity : 0<16*(a:ℝ)*b),abs_sub_comm]
  apply (div_le_iff₀ (by positivity : 0<16*(a:ℝ)*b)).mpr
  have hprod : 1≤16*(a:ℝ)*b := by nlinarith [mul_le_mul a.property.1 b.property.1 (by norm_num : (0:ℝ)≤1/4) ha.le]
  nlinarith [abs_nonneg ((a:ℝ)-b)]

end RoughRegime.Applications.Overlap
