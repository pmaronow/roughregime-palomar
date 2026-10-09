module

public import RoughRegime.BaselineScores
public import RoughRegime.UniformCube


@[expose] public section
/-! The genuine observation law with a spatial density and an affine
conditional response law. All normalizations are derived from score means. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

structure Scores {Z : Type*} [MeasurableSpace Z] (π : Measure Z) where
  su : Z → ℝ
  sv : Z → ℝ
  measurableU : Measurable su
  measurableV : Measurable sv
  C : ℝ
  nonnegativeC : 0 ≤ C
  boundU : ∀ z, |su z| ≤ C
  boundV : ∀ z, |sv z| ≤ C
  meanU : (∫ z, su z ∂π) = 0
  meanV : (∫ z, sv z ∂π) = 0

structure Field {X : Type*} [MeasurableSpace X] (η : Measure X) where
  p : X → ℝ
  u : X → ℝ
  v : X → ℝ
  measurableP : Measurable p
  measurableU : Measurable u
  measurableV : Measurable v
  P : ℝ
  nonnegativeP : 0 ≤ P
  densityBounds : ∀ x, 0 ≤ p x ∧ p x ≤ P
  integralP : (∫ x, p x ∂η) = 1
  epsilon : ℝ
  nonnegativeEpsilon : 0 ≤ epsilon
  boundU : ∀ x, |u x| ≤ epsilon
  boundV : ∀ x, |v x| ≤ epsilon

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  {η : Measure X} {π : Measure Z} [IsProbabilityMeasure η] [IsProbabilityMeasure π]

 def responseFactor (S : Scores π) (F : Field η) (x : X) (z : Z) : ℝ :=
   1 + F.u x*S.su z + F.v x*S.sv z

 omit [IsProbabilityMeasure η] [IsProbabilityMeasure π] in
 theorem responseFactor_measurable (S : Scores π) (F : Field η) :
     Measurable (fun o : X×Z => responseFactor S F o.1 o.2) := by
   unfold responseFactor
   exact ((measurable_const.add ((F.measurableU.comp measurable_fst).mul
     (S.measurableU.comp measurable_snd))).add ((F.measurableV.comp measurable_fst).mul
       (S.measurableV.comp measurable_snd)))

 omit [IsProbabilityMeasure η] in
 theorem responseFactor_integrable (S : Scores π) (F : Field η) (x : X) :
     Integrable (responseFactor S F x) π :=
   ((integrable_const 1).add
     ((AffineResponseLower.score_integrable π S.su S.measurableU S.C S.boundU).const_mul (F.u x))).add
     ((AffineResponseLower.score_integrable π S.sv S.measurableV S.C S.boundV).const_mul (F.v x))

 omit [IsProbabilityMeasure η] in
 theorem responseFactor_integral (S : Scores π) (F : Field η) (x : X) :
     (∫ z, responseFactor S F x z ∂π) = 1 := by
   have hu := AffineResponseLower.score_integrable π S.su S.measurableU S.C S.boundU
   have hv := AffineResponseLower.score_integrable π S.sv S.measurableV S.C S.boundV
   have hsum1 := integral_add (integrable_const (1:ℝ)) (hu.const_mul (F.u x))
   have hsum2 := integral_add ((integrable_const (1:ℝ)).add (hu.const_mul (F.u x))) (hv.const_mul (F.v x))
   simp only [Pi.add_apply] at hsum1 hsum2
   unfold responseFactor
   rw [hsum2, hsum1, integral_const_mul, integral_const_mul, S.meanU, S.meanV]
   simp

 omit [IsProbabilityMeasure η] [IsProbabilityMeasure π] in
 theorem responseFactor_bounds (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (x : X) (z : Z) : 1/2 ≤ responseFactor S F x z ∧ responseFactor S F x z ≤ 3/2 := by
   have hu : |F.u x*S.su z| ≤ F.epsilon*S.C := by
     rw [abs_mul]
     exact mul_le_mul (F.boundU x) (S.boundU z) (abs_nonneg _) F.nonnegativeEpsilon
   have hv : |F.v x*S.sv z| ≤ F.epsilon*S.C := by
     rw [abs_mul]
     exact mul_le_mul (F.boundV x) (S.boundV z) (abs_nonneg _) F.nonnegativeEpsilon
   unfold responseFactor
   constructor <;> nlinarith [neg_le_abs (F.u x*S.su z), le_abs_self (F.u x*S.su z),
     neg_le_abs (F.v x*S.sv z), le_abs_self (F.v x*S.sv z)]

 theorem spatialDensity_integrable (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4) :
     Integrable (fun o : X×Z => F.p o.1*responseFactor S F o.1 o.2) (η.prod π) := by
   apply Integrable.of_bound ((F.measurableP.comp measurable_fst).mul
     (responseFactor_measurable S F)).aestronglyMeasurable (F.P*(3/2))
   filter_upwards [] with o
   change ‖F.p o.1*responseFactor S F o.1 o.2‖ ≤ F.P*(3/2)
   rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (F.densityBounds o.1).1,
     abs_of_nonneg (by linarith [(responseFactor_bounds S F hsmall o.1 o.2).1])]
   exact mul_le_mul (F.densityBounds o.1).2 (responseFactor_bounds S F hsmall o.1 o.2).2
     (by linarith [(responseFactor_bounds S F hsmall o.1 o.2).1]) F.nonnegativeP

 def law (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4) :
     GeneralTesting.DensityLaw (η.prod π) where
   density o := F.p o.1*responseFactor S F o.1 o.2
   measurable := (F.measurableP.comp measurable_fst).mul (responseFactor_measurable S F)
   integrable := spatialDensity_integrable S F hsmall
   nonneg := Filter.Eventually.of_forall fun o => mul_nonneg (F.densityBounds o.1).1
     (by linarith [(responseFactor_bounds S F hsmall o.1 o.2).1])
   integral_one := by
     rw [integral_prod _ (spatialDensity_integrable S F hsmall)]
     simp_rw [integral_const_mul, responseFactor_integral, mul_one]
     exact F.integralP

 theorem law_density_nonnegative (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (o : X×Z) : 0 ≤ (law S F hsmall).density o :=
   mul_nonneg (F.densityBounds o.1).1 (by linarith [(responseFactor_bounds S F hsmall o.1 o.2).1])

 theorem responseFactor_lintegral (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (x : X) : (∫⁻ z, ENNReal.ofReal (responseFactor S F x z) ∂π) = 1 := by
   rw [← ofReal_integral_eq_lintegral_ofReal (responseFactor_integrable S F x)
     (Filter.Eventually.of_forall fun z => (by norm_num : (0:ℝ) ≤ 1/2).trans
       (responseFactor_bounds S F hsmall x z).1),
     responseFactor_integral]
   exact ENNReal.ofReal_one

 theorem law_marginal (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4) :
     (law S F hsmall).measure.map Prod.fst = η.withDensity (fun x => ENNReal.ofReal (F.p x)) := by
   apply Measure.ext
   intro t ht
   rw [Measure.map_apply measurable_fst ht, GeneralTesting.DensityLaw.measure,
     withDensity_apply _ (ht.preimage measurable_fst), withDensity_apply _ ht]
   have hset : Prod.fst ⁻¹' t = t ×ˢ (univ : Set Z) := by ext x; simp
   rw [hset, ← Measure.restrict_prod_eq_prod_univ]
   rw [lintegral_prod _ ((law S F hsmall).measurable.ennreal_ofReal.aemeasurable)]
   apply lintegral_congr
   intro x
   change (∫⁻ z, ENNReal.ofReal (F.p x*responseFactor S F x z) ∂π) = _
   simp_rw [ENNReal.ofReal_mul (F.densityBounds x).1]
   rw [lintegral_const_mul _ (by have hu := S.measurableU; have hv := S.measurableV; unfold responseFactor; fun_prop), responseFactor_lintegral S F hsmall, mul_one]

 def responseMoment (S : Scores π) (F : Field η) (f : Z → ℝ) (x : X) : ℝ :=
   ∫ z, responseFactor S F x z*f z ∂π

 theorem responseMoment_measurable (S : Scores π) (F : Field η) (f : Z → ℝ) (hf : Measurable f) :
     Measurable (responseMoment S F f) :=
   ((responseFactor_measurable S F).mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

 theorem responseMoment_bound (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (f : Z → ℝ) (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) (x : X) :
     |responseMoment S F f x| ≤ C := by
   have he := norm_integral_le_of_norm_le ((responseFactor_integrable S F x).mul_const C)
     (Filter.Eventually.of_forall fun z => show ‖responseFactor S F x z*f z‖ ≤ responseFactor S F x z*C from by
       rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [(responseFactor_bounds S F hsmall x z).1])]
       exact mul_le_mul_of_nonneg_left (hbound z) (by linarith [(responseFactor_bounds S F hsmall x z).1]))
   simpa only [responseMoment, Real.norm_eq_abs, integral_mul_const, responseFactor_integral, one_mul] using he

 theorem law_integral_snd (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C)
     (t : Set X) (ht : MeasurableSet t) :
     (∫ o in Prod.fst ⁻¹' t, f o.2 ∂(law S F hsmall).measure) =
       ∫ x in t, F.p x*responseMoment S F f x ∂η := by
   have hi : Integrable (fun o : X×Z => (law S F hsmall).density o*f o.2) (η.prod π) :=
     (law S F hsmall).integrable.mul_bdd (hf.comp measurable_snd).aestronglyMeasurable
       (Filter.Eventually.of_forall fun o => by simpa only [Real.norm_eq_abs] using hbound o.2)
   have hset : Prod.fst ⁻¹' t = t ×ˢ (univ : Set Z) := by ext x; simp
   unfold GeneralTesting.DensityLaw.measure
   rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
     ((law S F hsmall).measurable.ennreal_ofReal)
     (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ (ht.preimage measurable_fst)]
   simp_rw [ENNReal.toReal_ofReal (law_density_nonnegative S F hsmall _), smul_eq_mul]
   rw [hset, ← Measure.restrict_prod_eq_prod_univ]
   have hi' : Integrable (fun o : X×Z => (law S F hsmall).density o*f o.2) ((η.restrict t).prod π) := by
     rw [Measure.restrict_prod_eq_prod_univ]
     exact hi.integrableOn
   rw [integral_prod _ hi']
   apply integral_congr_ae
   filter_upwards [] with x
   change (∫ z, (F.p x*responseFactor S F x z)*f z ∂π) = F.p x*responseMoment S F f x
   simp_rw [mul_assoc]
   exact integral_const_mul _ _

 theorem law_integral_fst (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (g : X → ℝ) (hg : Measurable g) (t : Set X) (ht : MeasurableSet t) :
     (∫ o in Prod.fst ⁻¹' t, g o.1 ∂(law S F hsmall).measure) = ∫ x in t, F.p x*g x ∂η := by
   rw [← setIntegral_map ht hg.aestronglyMeasurable measurable_fst.aemeasurable, law_marginal]
   rw [setIntegral_withDensity_eq_setIntegral_toReal_smul F.measurableP.ennreal_ofReal
     (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ ht]
   simp_rw [ENNReal.toReal_ofReal (F.densityBounds _).1, smul_eq_mul]

 theorem law_conditional_snd (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
     (law S F hsmall).measure[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[(law S F hsmall).measure]
       (responseMoment S F f) ∘ Prod.fst := by
   have hm : MeasurableSpace.comap (@Prod.fst X Z) (inferInstance : MeasurableSpace X) ≤ (inferInstance : MeasurableSpace (X×Z)) := measurable_fst.comap_le
   have hfi : Integrable (f ∘ Prod.snd) (law S F hsmall).measure :=
     Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable C
       (Filter.Eventually.of_forall fun o => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hbound o.2)
   have hg := responseMoment_measurable S F f hf
   have hgi : Integrable ((responseMoment S F f) ∘ Prod.fst) (law S F hsmall).measure :=
     Integrable.of_bound (hg.comp measurable_fst).aestronglyMeasurable C
       (Filter.Eventually.of_forall fun o => by simpa only [Real.norm_eq_abs, Function.comp_apply]
         using (responseMoment_bound S F hsmall f C hC hbound o.1))
   have hgm : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
       ((responseMoment S F f) ∘ Prod.fst : X×Z → ℝ) :=
     hg.stronglyMeasurable.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
   apply (ae_eq_condExp_of_forall_setIntegral_eq hm hfi (fun t _ _ => hgi.integrableOn) ?_ hgm.aestronglyMeasurable).symm
   intro t ht _
   obtain ⟨s,hs,rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
   change (∫ o in Prod.fst ⁻¹' s, responseMoment S F f o.1 ∂(law S F hsmall).measure) =
     ∫ o in Prod.fst ⁻¹' s, f o.2 ∂(law S F hsmall).measure
   rw [law_integral_fst S F hsmall _ hg s hs, law_integral_snd S F hsmall f hf C hbound s hs]


 omit [IsProbabilityMeasure η] [IsProbabilityMeasure π] in
 theorem responseMoment_affine (S : Scores π) (F : Field η) (f : Z → ℝ)
     (hf : Integrable f π) (hfu : Integrable (fun z => f z*S.su z) π)
     (hfv : Integrable (fun z => f z*S.sv z) π) (x : X) :
     responseMoment S F f x = (∫ z, f z ∂π) + F.u x*(∫ z, f z*S.su z ∂π) +
       F.v x*(∫ z, f z*S.sv z ∂π) := by
   have he : (fun z => responseFactor S F x z*f z) =
       fun z => f z + F.u x*(f z*S.su z) + F.v x*(f z*S.sv z) := by
     funext z
     unfold responseFactor
     ring
   unfold responseMoment
   rw [he]
   have he1 := integral_add hf (hfu.const_mul (F.u x))
   have he2 := integral_add (hf.add (hfu.const_mul (F.u x))) (hfv.const_mul (F.v x))
   simp only [Pi.add_apply] at he1 he2
   rw [he2, he1, integral_const_mul, integral_const_mul]


 theorem law_measurable {W : Type*} [MeasurableSpace W] (S : Scores π)
     (F : W → Field η) (hsmall : ∀ w, (F w).epsilon*S.C ≤ 1/4)
     (hp : Measurable (fun o : W×X => (F o.1).p o.2))
     (hu : Measurable (fun o : W×X => (F o.1).u o.2))
     (hv : Measurable (fun o : W×X => (F o.1).v o.2)) :
     Measurable (fun w => (law S (F w) (hsmall w)).measure) := by
   apply measurable_withDensity
   have hm : Measurable (fun o : W×(X×Z) => (o.1,o.2.1)) :=
     measurable_fst.prodMk measurable_snd.fst
   have hsu : Measurable (fun o : W×(X×Z) => S.su o.2.2) :=
     S.measurableU.comp measurable_snd.snd
   have hsv : Measurable (fun o : W×(X×Z) => S.sv o.2.2) :=
     S.measurableV.comp measurable_snd.snd
   exact ((hp.comp hm).mul ((measurable_const.add ((hu.comp hm).mul hsu)).add
     ((hv.comp hm).mul hsv))).ennreal_ofReal

 def observationKernel {W : Type*} [MeasurableSpace W] (S : Scores π)
     (F : W → Field η) (hsmall : ∀ w, (F w).epsilon*S.C ≤ 1/4)
     (hp : Measurable (fun o : W×X => (F o.1).p o.2))
     (hu : Measurable (fun o : W×X => (F o.1).u o.2))
     (hv : Measurable (fun o : W×X => (F o.1).v o.2)) : ProbabilityTheory.Kernel W (X×Z) where
   toFun w := (law S (F w) (hsmall w)).measure
   measurable' := law_measurable S F hsmall hp hu hv

 instance observationKernel_markov {W : Type*} [MeasurableSpace W] (S : Scores π)
     (F : W → Field η) (hsmall : ∀ w, (F w).epsilon*S.C ≤ 1/4)
     (hp : Measurable (fun o : W×X => (F o.1).p o.2))
     (hu : Measurable (fun o : W×X => (F o.1).u o.2))
     (hv : Measurable (fun o : W×X => (F o.1).v o.2)) :
     ProbabilityTheory.IsMarkovKernel (observationKernel S F hsmall hp hu hv) where
   isProbabilityMeasure w := (law S (F w) (hsmall w)).isProbabilityMeasure


 def conditionalLaw (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4) (x : X) :
     GeneralTesting.DensityLaw π where
   density := responseFactor S F x
   measurable := (responseFactor_measurable S F).comp (measurable_const.prodMk measurable_id)
   integrable := responseFactor_integrable S F x
   nonneg := Filter.Eventually.of_forall fun z => (by norm_num : (0:ℝ) ≤ 1/2).trans
     (responseFactor_bounds S F hsmall x z).1
   integral_one := responseFactor_integral S F x

 theorem conditionalLaw_moment (S : Scores π) (F : Field η) (hsmall : F.epsilon*S.C ≤ 1/4)
     (x : X) (f : Z → ℝ) :
     (∫ z, f z ∂(conditionalLaw S F hsmall x).measure) = responseMoment S F f x := by
   unfold GeneralTesting.DensityLaw.measure
   rw [integral_withDensity_eq_integral_toReal_smul
     (conditionalLaw S F hsmall x).measurable.ennreal_ofReal
     (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
   simp_rw [ENNReal.toReal_ofReal (show 0 ≤ (conditionalLaw S F hsmall x).density _ from
     (by norm_num : (0:ℝ) ≤ 1/2).trans (responseFactor_bounds S F hsmall x _).1), smul_eq_mul]
   rfl


end RoughRegime.SpatialAffine
