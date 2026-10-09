module

public import RoughRegime.SpatialAffineLaw
public import RoughRegime.HolderConstants


@[expose] public section
/-! Actual conditional-response witnesses and target identities for the
spatial affine observation laws used in the hard-prior embedding. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false

variable (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
  (O : Model.Observables Z A) (π : ProbabilityMeasure Z)
  (S : Scores (π : Measure Z)) (F : Field (Model.cubeVolume A.d))
  (hsmall : F.epsilon*S.C ≤ 1/4)

 theorem model_target_split :
     Model.target A O (law S F hsmall).probabilityMeasure =
       (∫ x, F.p x*responseMoment S F O.W x ∂Model.cubeVolume A.d) + O.lam *
       ∫ x, F.p x*(responseMoment S F O.U x*responseMoment S F O.V x /
         responseMoment S F O.D x) ∂Model.cubeVolume A.d := by
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   have hD := law_conditional_snd S F hsmall O.D O.measurableD A.M0 A.hM0.le hDb
   have hU := law_conditional_snd S F hsmall O.U O.measurableU A.M0 A.hM0.le O.boundU
   have hV := law_conditional_snd S F hsmall O.V O.measurableV A.M0 A.hM0.le O.boundV
   obtain ⟨MW,hMW,hWb⟩ := O.boundW
   have hW := law_integral_snd S F hsmall O.W O.measurableW MW hWb univ MeasurableSet.univ
   simp only [preimage_univ,Measure.restrict_univ] at hW
   have he : (∫ o, ((law S F hsmall).measure[O.U ∘ Prod.snd | Model.covariateInformation A Z]) o *
       ((law S F hsmall).measure[O.V ∘ Prod.snd | Model.covariateInformation A Z]) o /
       ((law S F hsmall).measure[O.D ∘ Prod.snd | Model.covariateInformation A Z]) o ∂(law S F hsmall).measure) =
       ∫ o, responseMoment S F O.U o.1*responseMoment S F O.V o.1/responseMoment S F O.D o.1 ∂(law S F hsmall).measure := by
     apply integral_congr_ae
     filter_upwards [hU,hV,hD] with o hu hv hd
     rw [hu,hv,hd]
     rfl
   have hmeas : Measurable (fun x => responseMoment S F O.U x*responseMoment S F O.V x/responseMoment S F O.D x) :=
     ((responseMoment_measurable S F O.U O.measurableU).mul
       (responseMoment_measurable S F O.V O.measurableV)).div
       (responseMoment_measurable S F O.D O.measurableD)
   have hI := law_integral_fst S F hsmall _ hmeas univ MeasurableSet.univ
   simp only [preimage_univ,Measure.restrict_univ] at hI
   unfold Model.target
   exact congrArg₂ (fun a b : ℝ => a+b) hW (congrArg (fun r : ℝ => O.lam*r) (he.trans hI))

 def modelWitness
     (hw : ∀ x, A.δ ≤ responseMoment S F O.D x)
     (ha : (fun x => responseMoment S F O.U x/responseMoment S F O.D x) ∈ Model.holderBall A.α A.H)
     (hb : (fun x => responseMoment S F O.V x/responseMoment S F O.D x) ∈ Model.holderBall A.β A.H)
     (hg : ∀ x, A.gminus ≤ responseMoment S F O.D x*F.p x ∧ responseMoment S F O.D x*F.p x ≤ A.gplus) :
     Model.ModelWitness A O (law S F hsmall).probabilityMeasure where
   p := F.p
   w := responseMoment S F O.D
   a x := responseMoment S F O.U x/responseMoment S F O.D x
   b x := responseMoment S F O.V x/responseMoment S F O.D x
   measurableP := F.measurableP
   measurableW := responseMoment_measurable S F O.D O.measurableD
   measurableA := (responseMoment_measurable S F O.U O.measurableU).div (responseMoment_measurable S F O.D O.measurableD)
   measurableB := (responseMoment_measurable S F O.V O.measurableV).div (responseMoment_measurable S F O.D O.measurableD)
   nonnegativeP := Filter.Eventually.of_forall fun x => (F.densityBounds x).1
   marginal := law_marginal S F hsmall
   momentD := law_conditional_snd S F hsmall O.D O.measurableD A.M0 A.hM0.le
     (fun z => by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2)
   momentU := by
     filter_upwards [law_conditional_snd S F hsmall O.U O.measurableU A.M0 A.hM0.le O.boundU] with o ho
     change (law S F hsmall).measure[O.U ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o =
       responseMoment S F O.D o.1*(responseMoment S F O.U o.1/responseMoment S F O.D o.1)
     rw [ho]
     change responseMoment S F O.U o.1 = _
     field_simp [(ne_of_gt (A.hδ.trans_le (hw o.1)))]
   momentV := by
     filter_upwards [law_conditional_snd S F hsmall O.V O.measurableV A.M0 A.hM0.le O.boundV] with o ho
     change (law S F hsmall).measure[O.V ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o =
       responseMoment S F O.D o.1*(responseMoment S F O.V o.1/responseMoment S F O.D o.1)
     rw [ho]
     change responseMoment S F O.V o.1 = _
     field_simp [(ne_of_gt (A.hδ.trans_le (hw o.1)))]
   overlap := Filter.Eventually.of_forall hw
   smoothA := ha
   smoothB := hb
   densityBounds := Filter.Eventually.of_forall hg

 theorem law_mem_localClass
     (hw : ∀ x, A.δ ≤ responseMoment S F O.D x)
     (ha : (fun x => responseMoment S F O.U x/responseMoment S F O.D x) ∈ Model.holderBall A.α A.H)
     (hb : (fun x => responseMoment S F O.V x/responseMoment S F O.D x) ∈ Model.holderBall A.β A.H)
     (hg : ∀ x, A.gminus ≤ responseMoment S F O.D x*F.p x ∧ responseMoment S F O.D x*F.p x ≤ A.gplus)
     (r : ℝ) (hnear : ∀ x, |responseMoment S F O.D x-Model.baselineW A O π| ≤ r ∧
       |responseMoment S F O.U x/responseMoment S F O.D x-Model.baselineA A O π| ≤ r ∧
       |responseMoment S F O.V x/responseMoment S F O.D x-Model.baselineB A O π| ≤ r) :
     (law S F hsmall).probabilityMeasure ∈ Model.localClass A O π r := by
   exact ⟨modelWitness A O π S F hsmall hw ha hb hg, Filter.Eventually.of_forall hnear⟩

 include hsmall in
 theorem responseMoment_D_lower (_hbase : 0 < Model.baselineW A O π) (x : Model.Covariate A.d) :
     Model.baselineW A O π/2 ≤ responseMoment S F O.D x := by
   have he := AffineResponseLower.densityLaw_bounded_mean_lower (π : Measure Z)
     (conditionalLaw S F hsmall x) O.D O.measurableD A.M0 (1/2) A.hM0.le
     (fun z => (O.boundD z).1) (fun z => (O.boundD z).2)
     (Filter.Eventually.of_forall fun z => (responseFactor_bounds S F hsmall x z).1)
   rw [conditionalLaw_moment] at he
   change (1/2)*Model.baselineW A O π ≤ responseMoment S F O.D x at he
   linarith

 def affineMean (f : Z → ℝ) (u v : ℝ) : ℝ :=
   (∫ z, f z ∂(π : Measure Z)) + u*(∫ z, f z*S.su z ∂(π : Measure Z)) +
     v*(∫ z, f z*S.sv z ∂(π : Measure Z))

 def affineIntegrand (u v : ℝ) : ℝ :=
   affineMean π S O.W u v + O.lam*(affineMean π S O.U u v*affineMean π S O.V u v/affineMean π S O.D u v)

 theorem bounded_responseMoment_eq_affineMean (f : Z → ℝ) (hf : Measurable f) (C : ℝ)
     (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) (x : Model.Covariate A.d) :
     responseMoment S F f x = affineMean π S f (F.u x) (F.v x) := by
   exact responseMoment_affine S F f (AffineResponseLower.score_integrable (π : Measure Z) f hf C hbound)
     (AffineResponseLower.bounded_score_product_integrable (π : Measure Z) f S.su hf S.measurableU
       C S.C hC S.nonnegativeC hbound S.boundU)
     (AffineResponseLower.bounded_score_product_integrable (π : Measure Z) f S.sv hf S.measurableV
       C S.C hC S.nonnegativeC hbound S.boundV) x

 theorem model_target_integral (hbase : 0 < Model.baselineW A O π) :
     Model.target A O (law S F hsmall).probabilityMeasure =
       ∫ x, F.p x*affineIntegrand A O π S (F.u x) (F.v x) ∂Model.cubeVolume A.d := by
   let R := fun x => responseMoment S F O.U x*responseMoment S F O.V x/responseMoment S F O.D x
   have hmR : Measurable R := ((responseMoment_measurable S F O.U O.measurableU).mul
     (responseMoment_measurable S F O.V O.measurableV)).div (responseMoment_measurable S F O.D O.measurableD)
   have hR (x : Model.Covariate A.d) : |R x| ≤ A.M0^2/(Model.baselineW A O π/2) := by
     have hd := responseMoment_D_lower A O π S F hsmall hbase x
     have hd0 : 0 < responseMoment S F O.D x := (by linarith : 0 < Model.baselineW A O π/2).trans_le hd
     dsimp [R]
     rw [abs_div,abs_mul,abs_of_pos hd0]
     apply div_le_div₀ (by positivity)
       (show |responseMoment S F O.U x| * |responseMoment S F O.V x| ≤ A.M0^2 from by
         have he := mul_le_mul (responseMoment_bound S F hsmall O.U A.M0 A.hM0.le O.boundU x)
           (responseMoment_bound S F hsmall O.V A.M0 A.hM0.le O.boundV x) (abs_nonneg _) A.hM0.le
         simpa only [pow_two] using he)
       (by linarith) hd
   have hRi : Integrable (fun x => F.p x*R x) (Model.cubeVolume A.d) := by
     apply Integrable.of_bound (F.measurableP.mul hmR).aestronglyMeasurable
       (F.P*(A.M0^2/(Model.baselineW A O π/2)))
     filter_upwards [] with x
     change |F.p x*R x| ≤ _
     rw [abs_mul,abs_of_nonneg (F.densityBounds x).1]
     exact mul_le_mul (F.densityBounds x).2 (hR x) (abs_nonneg _) F.nonnegativeP
   obtain ⟨MW,hMW,hWb⟩ := O.boundW
   have hWi : Integrable (fun x => F.p x*responseMoment S F O.W x) (Model.cubeVolume A.d) := by
     apply Integrable.of_bound (F.measurableP.mul (responseMoment_measurable S F O.W O.measurableW)).aestronglyMeasurable (F.P*MW)
     filter_upwards [] with x
     change |F.p x*responseMoment S F O.W x| ≤ _
     rw [abs_mul,abs_of_nonneg (F.densityBounds x).1]
     exact mul_le_mul (F.densityBounds x).2 (responseMoment_bound S F hsmall O.W MW hMW hWb x) (abs_nonneg _) F.nonnegativeP
   have hDb (z : Z) : |O.D z| ≤ A.M0 := by rw [abs_of_nonneg (O.boundD z).1]; exact (O.boundD z).2
   have he : (fun x => F.p x*affineIntegrand A O π S (F.u x) (F.v x)) =
       (fun x => F.p x*responseMoment S F O.W x) + (fun x => O.lam*(F.p x*R x)) := by
     funext x
     dsimp [affineIntegrand,R]
     rw [← bounded_responseMoment_eq_affineMean A π S F O.W O.measurableW MW hMW hWb x,
       ← bounded_responseMoment_eq_affineMean A π S F O.U O.measurableU A.M0 A.hM0.le O.boundU x,
       ← bounded_responseMoment_eq_affineMean A π S F O.V O.measurableV A.M0 A.hM0.le O.boundV x,
       ← bounded_responseMoment_eq_affineMean A π S F O.D O.measurableD A.M0 A.hM0.le hDb x]
     ring
   rw [he]
   change Model.target A O (law S F hsmall).probabilityMeasure =
     ∫ x, F.p x*responseMoment S F O.W x+O.lam*(F.p x*R x) ∂Model.cubeVolume A.d
   rw [integral_add hWi (hRi.const_mul O.lam),integral_const_mul,model_target_split A O π S F hsmall]


end RoughRegime.SpatialAffine
