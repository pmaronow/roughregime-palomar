module

public import RoughRegime.ApplicationSeparatedMAR


@[expose] public section
/-! Actual pilot normalization of the missing-data observation. The response
records the covariate copy so that the normalized observables remain functions
of the response, as required by the generic experiment. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.SeparatedMAR

abbrev NormalizedResponse (d : ℕ) := Model.Covariate d × Response

def liftObservation (d : ℕ) (o : Model.Covariate d × Response) :
    Model.Covariate d × NormalizedResponse d := (o.1,o)

theorem liftObservation_measurable (d : ℕ) : Measurable (liftObservation d) :=
  measurable_fst.prodMk measurable_id

def normalizedLaw (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × Response)) :
    ProbabilityMeasure (Model.Covariate d × NormalizedResponse d) :=
  P.map (liftObservation d)

theorem normalizedLaw_measure (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × Response)) :
    (normalizedLaw d P : Measure (Model.Covariate d × NormalizedResponse d)) =
      (P : Measure (Model.Covariate d × Response)).map (liftObservation d) := rfl

def normalizedD (d : ℕ) (h : Model.Covariate d → ℝ) (z : NormalizedResponse d) : ℝ :=
  MAR.observed z.2 / h z.1

def normalizedV (d : ℕ) (h : Model.Covariate d → ℝ) (z : NormalizedResponse d) : ℝ :=
  MAR.observedOutcome z.2 / h z.1

theorem normalizedD_measurable (d : ℕ) (h : Model.Covariate d → ℝ) (hh : Measurable h) :
    Measurable (normalizedD d h) :=
  (MAR.observed_measurable.comp measurable_snd).div (hh.comp measurable_fst)

theorem normalizedV_measurable (d : ℕ) (h : Model.Covariate d → ℝ) (hh : Measurable h) :
    Measurable (normalizedV d h) :=
  (MAR.observedOutcome_measurable.comp measurable_snd).div (hh.comp measurable_fst)

def normalizedObservables (A : Model.Parameters) (h : Model.Covariate A.d → ℝ)
    (hh : Measurable h) (e : ℝ) (he : 0<e) (hlower : ∀ x,e≤h x)
    (hM : 1≤A.M0) (hMinv : 1/e≤A.M0) : Model.Observables (NormalizedResponse A.d) A where
  D := normalizedD A.d h
  U _ := 1
  V := normalizedV A.d h
  W _ := 0
  lam := 1
  hlam := one_ne_zero
  measurableD := normalizedD_measurable A.d h hh
  measurableU := measurable_const
  measurableV := normalizedV_measurable A.d h hh
  measurableW := measurable_const
  boundD z := by
    have hp := he.trans_le (hlower z.1)
    have hr := MAR.observed_range z.2
    refine ⟨div_nonneg hr.1 hp.le,?_⟩
    exact ((div_le_div_of_nonneg_right hr.2 hp.le).trans
      (one_div_le_one_div_of_le he (hlower z.1))).trans hMinv
  boundU _ := by simpa only [abs_one] using hM
  boundV z := by
    have hp := he.trans_le (hlower z.1)
    have hr := MAR.observedOutcome_range z.2
    change |MAR.observedOutcome z.2 / h z.1|≤A.M0
    rw [abs_of_nonneg (div_nonneg hr.1 hp.le)]
    exact ((div_le_div_of_nonneg_right hr.2 hp.le).trans
      (one_div_le_one_div_of_le he (hlower z.1))).trans hMinv
  boundW := ⟨0,le_rfl,fun _ => by simp⟩

/-- The true conditional moment after covariate-copy normalization. -/
theorem normalized_conditional (d : ℕ)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (h : Model.Covariate d → ℝ) (hh : Measurable h)
    (f : Response → ℝ) (hf : Measurable f) (g : Model.Covariate d → ℝ) (hg : Measurable g)
    (hfi : Integrable (f ∘ Prod.snd) μ)
    (hni : Integrable (fun o => (h o.1)⁻¹*f o.2) μ)
    (hc : μ[f ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ]
      g ∘ Prod.fst) :
    (μ.map (liftObservation d))[(fun o => f o.2.2/h o.2.1) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ.map (liftObservation d)]
      fun o => g o.1/h o.1 := by
  have hinfo : MeasurableSpace.comap (liftObservation d)
      (MeasurableSpace.comap Prod.fst inferInstance) =
      MeasurableSpace.comap (@Prod.fst (Model.Covariate d) Response) inferInstance := by
    rw [MeasurableSpace.comap_comp]
    rfl
  have hhm : @Measurable (Model.Covariate d × Response) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance (fun o => (h o.1)⁻¹) :=
    hh.inv.comp (measurable_iff_comap_le.mpr le_rfl)
  have hp := condExp_mul_of_stronglyMeasurable_left hhm.stronglyMeasurable hni hfi
  have hweighted : μ[(fun o => f o.2/h o.1) |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] fun o => g o.1/h o.1 := by
    filter_upwards [hp,hc] with o ho he
    change μ[(fun o => (h o.1)⁻¹*f o.2) | _] o =
      (h o.1)⁻¹*(μ[f ∘ Prod.snd | _] o) at ho
    simp only [Function.comp_apply] at he
    rw [he] at ho
    simpa only [div_eq_mul_inv,mul_comm] using ho
  have hgm : @Measurable (Model.Covariate d × NormalizedResponse d) ℝ
      (MeasurableSpace.comap Prod.fst inferInstance) inferInstance
      (fun o => g o.1/h o.1) :=
    (hg.div hh).comp (measurable_iff_comap_le.mpr le_rfl)
  apply conditional_map μ (liftObservation d) (liftObservation_measurable d)
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (fun o => f o.2.2/h o.2.1) (fun o => g o.1/h o.1)
    ((hf.comp (measurable_snd.comp measurable_snd)).div
      (hh.comp (measurable_fst.comp measurable_snd))) hgm
  · simpa only [Function.comp_def,liftObservation,div_eq_mul_inv,mul_comm] using hni
  · simpa only [hinfo,Function.comp_def,liftObservation] using hweighted

/-- The moment data used by normalization, independent of smoothness radii
and the design interval. -/
structure Moments (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × Response)) where
  p : Model.Covariate d → ℝ
  w : Model.Covariate d → ℝ
  b : Model.Covariate d → ℝ
  measurableP : Measurable p
  measurableW : Measurable w
  measurableB : Measurable b
  nonnegativeP : 0≤ᵐ[Model.cubeVolume d] p
  marginal : (P : Measure (Model.Covariate d × Response)).map Prod.fst =
    (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))
  momentD : (P : Measure (Model.Covariate d × Response))[
    MAR.observed ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      (P : Measure (Model.Covariate d × Response))] w ∘ Prod.fst
  momentV : (P : Measure (Model.Covariate d × Response))[
    MAR.observedOutcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      (P : Measure (Model.Covariate d × Response))] fun o => w o.1*b o.1

def Witness.moments (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) :
    Moments A.d P where
  p := W.p
  w := W.w
  b := W.b
  measurableP := W.measurableP
  measurableW := W.measurableW
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := W.momentD
  momentV := W.momentV

theorem normalized_moment_integrable (d : ℕ)
    (μ : Measure (Model.Covariate d × Response)) [IsProbabilityMeasure μ]
    (h : Model.Covariate d → ℝ) (hh : Measurable h)
    (e : ℝ) (he : 0<e) (hlower : ∀ x,e≤h x)
    (f : Response → ℝ) (hf : Measurable f) (hrange : ∀ z,f z ∈ Icc (0:ℝ) 1) :
    Integrable (fun o => (h o.1)⁻¹*f o.2) μ := by
  have hi : Integrable (fun o => f o.2/h o.1) μ := by
    apply Integrable.of_mem_Icc 0 (1/e)
    · exact ((hf.comp measurable_snd).div (hh.comp measurable_fst)).aemeasurable
    · apply Filter.Eventually.of_forall
      intro o
      have hp := he.trans_le (hlower o.1)
      exact ⟨div_nonneg (hrange o.2).1 hp.le,
        (div_le_div_of_nonneg_right (hrange o.2).2 hp.le).trans
          (one_div_le_one_div_of_le he (hlower o.1))⟩
  simpa only [div_eq_mul_inv,mul_comm] using hi

/-- The normalized law satisfies every generic model condition once the
actual normalized Holder and density bounds have been established. -/
def Moments.normalizedModel (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Moments A.d P)
    (h : Model.Covariate A.d → ℝ) (hh : Measurable h)
    (e : ℝ) (he : 0<e) (hlower : ∀ x,e≤h x)
    (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
    (hoverlap : ∀ᵐ x ∂Model.cubeVolume A.d,A.δ≤W.w x/h x)
    (hsmoothA : (fun x => h x/W.w x) ∈ Model.holderBall A.α A.H)
    (hsmoothB : W.b ∈ Model.holderBall A.β A.H)
    (hdensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus≤W.w x/h x*W.p x ∧ W.w x/h x*W.p x≤A.gplus) :
    Model.ModelWitness A (normalizedObservables A h hh e he hlower hM hMinv)
      (normalizedLaw A.d P) where
  p := W.p
  w x := W.w x/h x
  a x := h x/W.w x
  b := W.b
  measurableP := W.measurableP
  measurableW := W.measurableW.div hh
  measurableA := hh.div W.measurableW
  measurableB := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := by
    rw [normalizedLaw_measure,Measure.map_map measurable_fst (liftObservation_measurable A.d)]
    exact W.marginal
  momentD := by
    rw [normalizedLaw_measure]
    apply normalized_conditional A.d (P : Measure (Model.Covariate A.d × Response))
      h hh MAR.observed MAR.observed_measurable W.w W.measurableW
    · exact Integrable.of_mem_Icc 0 1
        (MAR.observed_measurable.comp measurable_snd).aemeasurable
        (Filter.Eventually.of_forall (fun o => MAR.observed_range o.2))
    · exact normalized_moment_integrable A.d _ h hh e he hlower
        MAR.observed MAR.observed_measurable MAR.observed_range
    · exact W.momentD
  momentU := by
    have hm : Model.covariateInformation A (NormalizedResponse A.d) ≤
        (inferInstance : MeasurableSpace (Model.Covariate A.d × NormalizedResponse A.d)) :=
      measurable_fst.comap_le
    have hw : ∀ᵐ o ∂(normalizedLaw A.d P : Measure (Model.Covariate A.d × NormalizedResponse A.d)),
        A.δ≤W.w o.1/h o.1 := by
      apply ae_of_ae_map (f := Prod.fst) (p := fun x => A.δ≤W.w x/h x)
        measurable_fst.aemeasurable
      rw [normalizedLaw_measure,Measure.map_map measurable_fst (liftObservation_measurable A.d)]
      change ∀ᵐ x ∂(P : Measure (Model.Covariate A.d × Response)).map Prod.fst,
        A.δ≤W.w x/h x
      rw [W.marginal]
      exact hoverlap.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
    change (normalizedLaw A.d P : Measure (Model.Covariate A.d × NormalizedResponse A.d))[
      (fun _ => (1:ℝ)) | Model.covariateInformation A (NormalizedResponse A.d)] =ᵐ[_]
      fun o => (W.w o.1/h o.1)*(h o.1/W.w o.1)
    rw [condExp_const hm]
    filter_upwards [hw] with o ho
    have hhn : h o.1 ≠ 0 := ne_of_gt (he.trans_le (hlower o.1))
    have hwn : W.w o.1 ≠ 0 := by
      intro hz
      rw [hz,zero_div] at ho
      exact (not_le_of_gt A.hδ) ho
    field_simp
  momentV := by
    rw [normalizedLaw_measure]
    have hi : Integrable (MAR.observedOutcome ∘ Prod.snd)
        (P : Measure (Model.Covariate A.d × Response)) :=
      Integrable.of_mem_Icc 0 1 (MAR.observedOutcome_measurable.comp measurable_snd).aemeasurable
        (Filter.Eventually.of_forall (fun o => MAR.observedOutcome_range o.2))
    have hn := normalized_moment_integrable A.d
      (P : Measure (Model.Covariate A.d × Response)) h hh e he hlower
      MAR.observedOutcome MAR.observedOutcome_measurable MAR.observedOutcome_range
    have hc := normalized_conditional A.d (P : Measure (Model.Covariate A.d × Response))
      h hh MAR.observedOutcome MAR.observedOutcome_measurable (fun x => W.w x*W.b x)
      (W.measurableW.mul W.measurableB) hi hn W.momentV
    filter_upwards [hc] with o ho
    calc
      _ = W.w o.1*W.b o.1/h o.1 := ho
      _ = (W.w o.1/h o.1)*W.b o.1 := by ring
  overlap := hoverlap
  smoothA := hsmoothA
  smoothB := hsmoothB
  densityBounds := hdensity

theorem Moments.normalizedModel_target_eq_mean (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Moments A.d P)
    (h : Model.Covariate A.d → ℝ) (hh : Measurable h)
    (e : ℝ) (he : 0<e) (hlower : ∀ x,e≤h x)
    (hM : 1≤A.M0) (hMinv : 1/e≤A.M0)
    (hoverlap : ∀ᵐ x ∂Model.cubeVolume A.d,A.δ≤W.w x/h x)
    (hsmoothA : (fun x => h x/W.w x) ∈ Model.holderBall A.α A.H)
    (hsmoothB : W.b ∈ Model.holderBall A.β A.H)
    (hdensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      A.gminus≤W.w x/h x*W.p x ∧ W.w x/h x*W.p x≤A.gplus) :
    Model.target A (normalizedObservables A h hh e he hlower hM hMinv) (normalizedLaw A.d P) =
      ∫ o, W.b o.1 ∂(P : Measure (Model.Covariate A.d × Response)) := by
  let O := normalizedObservables A h hh e he hlower hM hMinv
  let WM := W.normalizedModel A P h hh e he hlower hM hMinv hoverlap hsmoothA hsmoothB hdensity
  have ht : Model.target A O (normalizedLaw A.d P) =
      ∫ o, W.b o.1 ∂(normalizedLaw A.d P : Measure (Model.Covariate A.d × NormalizedResponse A.d)) := by
    rw [Model.target_weighted_representation A O _ WM,
      Model.marginal_integral A O _ WM W.b W.measurableB]
    simp only [O,normalizedObservables,WM,Moments.normalizedModel,
      integral_zero,zero_add,one_mul]
    apply integral_congr_ae
    filter_upwards [hoverlap] with x hx
    have hhn : h x ≠ 0 := ne_of_gt (he.trans_le (hlower x))
    have hwn : W.w x ≠ 0 := by
      intro hz
      rw [hz,zero_div] at hx
      exact (not_le_of_gt A.hδ) hx
    field_simp
  rw [ht,normalizedLaw_measure]
  change (∫ o, (W.b ∘ Prod.fst) o ∂(P : Measure _).map (liftObservation A.d)) = _
  rw [integral_map (liftObservation_measurable A.d).aemeasurable
    (W.measurableB.comp measurable_fst).aestronglyMeasurable]
  rfl

end RoughRegime.Applications.SeparatedMAR
