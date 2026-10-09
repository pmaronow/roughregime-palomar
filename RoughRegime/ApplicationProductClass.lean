module

public import RoughRegime.SampleMeanBound
public import RoughRegime.ConditionalExamples


@[expose] public section
/-! The literal conditional-mean classes for the bilinear and quadratic
applications, and their identification with the generic D=1 model. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace RoughRegime.Applications.Products

structure Witness (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (U V : Z→ℝ) (P : ProbabilityMeasure (Model.Observation A Z)) where
  p : Model.Covariate A.d→ℝ
  mU : Model.Covariate A.d→ℝ
  mV : Model.Covariate A.d→ℝ
  measurableP : Measurable p
  measurableU : Measurable mU
  measurableV : Measurable mV
  nonnegativeP : 0≤ᵐ[Model.cubeVolume A.d] p
  marginal : (P:Measure (Model.Observation A Z)).map Prod.fst=
    (Model.cubeVolume A.d).withDensity (fun x => ENNReal.ofReal (p x))
  momentU : (P:Measure (Model.Observation A Z))[U∘Prod.snd | Model.covariateInformation A Z] =ᵐ[
    (P:Measure (Model.Observation A Z))] mU∘Prod.fst
  momentV : (P:Measure (Model.Observation A Z))[V∘Prod.snd | Model.covariateInformation A Z] =ᵐ[
    (P:Measure (Model.Observation A Z))] mV∘Prod.fst
  smoothU : mU∈Model.holderBall A.α A.H
  smoothV : mV∈Model.holderBall A.β A.H
  densityBounds : ∀ᵐ x ∂Model.cubeVolume A.d, A.gminus≤p x ∧ p x≤A.gplus

def modelClass (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z] (U V : Z→ℝ) :
    Set (ProbabilityMeasure (Model.Observation A Z)) := {P | Nonempty (Witness A U V P)}

def Witness.toModel (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Model.Observables Z A) (hD : F.D=fun _ => 1) (hdelta : A.δ≤1)
    (P : ProbabilityMeasure (Model.Observation A Z)) (W : Witness A F.U F.V P) :
    Model.ModelWitness A F P where
  p := W.p
  w _ := 1
  a := W.mU
  b := W.mV
  measurableP := W.measurableP
  measurableW := measurable_const
  measurableA := W.measurableU
  measurableB := W.measurableV
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentD := by
    rw [hD]
    exact Filter.EventuallyEq.of_eq (condExp_const measurable_fst.comap_le 1)
  momentU := by simpa only [one_mul,Function.comp_def] using W.momentU
  momentV := by simpa only [one_mul,Function.comp_def] using W.momentV
  overlap := ae_of_all _ (fun _ => hdelta)
  smoothA := W.smoothU
  smoothB := W.smoothV
  densityBounds := by simpa only [one_mul] using W.densityBounds

theorem unit_weight {A : Model.Parameters} {Z : Type*} [MeasurableSpace Z]
    {F : Model.Observables Z A} (hD : F.D=fun _ => 1)
    {P : ProbabilityMeasure (Model.Observation A Z)} (W : Model.ModelWitness A F P) :
    ∀ᵐ x ∂Model.cubeVolume A.d, W.w x=1 := by
  have hm : Model.covariateInformation A Z≤(inferInstance:MeasurableSpace (Model.Observation A Z)) :=
    measurable_fst.comap_le
  have he : ∀ᵐ o ∂(P:Measure (Model.Observation A Z)), W.w o.1=1 := by
    have hd := W.momentD
    rw [hD] at hd
    change (P:Measure (Model.Observation A Z))[fun _ => (1:ℝ) | Model.covariateInformation A Z] =ᵐ[_]
      W.w∘Prod.fst at hd
    rw [condExp_const hm] at hd
    exact hd.symm
  have hmap : ∀ᵐ x ∂(P:Measure (Model.Observation A Z)).map Prod.fst, W.w x=1 :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun W.measurableW measurable_const)).mpr he
  rw [W.marginal,ae_withDensity_iff (f := fun x => ENNReal.ofReal (W.p x))
    (ENNReal.measurable_ofReal.comp W.measurableP)] at hmap
  filter_upwards [hmap,Model.witness_density_positive A F P W] with x hx hp
  exact hx (ENNReal.ofReal_ne_zero_iff.mpr hp)

def fromModel (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Model.Observables Z A) (hD : F.D=fun _ => 1)
    (P : ProbabilityMeasure (Model.Observation A Z)) (W : Model.ModelWitness A F P) :
    Witness A F.U F.V P where
  p := W.p
  mU := W.a
  mV := W.b
  measurableP := W.measurableP
  measurableU := W.measurableA
  measurableV := W.measurableB
  nonnegativeP := W.nonnegativeP
  marginal := W.marginal
  momentU := by
    have hw : ∀ᵐ o ∂(P:Measure (Model.Observation A Z)), W.w o.1=1 := by
      apply ae_of_ae_map (μ := (P:Measure (Model.Observation A Z))) (f := Prod.fst)
        (p := fun x => W.w x=1) measurable_fst.aemeasurable
      rw [W.marginal]
      exact (unit_weight hD W).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [W.momentU,hw] with o ho hw
    simpa only [hw,one_mul,Function.comp_def] using ho
  momentV := by
    have hw : ∀ᵐ o ∂(P:Measure (Model.Observation A Z)), W.w o.1=1 := by
      apply ae_of_ae_map (μ := (P:Measure (Model.Observation A Z))) (f := Prod.fst)
        (p := fun x => W.w x=1) measurable_fst.aemeasurable
      rw [W.marginal]
      exact (unit_weight hD W).filter_mono (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [W.momentV,hw] with o ho hw
    simpa only [hw,one_mul,Function.comp_def] using ho
  smoothU := W.smoothA
  smoothV := W.smoothB
  densityBounds := by
    filter_upwards [W.densityBounds,unit_weight hD W] with x hx hw
    simpa only [hw,one_mul] using hx

theorem modelClass_eq_generic (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Model.Observables Z A) (hD : F.D=fun _ => 1) (hdelta : A.δ≤1) :
    modelClass A F.U F.V=Model.modelClass A F := by
  ext P
  exact ⟨fun ⟨W⟩ => ⟨W.toModel A F hD hdelta P⟩,fun ⟨W⟩ => ⟨fromModel A F hD P W⟩⟩

def productObservables (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (hM : 1≤A.M0) (U V : Z→ℝ) (hU : Measurable U) (hV : Measurable V)
    (bU : ∀ z, |U z|≤1) (bV : ∀ z, |V z|≤1) : Model.Observables Z A where
  D _ := 1
  U := U
  V := V
  W _ := 0
  lam := 1
  hlam := one_ne_zero
  measurableD := measurable_const
  measurableU := hU
  measurableV := hV
  measurableW := measurable_const
  boundD _ := ⟨zero_le_one,hM⟩
  boundU z := (bU z).trans hM
  boundV z := (bV z).trans hM
  boundW := ⟨0,le_rfl,fun _ => by simp⟩

def covarianceObservables (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (hM : 1≤A.M0) (U V : Z→ℝ) (hU : Measurable U) (hV : Measurable V)
    (bU : ∀ z, |U z|≤1) (bV : ∀ z, |V z|≤1) : Model.Observables Z A where
  D _ := 1
  U := U
  V := V
  W z := U z*V z
  lam := -1
  hlam := by norm_num
  measurableD := measurable_const
  measurableU := hU
  measurableV := hV
  measurableW := hU.mul hV
  boundD _ := ⟨zero_le_one,hM⟩
  boundU z := (bU z).trans hM
  boundV z := (bV z).trans hM
  boundW := ⟨1,zero_le_one,fun z => by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (bU z) (bV z) (abs_nonneg _) zero_le_one⟩

theorem target_eq_product (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (hM : 1≤A.M0) (U V : Z→ℝ) (hU : Measurable U) (hV : Measurable V)
    (bU : ∀ z, |U z|≤1) (bV : ∀ z, |V z|≤1)
    (P : ProbabilityMeasure (Model.Observation A Z)) :
    Model.target A (productObservables A hM U V hU hV bU bV) P=
      ∫ o, ((P:Measure (Model.Observation A Z))[U∘Prod.snd | Model.covariateInformation A Z]) o *
        ((P:Measure (Model.Observation A Z))[V∘Prod.snd | Model.covariateInformation A Z]) o ∂(P:Measure (Model.Observation A Z)) := by
  unfold Model.target
  simp only [productObservables,Function.comp_def,condExp_const measurable_fst.comap_le,
    integral_zero,zero_add,one_mul,div_one]

theorem target_eq_conditional_covariance (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (hM : 1≤A.M0) (U V : Z→ℝ) (hU : Measurable U) (hV : Measurable V)
    (bU : ∀ z, |U z|≤1) (bV : ∀ z, |V z|≤1)
    (P : ProbabilityMeasure (Model.Observation A Z)) :
    Model.target A (covarianceObservables A hM U V hU hV bU bV) P=
      ∫ o, ConditionalExamples.conditionalCovariance (Model.covariateInformation A Z)
        (U∘Prod.snd) (V∘Prod.snd) (P:Measure (Model.Observation A Z)) o ∂(P:Measure (Model.Observation A Z)) := by
  have hUL := Applications.bounded_memLp (P:Measure (Model.Observation A Z)) (U∘Prod.snd)
    (hU.comp measurable_snd) 1 (fun o => bU o.2)
  have hVL := Applications.bounded_memLp (P:Measure (Model.Observation A Z)) (V∘Prod.snd)
    (hV.comp measurable_snd) 1 (fun o => bV o.2)
  rw [ConditionalExamples.mean_conditional_covariance measurable_fst.comap_le _ _ hUL hVL]
  unfold Model.target
  simp only [covarianceObservables,Function.comp_def,condExp_const measurable_fst.comap_le,div_one,neg_one_mul]
  ring

theorem target_eq_conditional_variance (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
    (hM : 1≤A.M0) (Y : Z→ℝ) (hY : Measurable Y) (bY : ∀ z, |Y z|≤1)
    (P : ProbabilityMeasure (Model.Observation A Z)) :
    Model.target A (covarianceObservables A hM Y Y hY hY bY bY) P=
      ∫ o, condVar (Model.covariateInformation A Z) (Y∘Prod.snd)
        (P:Measure (Model.Observation A Z)) o ∂(P:Measure (Model.Observation A Z)) := by
  have hYL := Applications.bounded_memLp (P:Measure (Model.Observation A Z)) (Y∘Prod.snd)
    (hY.comp measurable_snd) 1 (fun o => bY o.2)
  rw [ConditionalExamples.mean_conditional_variance measurable_fst.comap_le _ hYL]
  unfold Model.target
  simp only [covarianceObservables,Function.comp_def,condExp_const measurable_fst.comap_le,
    div_one,neg_one_mul,pow_two]
  ring

end RoughRegime.Applications.Products
