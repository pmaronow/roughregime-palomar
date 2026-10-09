module

public import RoughRegime.UniformCube
public import RoughRegime.HolderConstants
public import RoughRegime.ProductTarget


@[expose] public section
/-! Actual membership of constant response paths in the model and local class. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace RoughRegime.Model

def productLaw (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) : ProbabilityMeasure (Observation A Z) :=
  ⟨(cubeVolume A.d).prod (π : Measure Z), inferInstance⟩

def productWitness (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z)
    (hw : A.δ ≤ baselineW A F π)
    (hg : A.gminus ≤ baselineW A F π ∧ baselineW A F π ≤ A.gplus)
    (ha : |baselineA A F π| ≤ A.H) (hb : |baselineB A F π| ≤ A.H) :
    ModelWitness A F (productLaw A π) where
  p _ := 1
  w _ := baselineW A F π
  a _ := baselineA A F π
  b _ := baselineB A F π
  measurableP := measurable_const
  measurableW := measurable_const
  measurableA := measurable_const
  measurableB := measurable_const
  nonnegativeP := Filter.Eventually.of_forall fun _ => by norm_num
  marginal := by
    change ((cubeVolume A.d).prod (π : Measure Z)).map Prod.fst = _
    simp
  momentD := by
    exact Applications.conditional_snd_product (cubeVolume A.d) (π : Measure Z) F.D F.measurableD
  momentU := by
    have hw0 : baselineW A F π ≠ 0 := ne_of_gt (A.hδ.trans_le hw)
    filter_upwards [Applications.conditional_snd_product (cubeVolume A.d)
      (π : Measure Z) F.U F.measurableU] with x hx
    change ((cubeVolume A.d).prod (π : Measure Z))[F.U ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] x = baselineW A F π * baselineA A F π
    rw [hx]
    unfold baselineA
    field_simp
  momentV := by
    have hw0 : baselineW A F π ≠ 0 := ne_of_gt (A.hδ.trans_le hw)
    filter_upwards [Applications.conditional_snd_product (cubeVolume A.d)
      (π : Measure Z) F.V F.measurableV] with x hx
    change ((cubeVolume A.d).prod (π : Measure Z))[F.V ∘ Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] x = baselineW A F π * baselineB A F π
    rw [hx]
    unfold baselineB
    field_simp
  overlap := Filter.Eventually.of_forall fun _ => hw
  smoothA := const_mem_holderBall A.hα ha
  smoothB := const_mem_holderBall A.hβ hb
  densityBounds := Filter.Eventually.of_forall fun _ => by simpa using hg

theorem productLaw_mem_modelClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z)
    (hw : A.δ ≤ baselineW A F π)
    (hg : A.gminus ≤ baselineW A F π ∧ baselineW A F π ≤ A.gplus)
    (ha : |baselineA A F π| ≤ A.H) (hb : |baselineB A F π| ≤ A.H) :
    productLaw A π ∈ modelClass A F := ⟨productWitness A F π hw hg ha hb⟩

theorem productLaw_mem_localClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π π0 : ProbabilityMeasure Z) (r : ℝ)
    (hw : A.δ ≤ baselineW A F π)
    (hg : A.gminus ≤ baselineW A F π ∧ baselineW A F π ≤ A.gplus)
    (ha : |baselineA A F π| ≤ A.H) (hb : |baselineB A F π| ≤ A.H)
    (hdw : |baselineW A F π - baselineW A F π0| ≤ r)
    (hda : |baselineA A F π - baselineA A F π0| ≤ r)
    (hdb : |baselineB A F π - baselineB A F π0| ≤ r) :
    productLaw A π ∈ localClass A F π0 r := by
  refine ⟨productWitness A F π hw hg ha hb, ?_⟩
  exact Filter.Eventually.of_forall fun _ => ⟨hdw, hda, hdb⟩

theorem baselineRatios_continuousAt (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (ν : ℝ → ProbabilityMeasure Z) (t0 : ℝ)
    (hD : ContinuousAt (fun t => baselineW A F (ν t)) t0)
    (hU : ContinuousAt (fun t => ∫ z, F.U z ∂(ν t : Measure Z)) t0)
    (hV : ContinuousAt (fun t => ∫ z, F.V z ∂(ν t : Measure Z)) t0)
    (hw : baselineW A F (ν t0) ≠ 0) :
    ContinuousAt (fun t => baselineA A F (ν t)) t0 ∧
      ContinuousAt (fun t => baselineB A F (ν t)) t0 := by
  exact ⟨hU.div hD hw, hV.div hD hw⟩

/-- Constant response paths remain in every positive local radius about the
interior baseline. All smoothness and model-membership conditions are derived. -/
theorem eventually_productLaw_mem_localClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π0 : ProbabilityMeasure Z) (ν : ℝ → ProbabilityMeasure Z)
    (hν0 : ν 0 = π0) (hnd : Nondegenerate A F π0) (r : ℝ) (hr : 0 < r)
    (hD : ContinuousAt (fun t => baselineW A F (ν t)) 0)
    (hA : ContinuousAt (fun t => baselineA A F (ν t)) 0)
    (hB : ContinuousAt (fun t => baselineB A F (ν t)) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), productLaw A (ν t) ∈ localClass A F π0 r := by
  obtain ⟨_, hwl, hwh, hal, hbl, _⟩ := hnd
  have hlow : ∀ᶠ t in 𝓝 (0 : ℝ), max A.δ A.gminus < baselineW A F (ν t) :=
    continuousAt_const.eventually_lt hD (by simpa [hν0] using hwl)
  have hhigh : ∀ᶠ t in 𝓝 (0 : ℝ), baselineW A F (ν t) < A.gplus :=
    hD.eventually_lt continuousAt_const (by simpa [hν0] using hwh)
  have hanorm : ∀ᶠ t in 𝓝 (0 : ℝ), |baselineA A F (ν t)| < A.H :=
    hA.abs.eventually_lt continuousAt_const (by simpa [hν0] using hal)
  have hbnorm : ∀ᶠ t in 𝓝 (0 : ℝ), |baselineB A F (ν t)| < A.H :=
    hB.abs.eventually_lt continuousAt_const (by simpa [hν0] using hbl)
  have hdnear : ∀ᶠ t in 𝓝 (0 : ℝ), |baselineW A F (ν t) - baselineW A F π0| < r :=
    (hD.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  have hanear : ∀ᶠ t in 𝓝 (0 : ℝ), |baselineA A F (ν t) - baselineA A F π0| < r :=
    (hA.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  have hbnear : ∀ᶠ t in 𝓝 (0 : ℝ), |baselineB A F (ν t) - baselineB A F π0| < r :=
    (hB.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  filter_upwards [hlow, hhigh, hanorm, hbnorm, hdnear, hanear, hbnear] with t hl hh ha hb hd da db
  exact productLaw_mem_localClass A F (ν t) π0 r
    ((le_max_left _ _).trans hl.le) ⟨(le_max_right _ _).trans hl.le, hh.le⟩
    ha.le hb.le hd.le da.le db.le

end RoughRegime.Model
