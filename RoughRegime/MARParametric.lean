module

public import RoughRegime.MARLocalized
public import RoughRegime.ApplicationEffectTransfers


@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace RoughRegime.Applications.MAR

/-- Half of the paper's MAR regression score. The affine parameter is the
change in the observed regression, rather than its residual mean. -/
def regressionScore (z : Response) : ℝ := 4 * observedOutcome z - 2 * observed z

lemma regressionScore_measurable : Measurable regressionScore := by
  exact (measurable_const.mul observedOutcome_measurable).sub
    (measurable_const.mul observed_measurable)

lemma regressionScore_bound (z : Response) : |regressionScore z| ≤ 2 := by
  cases z with
  | inl z => simp [regressionScore, observed, observedOutcome]
  | inr y =>
    simp only [regressionScore, observed, observedOutcome, Sum.elim_inr]
    exact abs_le.mpr ⟨by linarith [y.property.1], by linarith [y.property.2]⟩

lemma regressionScore_moments :
    (∫ z, regressionScore z ∂(baseline : Measure Response)) = 0 ∧
    (∫ z, observed z * regressionScore z ∂(baseline : Measure Response)) = 0 ∧
    (∫ z, observedOutcome z * regressionScore z ∂(baseline : Measure Response)) = 1 / 2 := by
  rw [baseline_integral regressionScore regressionScore_measurable,
    baseline_integral (fun z => observed z * regressionScore z)
      (observed_measurable.mul regressionScore_measurable),
    baseline_integral (fun z => observedOutcome z * regressionScore z)
      (observedOutcome_measurable.mul regressionScore_measurable)]
  norm_num [regressionScore, observed, observedOutcome, missingPoint, zeroPoint, onePoint]

def responsePath (t : ℝ) : GeneralTesting.DensityLaw (baseline : Measure Response) :=
  AffineResponseLower.responseDensityLaw (baseline : Measure Response)
    (fun _ => 0) regressionScore measurable_const regressionScore_measurable
    0 (1 / 8) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => by norm_num) regressionScore_bound (by simp) regressionScore_moments.1 t

theorem responsePath_integral (t : ℝ) (f : Response → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂(responsePath t).measure) = (∫ z, f z ∂(baseline : Measure Response)) +
      AffineResponseLower.clip (1 / 8) t *
        (∫ z, f z * regressionScore z ∂(baseline : Measure Response)) := by
  have hi := AffineResponseLower.score_integrable (baseline : Measure Response) f hf B hbound
  have his := AffineResponseLower.bounded_score_product_integrable
    (baseline : Measure Response) f regressionScore hf regressionScore_measurable
    B 2 hB (by norm_num) hbound regressionScore_bound
  have he := AffineResponseLower.integral_density_affine (baseline : Measure Response)
    (responsePath t) (fun _ => 0) regressionScore f 0 (AffineResponseLower.clip (1 / 8) t)
    (Eventually.of_forall fun _ => rfl) hi (by simp) his
  simpa only [zero_mul, add_zero] using he

theorem responsePath_moments (t : ℝ) :
    (∫ z, observed z ∂(responsePath t).measure) = 1 / 2 ∧
    (∫ z, observedOutcome z ∂(responsePath t).measure) =
      1 / 4 + AffineResponseLower.clip (1 / 8) t / 2 := by
  constructor
  · rw [responsePath_integral t observed observed_measurable 1 (by norm_num)
      (fun z => by simpa only [abs_of_nonneg (observed_range z).1] using (observed_range z).2),
      baseline_response_moments.1, regressionScore_moments.2.1]
    simp
  · rw [responsePath_integral t observedOutcome observedOutcome_measurable 1 (by norm_num)
      (fun z => by simpa only [abs_of_nonneg (observedOutcome_range z).1] using
        (observedOutcome_range z).2), baseline_response_moments.2,
      regressionScore_moments.2.2]
    ring

def parametricLaw (A : Model.Parameters) (t : ℝ) :
    GeneralTesting.DensityLaw ((Model.cubeVolume A.d).prod (baseline : Measure Response)) :=
  AffineResponseLower.withDesign (baseline : Measure Response) (Model.cubeVolume A.d) (responsePath t)

theorem parametricLaw_eq_product (A : Model.Parameters) (t : ℝ) :
    (parametricLaw A t).probabilityMeasure = Model.productLaw A (responsePath t).probabilityMeasure := by
  apply Subtype.ext
  exact AffineResponseLower.withDesign_measure (baseline : Measure Response)
    (Model.cubeVolume A.d) (responsePath t)

theorem parametricLaw_target (A : Model.Parameters) (hM : 1 ≤ A.M0) (t : ℝ) :
    Model.target A (observables A hM) (parametricLaw A t).probabilityMeasure =
      1 / 2 + AffineResponseLower.clip (1 / 8) t := by
  unfold parametricLaw
  rw [AffineResponseLower.model_target_withDesign]
  change (∫ _, (0 : ℝ) ∂(responsePath t).measure) + 1 *
    ((∫ _, (1 : ℝ) ∂(responsePath t).measure) *
      (∫ z, observedOutcome z ∂(responsePath t).measure) /
      (∫ z, observed z ∂(responsePath t).measure)) = _
  rw [(responsePath_moments t).1, (responsePath_moments t).2]
  simp
  ring

theorem responsePath_ratios (A : Model.Parameters) (hM : 1 ≤ A.M0) (t : ℝ) :
    Model.baselineW A (observables A hM) (responsePath t).probabilityMeasure = 1 / 2 ∧
    Model.baselineA A (observables A hM) (responsePath t).probabilityMeasure = 2 ∧
    Model.baselineB A (observables A hM) (responsePath t).probabilityMeasure =
      1 / 2 + AffineResponseLower.clip (1 / 8) t := by
  dsimp only [Model.baselineW, Model.baselineA, Model.baselineB, observables,
    GeneralTesting.DensityLaw.probabilityMeasure]
  change (∫ z, observed z ∂(responsePath t).measure) = 1 / 2 ∧
    ((∫ _, (1 : ℝ) ∂(responsePath t).measure) / (∫ z, observed z ∂(responsePath t).measure)) = 2 ∧
    ((∫ z, observedOutcome z ∂(responsePath t).measure) / (∫ z, observed z ∂(responsePath t).measure)) =
      1 / 2 + AffineResponseLower.clip (1 / 8) t
  rw [(responsePath_moments t).1, (responsePath_moments t).2]
  simp
  ring

def parametricWitness (A : Model.Parameters) (hM : 1 ≤ A.M0)
    (hδ : A.δ ≤ 1 / 2) (hg : A.gminus ≤ 1 / 2 ∧ 1 / 2 ≤ A.gplus)
    (hH : 2 ≤ A.H) (t : ℝ) : Witness A (parametricLaw A t).probabilityMeasure := by
  rw [parametricLaw_eq_product]
  have hm := responsePath_ratios A hM t
  have hw : A.δ ≤ Model.baselineW A (observables A hM) (responsePath t).probabilityMeasure :=
    hm.1 ▸ hδ
  have hgg : A.gminus ≤ Model.baselineW A (observables A hM) (responsePath t).probabilityMeasure ∧
      Model.baselineW A (observables A hM) (responsePath t).probabilityMeasure ≤ A.gplus := hm.1 ▸ hg
  have ha : |Model.baselineA A (observables A hM) (responsePath t).probabilityMeasure| ≤ A.H := by
    simpa only [hm.2.1, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hH
  have hb : |Model.baselineB A (observables A hM) (responsePath t).probabilityMeasure| ≤ A.H := by
    rw [hm.2.2]
    have ht := AffineResponseLower.clip_abs_le (by norm_num : (0 : ℝ) ≤ 1 / 8) t
    have he := abs_add_le (1 / 2 : ℝ) (AffineResponseLower.clip (1 / 8) t)
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at he
    linarith
  let h := Model.productWitness A (observables A hM) (responsePath t).probabilityMeasure hw hgg ha hb
  exact genericWitnessToMAR A hM _ h (Eventually.of_forall fun _ => by
    change Model.baselineW A (observables A hM) (responsePath t).probabilityMeasure ≤ 1 - A.δ
    rw [hm.1]
    linarith)

end RoughRegime.Applications.MAR
