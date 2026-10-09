module

public import RoughRegime.ApplicationEffects
public import RoughRegime.ApplicationOverlapBounds
public import RoughRegime.CausalConditionalBayes


@[expose] public section
/-! The observed-law overlap-weighted identity. Arm means are actual conditional
expectations under event-conditioned laws. No potential outcomes or causal
independence, consistency, or exchangeability assumptions enter these results. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def armEvent (d : ℕ) (j : Bool) : Set (Model.Covariate d × Response) :=
  {o | o.2.1 = j}

theorem armEvent_measurable (d : ℕ) (j : Bool) : MeasurableSet (armEvent d j) :=
  measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const

theorem armEvent_indicator_one (d : ℕ) (j : Bool) :
    (armEvent d j).indicator (fun _ => (1 : ℝ)) = MAR.armIndicator j ∘ Prod.snd := by
  funext o
  by_cases h : o.2.1 = j <;> simp [armEvent, MAR.armIndicator, h]

theorem armEvent_indicator_outcome (d : ℕ) (j : Bool) :
    (armEvent d j).indicator (outcome ∘ Prod.snd) = MAR.armOutcome j ∘ Prod.snd := by
  funext o
  by_cases h : o.2.1 = j <;> simp [armEvent, MAR.armOutcome, MAR.armIndicator, outcome, h]

/-- The arm regression is defined using the true law conditioned on A=j. -/
def conditionalArmMean (d : ℕ) (j : Bool)
    (P : ProbabilityMeasure (Model.Covariate d × Response)) :
    Model.Covariate d × Response → ℝ :=
  (cond (P : Measure (Model.Covariate d × Response)) (armEvent d j))[
    outcome ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance]

theorem arm_selector_complement (d : ℕ)
    (P : ProbabilityMeasure (Model.Covariate d × Response)) :
    (P : Measure (Model.Covariate d × Response))[
      MAR.armIndicator false ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
      (P : Measure (Model.Covariate d × Response))] fun o =>
        1 - (P : Measure (Model.Covariate d × Response))[
          MAR.armIndicator true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o := by
  let m : MeasurableSpace (Model.Covariate d × Response) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Model.Covariate d))
  let : MeasurableSpace (Model.Covariate d × Response) :=
    (inferInstance : MeasurableSpace (Model.Covariate d)).prod (inferInstance : MeasurableSpace Response)
  have h := condExp_sub (integrable_const (1 : ℝ)) (MAR.armIndicator_integrable d true P) m
  have he : ((fun _ : Model.Covariate d × Response => (1 : ℝ)) -
      MAR.armIndicator true ∘ Prod.snd) = MAR.armIndicator false ∘ Prod.snd := by
    funext o
    have hp := MAR.armIndicator_partition o.2
    simp only [Pi.sub_apply, Function.comp_apply]
    linarith
  rw [he] at h
  filter_upwards [h] with o ho
  rw [ho]
  change (P : Measure (Model.Covariate d × Response))[(fun _ => (1 : ℝ)) | m] o - _ = _
  rw [condExp_const measurable_fst.comap_le]

theorem Witness.arm_selector_positive (A : Model.Parameters) (ε : ℝ) (hε : 0 < ε)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) (j : Bool) :
    ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)),
      0 < (P : Measure (Model.Covariate A.d × Response))[
        MAR.armIndicator j ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o := by
  cases j
  · filter_upwards [arm_selector_complement A.d P, W.momentU,
      W.overlap_on_observations A ε P] with o hc hw ho
    change (P : Measure (Model.Covariate A.d × Response))[
      MAR.armIndicator true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o = W.mU o.1 at hw
    rw [hc, hw]
    linarith [ho.2]
  · filter_upwards [W.momentU, W.overlap_on_observations A ε P] with o hw ho
    change (P : Measure (Model.Covariate A.d × Response))[
      MAR.armIndicator true ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] o = W.mU o.1 at hw
    rw [hw]
    exact hε.trans_le ho.1

theorem Witness.arm_mass_ne_zero (A : Model.Parameters) (ε : ℝ) (hε : 0 < ε)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) (j : Bool) :
    (P : Measure (Model.Covariate A.d × Response)) (armEvent A.d j) ≠ 0 := by
  intro hz
  have hnot : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), o ∉ armEvent A.d j :=
    measure_eq_zero_iff_ae_notMem.mp hz
  have hi : MAR.armIndicator j ∘ Prod.snd =ᵐ[
      (P : Measure (Model.Covariate A.d × Response))] 0 := by
    rw [← armEvent_indicator_one A.d j]
    exact hnot.mono fun o ho => by simp [ho]
  have he := condExp_congr_ae hi (m := MeasurableSpace.comap Prod.fst inferInstance)
  rw [condExp_zero] at he
  have hf : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)), False := by
    filter_upwards [W.arm_selector_positive A ε hε P j, he] with o hp he
    rw [he] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  exact hf.exists.choose_spec

/-- Bayes' conditional event identity derives the arm means from their actual
conditioned laws, including the transfer back to the original design law. -/
theorem Witness.conditionalArmMean_eq_regression (A : Model.Parameters) (ε : ℝ) (hε : 0 < ε)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) (j : Bool) :
    conditionalArmMean A.d j P =ᵐ[(P : Measure (Model.Covariate A.d × Response))]
      MAR.regression A.d j P := by
  have hq : ∀ᵐ o ∂(P : Measure (Model.Covariate A.d × Response)),
      0 < (P : Measure (Model.Covariate A.d × Response))[
        (armEvent A.d j).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap Prod.fst inferInstance] o := by
    rw [armEvent_indicator_one]
    exact W.arm_selector_positive A ε hε P j
  have h := Causal.conditional_event_mean_ae_original
    (P : Measure (Model.Covariate A.d × Response))
    (MeasurableSpace.comap Prod.fst inferInstance) measurable_fst.comap_le
    (armEvent A.d j) (armEvent_measurable A.d j) (W.arm_mass_ne_zero A ε hε P j)
    (outcome ∘ Prod.snd) (outcome_measurable.comp measurable_snd)
    (ae_of_all _ fun o => outcome_bound o.2) hq
  filter_upwards [h] with o ho
  simpa only [conditionalArmMean, MAR.regression, armEvent_indicator_one,
    armEvent_indicator_outcome] using ho

theorem Witness.numerator_eq_weighted_arm_regressions (A : Model.Parameters) (ε : ℝ)
    (hε : 0 < ε) (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) :
    numerator A.d P = ∫ o, W.mU o.1 * (1 - W.mU o.1) *
      (MAR.regression A.d true P o - MAR.regression A.d false P o)
      ∂(P : Measure (Model.Covariate A.d × Response)) := by
  let μ : Measure (Model.Covariate A.d × Response) := P
  let m : MeasurableSpace (Model.Covariate A.d × Response) :=
    MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (Model.Covariate A.d))
  let : MeasurableSpace (Model.Covariate A.d × Response) :=
    (inferInstance : MeasurableSpace (Model.Covariate A.d)).prod (inferInstance : MeasurableSpace Response)
  have hm : m ≤ (inferInstance : MeasurableSpace (Model.Covariate A.d × Response)) :=
    measurable_fst.comap_le
  have ha : MemLp (treatment ∘ Prod.snd) 2 μ := bounded_memLp μ _
    (treatment_measurable.comp measurable_snd) 1 fun o => treatment_bound o.2
  have hy : MemLp (outcome ∘ Prod.snd) 2 μ := bounded_memLp μ _
    (outcome_measurable.comp measurable_snd) 1 fun o => outcome_bound o.2
  have hi : Integrable (fun o => μ[treatment ∘ Prod.snd | m] o *
      μ[outcome ∘ Prod.snd | m] o) μ :=
    memLp_one_iff_integrable.mp ((ha.condExp (m := m) one_le_two).mul
      (hy.condExp (m := m) one_le_two))
  have hs := condExp_add (MAR.armOutcome_integrable A.d true P)
    (MAR.armOutcome_integrable A.d false P) m
  have he : (MAR.armOutcome true ∘ (Prod.snd : Model.Covariate A.d × Response → Response) +
      MAR.armOutcome false ∘ Prod.snd) =
      outcome ∘ Prod.snd := by
    funext o
    exact MAR.armOutcome_partition o.2
  rw [he] at hs
  rw [numerator, ConditionalExamples.mean_conditional_covariance hm _ _ ha hy]
  change (∫ o, MAR.armOutcome true o.2 ∂μ) -
      (∫ o, μ[treatment ∘ Prod.snd | m] o * μ[outcome ∘ Prod.snd | m] o ∂μ) = _
  rw [← integral_condExp hm (μ := μ) (f := fun o => MAR.armOutcome true o.2),
    ← integral_sub integrable_condExp hi]
  apply integral_congr_ae
  filter_upwards [hs, arm_selector_complement A.d P, W.momentU,
      W.overlap_on_observations A ε P] with o hs hc hw ho
  change μ[MAR.armIndicator true ∘ Prod.snd | m] o = W.mU o.1 at hw
  have hc' : μ[MAR.armIndicator false ∘ Prod.snd | m] o = 1 - W.mU o.1 := by
    exact hc.trans (by rw [hw])
  have hw0 : W.mU o.1 ≠ 0 := ne_of_gt (hε.trans_le ho.1)
  have hw1 : 1 - W.mU o.1 ≠ 0 := ne_of_gt (by linarith [ho.2])
  change μ[MAR.armOutcome true ∘ Prod.snd | m] o -
    μ[MAR.armIndicator true ∘ Prod.snd | m] o * μ[outcome ∘ Prod.snd | m] o = _
  simp only [MAR.regression]
  rw [hw, hc', hs]
  simp only [Pi.add_apply]
  dsimp only [μ, m]
  field_simp [hw0, hw1]
  ring

/-- The observed-arm conditional ratios give the same weighted identity. -/
theorem Witness.effect_eq_weighted_arm_regressions (A : Model.Parameters) (ε : ℝ)
    (hε : 0 < ε) (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) :
    effect A.d P =
      (∫ o, W.mU o.1 * (1 - W.mU o.1) *
        (MAR.regression A.d true P o - MAR.regression A.d false P o)
        ∂(P : Measure (Model.Covariate A.d × Response))) /
      (∫ o, W.mU o.1 * (1 - W.mU o.1)
        ∂(P : Measure (Model.Covariate A.d × Response))) := by
  rw [effect, W.denominator_eq A ε P, W.numerator_eq_weighted_arm_regressions A ε hε P]

/-- The source's purely statistical overlap identity with actual conditional
means under the two observed arm-conditioned laws. -/
theorem Witness.effect_eq_weighted_conditional_arm_means (A : Model.Parameters) (ε : ℝ)
    (hε : 0 < ε) (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A ε P) :
    effect A.d P =
      (∫ o, W.mU o.1 * (1 - W.mU o.1) *
        (conditionalArmMean A.d true P o - conditionalArmMean A.d false P o)
        ∂(P : Measure (Model.Covariate A.d × Response))) /
      (∫ o, W.mU o.1 * (1 - W.mU o.1)
        ∂(P : Measure (Model.Covariate A.d × Response))) := by
  rw [effect, W.denominator_eq A ε P, W.numerator_eq_weighted_arm_regressions A ε hε P]
  congr 1
  apply integral_congr_ae
  filter_upwards [W.conditionalArmMean_eq_regression A ε hε P true,
    W.conditionalArmMean_eq_regression A ε hε P false] with o h1 h0
  rw [h1, h0]

end RoughRegime.Applications.Overlap
