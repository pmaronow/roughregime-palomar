module

public import RoughRegime.Applications


@[expose] public section
/-! Actual bounded-iid concentration for the fixed-grid pilot in Lemma 20. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal ContDiff
namespace RoughRegime.Applications

/-- A direct Hoeffding bound for a centered bounded observable on the genuine iid law. -/
theorem iid_sum_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (X : Ω → ℝ) (hX : Measurable X) (hb : ∀ x, |X x| ≤ 1)
    (hm : (∫ x, X x ∂μ) = 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | (n : ℝ) * ε ≤ ∑ i, X (x i)} ≤ Real.exp (-(n : ℝ) * ε ^ 2 / 2) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  have hs : ∀ i : Fin n, HasSubgaussianMGF (fun x : Fin n → Ω => X (x i)) 1 ν := by
    intro i
    have hm' : (∫ x : Fin n → Ω, X (x i) ∂ν) = 0 := by
      exact (integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) hX.aestronglyMeasurable).trans hm
    have hg := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((hX.comp (measurable_pi_apply i)).aemeasurable)
      (ae_of_all ν (fun x => (abs_le.mp (hb (x i))))) hm'
    norm_num at hg
    exact hg
  have hi : iIndepFun (fun i : Fin n => fun x : Fin n → Ω => X (x i)) ν :=
    iIndepFun_pi (fun _ => hX.aemeasurable)
  have hsum : HasSubgaussianMGF (fun x : Fin n → Ω => ∑ i, X (x i)) (n : ℝ≥0) ν := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hi (c := fun _ => (1 : ℝ≥0))
      (s := Finset.univ) (fun i _ => hs i)
  have ht := hsum.measure_ge_le (show 0 ≤ (n : ℝ) * ε by positivity)
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have heq : -((n : ℝ) * ε) ^ 2 / (2 * (n : ℝ)) = -(n : ℝ) * ε ^ 2 / 2 := by
    field_simp
  simpa only [NNReal.coe_natCast, heq] using ht

/-- The corresponding genuine two-sided error bound. -/
theorem iid_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (X : Ω → ℝ) (hX : Measurable X) (hb : ∀ x, |X x| ≤ 1)
    (hm : (∫ x, X x ∂μ) = 0) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | (n : ℝ) * ε ≤ |∑ i, X (x i)|} ≤ 2 * Real.exp (-(n : ℝ) * ε ^ 2 / 2) := by
  have hp := iid_sum_upper_tail μ hn X hX hb hm ε hε
  have hnmean : (∫ x, -X x ∂μ) = 0 := by rw [integral_neg, hm, neg_zero]
  have hneg := iid_sum_upper_tail μ hn (fun x => -X x) hX.neg
    (fun x => by simpa only [abs_neg] using hb x) hnmean ε hε
  have heq : {x : Fin n → Ω | (n : ℝ) * ε ≤ |∑ i, X (x i)|} =
      {x | (n : ℝ) * ε ≤ ∑ i, X (x i)} ∪
      {x | (n : ℝ) * ε ≤ ∑ i, -X (x i)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib, le_abs]
  rw [heq]
  exact (measureReal_union_le _ _).trans (by linarith)

def cellIndicator {Ω : Type*} (Q : Set Ω) : Ω → ℝ := Q.indicator (fun _ => 1)

def cellResponse {Ω : Type*} (Q : Set Ω) (R : Ω → ℝ) : Ω → ℝ := Q.indicator R

def cellMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : Set Ω) (R : Ω → ℝ) : ℝ :=
  (∫ x, cellResponse Q R x ∂μ) / μ.real Q

def cellCount {Ω : Type*} {n : ℕ} (Q : Set Ω) (x : Fin n → Ω) : ℝ :=
  ∑ i, cellIndicator Q (x i)

def cellSum {Ω : Type*} {n : ℕ} (Q : Set Ω) (R : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i, cellResponse Q R (x i)

/-- The actual empirical mean inside a cell, with the paper's empty-cell default. -/
def cellAverage {Ω : Type*} {n : ℕ} (Q : Set Ω) (R : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  if cellCount Q x = 0 then 1 / 2 else cellSum Q R x / cellCount Q x

lemma cellIndicator_range {Ω : Type*} (Q : Set Ω) (x : Ω) :
    cellIndicator Q x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ Q <;> simp [cellIndicator, hx]

lemma cellResponse_range {Ω : Type*} (Q : Set Ω) (R : Ω → ℝ)
    (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1) (x : Ω) :
    cellResponse Q R x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : x ∈ Q
  · simpa [cellResponse, hx] using hR x
  · simp [cellResponse, hx]

lemma integral_cellIndicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : Set Ω) (hQ : MeasurableSet Q) :
    (∫ x, cellIndicator Q x ∂μ) = μ.real Q := by
  simp [cellIndicator, integral_indicator hQ]

lemma cellMean_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : Set Ω) (hQ : MeasurableSet Q)
    (hπ : 0 < μ.real Q) (R : Ω → ℝ) (hmR : Measurable R)
    (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1) :
    cellMean μ Q R ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable (cellIndicator Q) μ := Integrable.of_mem_Icc 0 1
    (measurable_const.indicator hQ).aemeasurable (ae_of_all μ (cellIndicator_range Q))
  have hr : Integrable (cellResponse Q R) μ := Integrable.of_mem_Icc 0 1
    (hmR.indicator hQ).aemeasurable (ae_of_all μ (cellResponse_range Q R hR))
  have hnonneg : 0 ≤ ∫ x, cellResponse Q R x ∂μ :=
    integral_nonneg (fun x => (cellResponse_range Q R hR x).1)
  have hle : (∫ x, cellResponse Q R x ∂μ) ≤ μ.real Q := by
    rw [← integral_cellIndicator μ Q hQ]
    apply integral_mono hr hi
    intro x
    by_cases hx : x ∈ Q
    · simpa [cellResponse, cellIndicator, hx] using (hR x).2
    · simp [cellResponse, cellIndicator, hx]
  exact ⟨div_nonneg hnonneg hπ.le, (div_le_one hπ).mpr hle⟩

/-- A true conditional expectation identifies the cell mean with the average
of the conditional regression on that information-measurable cell. -/
lemma cellMean_eq_conditional_average {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (Q : Set Ω) (hQ : MeasurableSet[m] Q)
    (R w : Ω → ℝ) (hR : Integrable R μ) (hw : μ[R | m] =ᵐ[μ] w) :
    @cellMean Ω m0 μ Q R = (∫ x in Q, w x ∂μ) / μ.real Q := by
  unfold cellMean cellResponse
  rw [integral_indicator (hm Q hQ)]
  congr 1
  exact (setIntegral_condExp hm hR hQ).symm.trans (integral_congr_ae (hw.filter_mono ae_restrict_le))

lemma conditional_cellMean_mem_Icc {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (Q : Set Ω) (hQ : MeasurableSet[m] Q) (hπ : 0 < μ.real Q)
    (R w : Ω → ℝ) (hR : Integrable R μ) (hw : μ[R | m] =ᵐ[μ] w)
    (a b : ℝ) (hbound : ∀ x ∈ Q, w x ∈ Set.Icc a b) :
    @cellMean Ω m0 μ Q R ∈ Set.Icc a b := by
  have hwi : Integrable w μ := integrable_condExp.congr hw
  have hl : ∀ᵐ x ∂μ.restrict Q, a ≤ w x :=
    (ae_restrict_mem (hm Q hQ)).mono (fun x hx => (hbound x hx).1)
  have hu : ∀ᵐ x ∂μ.restrict Q, w x ≤ b :=
    (ae_restrict_mem (hm Q hQ)).mono (fun x hx => (hbound x hx).2)
  have hlo := integral_mono_ae (integrable_const a) hwi.integrableOn hl
  have hup := integral_mono_ae hwi.integrableOn (integrable_const b) hu
  simp only [integral_const, Measure.restrict_apply_univ, measureReal_def, smul_eq_mul] at hlo hup
  rw [cellMean_eq_conditional_average μ m hm Q hQ R w hR hw]
  exact ⟨(le_div_iff₀ hπ).mpr (by simpa [mul_comm, measureReal_def] using hlo),
    (div_le_iff₀ hπ).mpr (by simpa [mul_comm, measureReal_def] using hup)⟩

lemma conditional_cellMean_bias {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (Q : Set Ω) (hQ : MeasurableSet[m] Q) (hπ : 0 < μ.real Q)
    (R w : Ω → ℝ) (hR : Integrable R μ) (hw : μ[R | m] =ᵐ[μ] w)
    (c ζ : ℝ) (hbound : ∀ x ∈ Q, |w x - c| ≤ ζ) :
    |@cellMean Ω m0 μ Q R - c| ≤ ζ := by
  have hb := conditional_cellMean_mem_Icc μ m hm Q hQ hπ R w hR hw (c - ζ) (c + ζ)
    (fun x hx => by have hh := abs_le.mp (hbound x hx); exact ⟨by linarith, by linarith⟩)
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

lemma cellAverage_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Q : Set Ω) (hQ : MeasurableSet Q) (R : Ω → ℝ) (hmR : Measurable R) :
    Measurable (cellAverage (n := n) Q R) := by
  have hi : Measurable (cellCount (n := n) Q) :=
    Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator hQ).comp (measurable_pi_apply i))
  have hr : Measurable (cellSum (n := n) Q R) :=
    Finset.measurable_sum _ (fun i _ =>
      (hmR.indicator hQ).comp (measurable_pi_apply i))
  exact measurable_const.ite (measurableSet_eq_fun hi measurable_const) (hr.div hi)

/-- The actual centered numerator of the empirical conditional mean. -/
def cellCentered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Q : Set Ω) (R : Ω → ℝ) (x : Ω) : ℝ :=
  cellResponse Q R x - cellMean μ Q R * cellIndicator Q x

lemma cellCentered_properties {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : Set Ω) (hQ : MeasurableSet Q)
    (hπ : 0 < μ.real Q) (R : Ω → ℝ) (hmR : Measurable R)
    (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (cellCentered μ Q R) ∧
      (∀ x, |cellCentered μ Q R x| ≤ 1) ∧ (∫ x, cellCentered μ Q R x ∂μ) = 0 := by
  have hmi : Measurable (cellIndicator Q) := measurable_const.indicator hQ
  have hmr : Measurable (cellResponse Q R) := hmR.indicator hQ
  have hi : Integrable (cellIndicator Q) μ := Integrable.of_mem_Icc 0 1
    hmi.aemeasurable (ae_of_all μ (cellIndicator_range Q))
  have hr : Integrable (cellResponse Q R) μ := Integrable.of_mem_Icc 0 1
    hmr.aemeasurable (ae_of_all μ (cellResponse_range Q R hR))
  have hm := cellMean_range μ Q hQ hπ R hmR hR
  refine ⟨hmr.sub (hmi.const_mul _), ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Q
    · simp only [cellCentered, cellResponse, cellIndicator, Set.indicator_of_mem hx, mul_one]
      exact abs_le.mpr ⟨by linarith [(hR x).1, hm.2], by linarith [(hR x).2, hm.1]⟩
    · simp [cellCentered, cellResponse, cellIndicator, hx]
  · change (∫ x, cellResponse Q R x - cellMean μ Q R * cellIndicator Q x ∂μ) = 0
    rw [integral_sub hr (hi.const_mul _), integral_const_mul,
      integral_cellIndicator μ Q hQ]
    unfold cellMean
    field_simp
    ring

/-- Exponential concentration of the genuine cell average, including empty cells.
The direct bounded-sum proof gives a constant sufficient for the fixed-accuracy pilot. -/
theorem cellAverage_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (Q : Set Ω) (hQ : MeasurableSet Q) (hπ : 0 < μ.real Q)
    (R : Ω → ℝ) (hmR : Measurable R) (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηone : η ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | η ≤ |cellAverage Q R x - cellMean μ Q R|} ≤
      3 * Real.exp (-(n : ℝ) * (μ.real Q) ^ 2 * η ^ 2 / 8) := by
  let π := μ.real Q
  let m := cellMean μ Q R
  let A := cellCentered μ Q R
  let B : Ω → ℝ := fun x => π - cellIndicator Q x
  have hπpos : 0 < π := hπ
  have hπone : π ≤ 1 := measureReal_le_one
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hA := cellCentered_properties μ Q hQ hπ R hmR hR
  have hmi : Measurable (cellIndicator Q) := measurable_const.indicator hQ
  have hmb : Measurable B := measurable_const.sub hmi
  have hbb : ∀ x, |B x| ≤ 1 := by
    intro x
    have hi := cellIndicator_range Q x
    exact abs_le.mpr ⟨by dsimp [B]; linarith [hi.2], by dsimp [B]; linarith [hi.1]⟩
  have hBm : (∫ x, B x ∂μ) = 0 := by
    have hi : Integrable (cellIndicator Q) μ := Integrable.of_mem_Icc 0 1
      hmi.aemeasurable (ae_of_all μ (cellIndicator_range Q))
    change (∫ x, π - cellIndicator Q x ∂μ) = 0
    rw [integral_sub (integrable_const _) hi, integral_const, integral_cellIndicator μ Q hQ]
    simp [π]
  have hp := iid_sum_abs_tail μ hn A hA.1 hA.2.1 hA.2.2 (π * η / 2) (by positivity)
  have hl := iid_sum_upper_tail μ hn B hmb hbb hBm (π / 2) (by positivity)
  have hsub : {x : Fin n → Ω | η ≤ |cellAverage Q R x - m|} ⊆
      {x | (n : ℝ) * (π * η / 2) ≤ |∑ i, A (x i)|} ∪
      {x | (n : ℝ) * (π / 2) ≤ ∑ i, B (x i)} := by
    intro x hx
    by_contra hnot
    have hnot' := not_or.mp hnot
    have ha : |∑ i, A (x i)| < (n : ℝ) * (π * η / 2) := lt_of_not_ge hnot'.1
    have hb : (∑ i, B (x i)) < (n : ℝ) * (π / 2) := lt_of_not_ge hnot'.2
    have hBsum : (∑ i, B (x i)) = (n : ℝ) * π - cellCount Q x := by
      simp only [B, Finset.sum_sub_distrib, cellCount, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hBsum] at hb
    have hc : 0 < cellCount Q x := by nlinarith [mul_pos hnpos hπ]
    have hAsum : (∑ i, A (x i)) = cellSum Q R x - m * cellCount Q x := by
      simp only [A, cellCentered, cellSum, cellCount, m, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have heq : cellAverage Q R x - m = (∑ i, A (x i)) / cellCount Q x := by
      rw [cellAverage, ite_eq_right hc.ne', hAsum]
      field_simp
    change η ≤ |cellAverage Q R x - m| at hx
    rw [heq, abs_div, abs_of_pos hc] at hx
    have he := (le_div_iff₀ hc).mp hx
    nlinarith
  have hExp : Real.exp (-(n : ℝ) * (π / 2) ^ 2 / 2) ≤
      Real.exp (-(n : ℝ) * (π * η / 2) ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have hs : η ^ 2 ≤ 1 := by nlinarith
    have hp2 : 0 ≤ (n : ℝ) * π ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hp2]
  have hbound := (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add hp (hl.trans hExp)))
  have hexp : -(n : ℝ) * (π * η / 2) ^ 2 / 2 = -(n : ℝ) * π ^ 2 * η ^ 2 / 8 := by ring
  rw [hexp] at hbound
  linarith

/-- Uniform cell-probability lower bounds give a uniform exponential constant. -/
theorem cellAverage_uniform_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : n ≠ 0)
    (Q : Set Ω) (hQ : MeasurableSet Q) (p : ℝ) (hp : 0 < p) (hπ : p ≤ μ.real Q)
    (R : Ω → ℝ) (hmR : Measurable R) (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (hηone : η ≤ 1) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {x | η ≤ |cellAverage Q R x - cellMean μ Q R|} ≤
      3 * Real.exp (-(n : ℝ) * p ^ 2 * η ^ 2 / 8) := by
  apply (cellAverage_exponential_tail μ hn Q hQ (hp.trans_le hπ) R hmR hR η hη hηone).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hs : p ^ 2 ≤ (μ.real Q) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (n : ℝ) * η ^ 2 / 8 by positivity)
  nlinarith

/-- The paper's pilot, constructed from actual cell counts and response sums. -/
def fixedGridPilot {Ω X J : Type*} [Fintype J] {n : ℕ}
    (Q : J → Set Ω) (R : Ω → ℝ) (φ : J → X → ℝ) (ε : ℝ) (hε : ε ≤ 1 - ε)
    (x : X) (data : Fin n → Ω) : ℝ :=
  ∑ j, φ j x * (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ)

theorem fixedGridPilot_jointly_measurable {Ω X J : Type*} [Fintype J]
    [MeasurableSpace Ω] [MeasurableSpace X] {n : ℕ}
    (Q : J → Set Ω) (hQ : ∀ j, MeasurableSet (Q j)) (R : Ω → ℝ) (hR : Measurable R)
    (φ : J → X → ℝ) (hφ : ∀ j, Measurable (φ j)) (ε : ℝ) (hε : ε ≤ 1 - ε) :
    Measurable (Function.uncurry (fixedGridPilot (n := n) Q R φ ε hε)) := by
  apply Finset.measurable_sum
  intro j _
  have hc : Measurable (fun data : Fin n → Ω =>
      (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ)) :=
    measurable_subtype_coe.comp (continuous_projIcc.measurable.comp
      (cellAverage_measurable (Q j) (hQ j) R hR))
  exact (hφ j).comp measurable_fst |>.mul (hc.comp measurable_snd)

theorem fixedGridPilot_smooth {Ω X J : Type*} [Fintype J]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (Q : J → Set Ω) (R : Ω → ℝ) (φ : J → X → ℝ)
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (ε : ℝ) (hε : ε ≤ 1 - ε) (data : Fin n → Ω) :
    ContDiff ℝ ∞ (fun x => fixedGridPilot Q R φ ε hε x data) := by
  exact ContDiff.sum (fun j _ => (hφ j).mul contDiff_const)

theorem fixedGridPilot_range {Ω X J : Type*} [Fintype J] {n : ℕ}
    (Q : J → Set Ω) (R : Ω → ℝ) (φ : J → X → ℝ)
    (ε : ℝ) (hε : ε ≤ 1 - ε) (x : X) (data : Fin n → Ω)
    (hφ : ∀ j, 0 ≤ φ j x) (hsum : ∑ j, φ j x = 1) :
    fixedGridPilot Q R φ ε hε x data ∈ Set.Icc ε (1 - ε) :=
  pilot_convex_range (fun j => φ j x) _ ε hφ hsum
    (fun j => (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data)).property)

/-- The actual finite-cell pilot has exponential uniform error. Its deterministic
local-bias premise is the geometric step supplied by a fine smooth partition. -/
theorem fixedGridPilot_uniform_exponential_tail {Ω X J : Type*} [Fintype J]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (Q : J → Set Ω) (hQ : ∀ j, MeasurableSet (Q j))
    (p : ℝ) (hp : 0 < p) (hπ : ∀ j, p ≤ μ.real (Q j))
    (R : Ω → ℝ) (hmR : Measurable R) (hR : ∀ x, R x ∈ Set.Icc (0 : ℝ) 1)
    (φ : J → X → ℝ) (D : Set X) (w : X → ℝ)
    (ε : ℝ) (hε : ε ≤ 1 - ε)
    (hm : ∀ j, cellMean μ (Q j) R ∈ Set.Icc ε (1 - ε))
    (hφ : ∀ x ∈ D, ∀ j, 0 ≤ φ j x) (hsum : ∀ x ∈ D, ∑ j, φ j x = 1)
    (ζ : ℝ) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hbias : ∀ x ∈ D, ∀ j, φ j x ≠ 0 → |cellMean μ (Q j) R - w x| ≤ ζ / 4) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {data | ∃ x ∈ D, ζ < |fixedGridPilot Q R φ ε hε x data - w x|} ≤
      (3 * Fintype.card J : ℝ) * Real.exp (-(n : ℝ) * p ^ 2 * ζ ^ 2 / 32) := by
  let bad : J → Set (Fin n → Ω) := fun j =>
    {data | ζ / 2 ≤ |cellAverage (Q j) R data - cellMean μ (Q j) R|}
  have hsub : {data : Fin n → Ω |
      ∃ x ∈ D, ζ < |fixedGridPilot Q R φ ε hε x data - w x|} ⊆ ⋃ j, bad j := by
    intro data hd
    obtain ⟨x, hx, herr⟩ := hd
    by_contra hnobad
    have hgood : ∀ j, |cellAverage (Q j) R data - cellMean μ (Q j) R| < ζ / 2 := by
      intro j
      exact lt_of_not_ge (fun hj => hnobad (Set.mem_iUnion.mpr ⟨j, hj⟩))
    have hc : ∀ j, |(Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ) -
        cellMean μ (Q j) R| ≤ |cellAverage (Q j) R data - cellMean μ (Q j) R| := by
      intro j
      have hh := Set.abs_projIcc_sub_projIcc hε
        (c := cellAverage (Q j) R data) (d := cellMean μ (Q j) R)
      rw [Set.projIcc_of_mem hε (hm j)] at hh
      exact hh
    have he := pilot_convex_error (fun j => φ j x)
      (fun j => (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ))
      (w x) (3 * ζ / 4) (hφ x hx) (hsum x hx) (fun j hj => by
        have ha := abs_sub_le (Set.projIcc ε (1 - ε) hε (cellAverage (Q j) R data) : ℝ)
          (cellMean μ (Q j) R) (w x)
        have hb := hbias x hx j hj
        have hg := (hc j).trans_lt (hgood j)
        linarith)
    change |fixedGridPilot Q R φ ε hε x data - w x| ≤ 3 * ζ / 4 at he
    linarith
  apply (measureReal_mono hsub).trans
  apply (measureReal_iUnion_fintype_le bad).trans
  have hb : ∀ j, (Measure.pi (fun _ : Fin n => μ)).real (bad j) ≤
      3 * Real.exp (-(n : ℝ) * p ^ 2 * ζ ^ 2 / 32) := by
    intro j
    have hh := cellAverage_uniform_exponential_tail μ hn (Q j) (hQ j) p hp (hπ j)
      R hmR hR (ζ / 2) (by positivity) (by linarith)
    have he : -(n : ℝ) * p ^ 2 * (ζ / 2) ^ 2 / 8 = -(n : ℝ) * p ^ 2 * ζ ^ 2 / 32 := by ring
    simpa only [he] using hh
  calc
    _ ≤ ∑ _j : J, 3 * Real.exp (-(n : ℝ) * p ^ 2 * ζ ^ 2 / 32) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp; ring

/-- Any explicit uniform exponential bound has the paper's shared-constant form. -/
lemma exponential_bound_shared_constant (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      M * Real.exp (-a * n) ≤ c⁻¹ * Real.exp (-c * n) := by
  let c := min a (1 / (M + 1))
  have hc : 0 < c := lt_min ha (one_div_pos.mpr (by linarith))
  have hca : c ≤ a := min_le_left _ _
  have hcM : c ≤ 1 / (M + 1) := min_le_right _ _
  have hmc : M ≤ c⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hc]
    have hm := (le_div_iff₀ (show 0 < M + 1 by linarith)).mp hcM
    nlinarith
  refine ⟨c, hc, fun n => ?_⟩
  calc
    _ ≤ c⁻¹ * Real.exp (-a * n) := mul_le_mul_of_nonneg_right hmc (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hca (show 0 ≤ (n : ℝ) by positivity)]))
      (inv_nonneg.mpr hc.le)

end RoughRegime.Applications
