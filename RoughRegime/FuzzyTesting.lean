module

public import RoughRegime.GeneralTesting


@[expose] public section
/-! Sharp testing and fuzzy-prior reduction for arbitrary observation spaces. -/
noncomputable section
open MeasureTheory Set Filter
namespace RoughRegime.GeneralTesting

theorem square_root_testing_sharp_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    7 * (a + b) / 16 - 4 * (Real.sqrt a - Real.sqrt b) ^ 2 ≤ min a b := by
  apply le_min
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (9 * Real.sqrt a - 8 * Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (8 * Real.sqrt a - 9 * Real.sqrt b), Real.sqrt_nonneg a, Real.sqrt_nonneg b]

theorem test_loss_sharp_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) (A : Set Ω) (hA : MeasurableSet A) :
    7 / 8 - 4 * hellingerSquared L R ≤ L.measure.real Aᶜ + R.measure.real A := by
  have hH := hellinger_integrable L R
  have hL := L.integrable.indicator hA.compl
  have hR := R.integrable.indicator hA
  have hp : (fun x => (7 / 16 : ℝ) * (L.density x + R.density x) -
      4 * (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) ≤ᵐ[μ]
      (fun x => Aᶜ.indicator L.density x + A.indicator R.density x) := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    have hl := square_root_testing_sharp_lower hx hy
    by_cases h : x ∈ A
    · rw [indicator_of_notMem (show x ∉ Aᶜ from fun hxA => hxA h),
        indicator_of_mem h, zero_add]
      convert hl.trans (min_le_right _ _) using 1; ring
    · rw [indicator_of_mem (show x ∈ Aᶜ from h), indicator_of_notMem h, add_zero]
      convert hl.trans (min_le_left _ _) using 1; ring
  have hi := integral_mono_ae
    (((L.integrable.add R.integrable).const_mul (7 / 16 : ℝ)).sub (hH.const_mul 4))
    (hL.add hR) hp
  change (∫ x, (7 / 16 : ℝ) * (L.density x + R.density x) -
    4 * (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ) ≤
    ∫ x, Aᶜ.indicator L.density x + A.indicator R.density x ∂μ at hi
  have hI : Integrable (fun x => (7 / 16 : ℝ) * (L.density x + R.density x)) μ :=
    (L.integrable.add R.integrable).const_mul _
  rw [integral_sub hI (hH.const_mul 4),
    integral_const_mul,
    integral_const_mul, integral_add L.integrable R.integrable,
    L.integral_one, R.integral_one, integral_add hL hR,
    ← L.measureReal_eq_integral_indicator Aᶜ hA.compl,
    ← R.measureReal_eq_integral_indicator A hA] at hi
  norm_num at hi
  unfold hellingerSquared
  linarith


/-- A fuzzy two-prior comparison on genuine joint parameter/data laws. The
observation marginals are supplied as equalities of measures; target
concentration is distinct from the estimator's error conclusion. -/
theorem fuzzy_joint_three_eighths {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (JL JR : Measure (W × Ω))
    [IsProbabilityMeasure JL] [IsProbabilityMeasure JR]
    (hJL : JL.map Prod.snd = L.measure) (hJR : JR.map Prod.snd = R.measure)
    (target : W → ℝ) (g : Ω → ℝ) (hg : Measurable g)
    (a b : ℝ) (hH : hellingerSquared L R ≤ 1 / 64)
    (hCL : JL.real {q | |b - a| / 4 < |target q.1 - a|} ≤ 1 / 32)
    (hCR : JR.real {q | |b - a| / 4 < |target q.1 - b|} ≤ 1 / 32) :
    (3 / 8 : ℝ) ≤ JL.real {q | |b - a| / 4 ≤ |g q.2 - target q.1|} ∨
      (3 / 8 : ℝ) ≤ JR.real {q | |b - a| / 4 ≤ |g q.2 - target q.1|} := by
  let A : Set Ω := {x | |g x - a| < |b - a| / 2}
  let E : Set (W × Ω) := {q | |b - a| / 4 ≤ |g q.2 - target q.1|}
  let CL : Set (W × Ω) := {q | |b - a| / 4 < |target q.1 - a|}
  let CR : Set (W × Ω) := {q | |b - a| / 4 < |target q.1 - b|}
  have hA : MeasurableSet A := measurableSet_lt (hg.sub measurable_const).abs measurable_const
  have hobsL : L.measure.real Aᶜ = JL.real (Prod.snd ⁻¹' Aᶜ) := by
    rw [← hJL, measureReal_def, Measure.map_apply measurable_snd hA.compl]
    rfl
  have hobsR : R.measure.real A = JR.real (Prod.snd ⁻¹' A) := by
    rw [← hJR, measureReal_def, Measure.map_apply measurable_snd hA]
    rfl
  have hsubL : Prod.snd ⁻¹' Aᶜ ⊆ E ∪ CL := by
    intro q hq
    by_cases hcl : q ∈ CL
    · exact Or.inr hcl
    · apply Or.inl
      have hc : |target q.1 - a| ≤ |b - a| / 4 := le_of_not_gt hcl
      have ho : |b - a| / 2 ≤ |g q.2 - a| := le_of_not_gt hq
      have htri : |g q.2 - a| ≤ |g q.2 - target q.1| + |target q.1 - a| :=
        abs_sub_le _ _ _
      change |b - a| / 4 ≤ |g q.2 - target q.1|
      linarith
  have hsubR : Prod.snd ⁻¹' A ⊆ E ∪ CR := by
    intro q hq
    by_cases hcr : q ∈ CR
    · exact Or.inr hcr
    · apply Or.inl
      have hc : |target q.1 - b| ≤ |b - a| / 4 := le_of_not_gt hcr
      have ho : |g q.2 - a| < |b - a| / 2 := hq
      have hsep : |b - a| ≤ |g q.2 - a| + |g q.2 - b| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le b (g q.2) a
      have htri : |g q.2 - b| ≤ |g q.2 - target q.1| + |target q.1 - b| :=
        abs_sub_le _ _ _
      change |b - a| / 4 ≤ |g q.2 - target q.1|
      linarith
  have hL := (measureReal_mono (μ := JL) hsubL).trans (measureReal_union_le (μ := JL) E CL)
  have hR := (measureReal_mono (μ := JR) hsubR).trans (measureReal_union_le (μ := JR) E CR)
  have htest := test_loss_sharp_lower L R A hA
  rw [hobsL, hobsR] at htest
  by_contra h
  push Not at h
  change JL.real E < 3 / 8 ∧ JR.real E < 3 / 8 at h
  change JL.real CL ≤ 1 / 32 at hCL
  change JR.real CR ≤ 1 / 32 at hCR
  linarith

theorem fuzzy_joint_error_budget {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (JL JR : Measure (W × Ω))
    [IsProbabilityMeasure JL] [IsProbabilityMeasure JR]
    (hJL : JL.map Prod.snd = L.measure) (hJR : JR.map Prod.snd = R.measure)
    (target : W → ℝ) (g : Ω → ℝ) (hg : Measurable g)
    (a b q : ℝ)
    (hbudget : 2 * q ≤ 7 / 8 - 4 * hellingerSquared L R -
      JL.real {r | |b - a| / 4 < |target r.1 - a|} -
      JR.real {r | |b - a| / 4 < |target r.1 - b|}) :
    q ≤ JL.real {q | |b - a| / 4 ≤ |g q.2 - target q.1|} ∨
      q ≤ JR.real {q | |b - a| / 4 ≤ |g q.2 - target q.1|} := by
  let A : Set Ω := {x | |g x - a| < |b - a| / 2}
  let E : Set (W × Ω) := {q | |b - a| / 4 ≤ |g q.2 - target q.1|}
  let CL : Set (W × Ω) := {q | |b - a| / 4 < |target q.1 - a|}
  let CR : Set (W × Ω) := {q | |b - a| / 4 < |target q.1 - b|}
  have hA : MeasurableSet A := measurableSet_lt (hg.sub measurable_const).abs measurable_const
  have hobsL : L.measure.real Aᶜ = JL.real (Prod.snd ⁻¹' Aᶜ) := by
    rw [← hJL, measureReal_def, Measure.map_apply measurable_snd hA.compl]
    rfl
  have hobsR : R.measure.real A = JR.real (Prod.snd ⁻¹' A) := by
    rw [← hJR, measureReal_def, Measure.map_apply measurable_snd hA]
    rfl
  have hsubL : Prod.snd ⁻¹' Aᶜ ⊆ E ∪ CL := by
    intro q hq
    by_cases hcl : q ∈ CL
    · exact Or.inr hcl
    · apply Or.inl
      have hc : |target q.1 - a| ≤ |b - a| / 4 := le_of_not_gt hcl
      have ho : |b - a| / 2 ≤ |g q.2 - a| := le_of_not_gt hq
      have htri : |g q.2 - a| ≤ |g q.2 - target q.1| + |target q.1 - a| :=
        abs_sub_le _ _ _
      change |b - a| / 4 ≤ |g q.2 - target q.1|
      linarith
  have hsubR : Prod.snd ⁻¹' A ⊆ E ∪ CR := by
    intro q hq
    by_cases hcr : q ∈ CR
    · exact Or.inr hcr
    · apply Or.inl
      have hc : |target q.1 - b| ≤ |b - a| / 4 := le_of_not_gt hcr
      have ho : |g q.2 - a| < |b - a| / 2 := hq
      have hsep : |b - a| ≤ |g q.2 - a| + |g q.2 - b| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le b (g q.2) a
      have htri : |g q.2 - b| ≤ |g q.2 - target q.1| + |target q.1 - b| :=
        abs_sub_le _ _ _
      change |b - a| / 4 ≤ |g q.2 - target q.1|
      linarith
  have hL := (measureReal_mono (μ := JL) hsubL).trans (measureReal_union_le (μ := JL) E CL)
  have hR := (measureReal_mono (μ := JR) hsubR).trans (measureReal_union_le (μ := JR) E CR)
  have htest := test_loss_sharp_lower L R A hA
  rw [hobsL, hobsR] at htest
  by_contra h
  push Not at h
  change JL.real E < q ∧ JR.real E < q at h
  change 2 * q ≤ 7 / 8 - 4 * hellingerSquared L R - JL.real CL - JR.real CR at hbudget
  linarith

open ProbabilityTheory
open scoped ENNReal

/-- Averaging error under a genuine parameter/data experiment cannot exceed
its supremum over parameters. -/
theorem joint_error_le_sup {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    (prior : Measure W) [IsProbabilityMeasure prior]
    (K : Kernel W Ω) [IsMarkovKernel K] (target : W → ℝ) (ht : Measurable target)
    (g : Ω → ℝ) (hg : Measurable g) (δ : ℝ) :
    (prior ⊗ₘ K) {q | δ ≤ |g q.2 - target q.1|} ≤
      ⨆ w, K w {x | δ ≤ |g x - target w|} := by
  have hE : MeasurableSet {q : W × Ω | δ ≤ |g q.2 - target q.1|} :=
    measurableSet_le measurable_const ((hg.comp measurable_snd).sub (ht.comp measurable_fst)).abs
  rw [Measure.compProd_apply hE]
  calc
    _ ≤ ∫⁻ _ : W, ⨆ w, K w {x | δ ≤ |g x - target w|} ∂prior :=
      lintegral_mono fun w => le_iSup (fun w => K w {x | δ ≤ |g x - target w|}) w
    _ = _ := by simp

/-- Genuine Bayesian fuzzy testing for a common Markov observation kernel.
The conclusion is the usual worst-parameter tail bound, and priors may be
continuous or countable. -/
theorem fuzzy_kernel_three_eighths {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure) (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target) (g : Ω → ℝ) (hg : Measurable g)
    (a b : ℝ) (hH : hellingerSquared L R ≤ 1 / 64)
    (hCL : PL.real {w | |b - a| / 4 < |target w - a|} ≤ 1 / 32)
    (hCR : PR.real {w | |b - a| / 4 < |target w - b|} ≤ 1 / 32) :
    (3 / 8 : ℝ≥0∞) ≤ ⨆ w, K w {x | |b - a| / 4 ≤ |g x - target w|} := by
  have hconc (P : Measure W) [IsProbabilityMeasure P] (c : ℝ) :
      (P ⊗ₘ K).real {q | |b - a| / 4 < |target q.1 - c|} =
        P.real {w | |b - a| / 4 < |target w - c|} := by
    have hS : MeasurableSet {w | |b - a| / 4 < |target w - c|} :=
      measurableSet_lt measurable_const (ht.sub measurable_const).abs
    have hf := Measure.fst_compProd P K
    change (P ⊗ₘ K).real (Prod.fst ⁻¹' {w | |b - a| / 4 < |target w - c|}) = _
    calc
      _ = (P ⊗ₘ K).fst.real {w | |b - a| / 4 < |target w - c|} := by
        rw [measureReal_def, measureReal_def, Measure.fst_apply hS]
      _ = _ := congrArg (fun Q : Measure W => Q.real {w | |b - a| / 4 < |target w - c|}) hf
  have hcL := hCL
  have hcR := hCR
  rw [← hconc PL a] at hcL
  rw [← hconc PR b] at hcR
  have h := fuzzy_joint_three_eighths L R (PL ⊗ₘ K) (PR ⊗ₘ K)
    hPL hPR target g hg a b hH hcL hcR
  have hconvert (P : Measure W) [IsProbabilityMeasure P]
      (hP : (3 / 8 : ℝ) ≤ (P ⊗ₘ K).real {q | |b - a| / 4 ≤ |g q.2 - target q.1|}) :
      (3 / 8 : ℝ≥0∞) ≤ ⨆ w, K w {x | |b - a| / 4 ≤ |g x - target w|} := by
    have he := ENNReal.ofReal_le_of_le_toReal hP
    have he' : (3 / 8 : ℝ≥0∞) ≤ (P ⊗ₘ K) {q | |b - a| / 4 ≤ |g q.2 - target q.1|} := by
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat] using he
    exact he'.trans (joint_error_le_sup P K target ht g hg (|b - a| / 4))
  rcases h with h | h
  · exact hconvert PL h
  · exact hconvert PR h

/-- A testing budget with arbitrary prior concentration and a common genuine
observation kernel. This leaves a strict margin for de-Poissonization. -/
theorem fuzzy_kernel_error_budget {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure) (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target) (g : Ω → ℝ) (hg : Measurable g)
    (a b q : ℝ)
    (hbudget : 2 * q ≤ 7 / 8 - 4 * hellingerSquared L R -
      PL.real {w | |b - a| / 4 < |target w - a|} -
      PR.real {w | |b - a| / 4 < |target w - b|}) :
    ENNReal.ofReal q ≤ ⨆ w, K w {x | |b - a| / 4 ≤ |g x - target w|} := by
  have hconc (P : Measure W) [IsProbabilityMeasure P] (c : ℝ) :
      (P ⊗ₘ K).real {r | |b - a| / 4 < |target r.1 - c|} =
        P.real {w | |b - a| / 4 < |target w - c|} := by
    have hS : MeasurableSet {w | |b - a| / 4 < |target w - c|} :=
      measurableSet_lt measurable_const (ht.sub measurable_const).abs
    change (P ⊗ₘ K).real (Prod.fst ⁻¹' {w | |b - a| / 4 < |target w - c|}) = _
    calc
      _ = (P ⊗ₘ K).fst.real {w | |b - a| / 4 < |target w - c|} := by
        rw [measureReal_def, measureReal_def, Measure.fst_apply hS]
      _ = _ := congrArg (fun Q : Measure W => Q.real {w | |b - a| / 4 < |target w - c|})
        (Measure.fst_compProd P K)
  have hb := hbudget
  rw [← hconc PL a, ← hconc PR b] at hb
  have h := fuzzy_joint_error_budget L R (PL ⊗ₘ K) (PR ⊗ₘ K)
    hPL hPR target g hg a b q hb
  have hconvert (P : Measure W) [IsProbabilityMeasure P]
      (hP : q ≤ (P ⊗ₘ K).real {r | |b - a| / 4 ≤ |g r.2 - target r.1|}) :
      ENNReal.ofReal q ≤ ⨆ w, K w {x | |b - a| / 4 ≤ |g x - target w|} :=
    (ENNReal.ofReal_le_of_le_toReal hP).trans
      (joint_error_le_sup P K target ht g hg (|b - a| / 4))
  rcases h with h | h
  · exact hconvert PL h
  · exact hconvert PR h


/-- The prior concentration required by fuzzy testing follows from actual
variance. -/
theorem prior_concentration_of_variance {W : Type*} [MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] (target : W → ℝ) (ht : MemLp target 2 P)
    (sep : ℝ) (hs : 0 < sep) (hv : variance target P ≤ sep ^ 2 / 512) :
    P.real {w | sep / 4 < |target w - ∫ w, target w ∂P|} ≤ 1 / 32 := by
  have htail := meas_ge_le_variance_div_sq ht (c := sep / 4) (by positivity)
  have hq : variance target P / (sep / 4) ^ 2 ≤ 1 / 32 := by
    apply (div_le_iff₀ (by positivity : 0 < (sep / 4) ^ 2)).mpr
    nlinarith
  have hENN : P {w | sep / 4 < |target w - ∫ w, target w ∂P|} ≤
      ENNReal.ofReal (1 / 32 : ℝ) :=
    (measure_mono (show {w | sep / 4 < |target w - ∫ w, target w ∂P|} ⊆
      {w | sep / 4 ≤ |target w - ∫ w, target w ∂P|} from by
        intro w hw
        change sep / 4 < |target w - ∫ w, target w ∂P| at hw
        change sep / 4 ≤ |target w - ∫ w, target w ∂P|
        exact hw.le)).trans
      (htail.trans (ENNReal.ofReal_le_ofReal hq))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 32)] using hreal

/-- Fuzzy testing stated entirely in terms of true prior means and variances. -/
theorem fuzzy_kernel_variance {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure) (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target) (htL : MemLp target 2 PL) (htR : MemLp target 2 PR)
    (g : Ω → ℝ) (hg : Measurable g)
    (hH : hellingerSquared L R ≤ 1 / 64)
    (hsep : 0 < |(∫ w, target w ∂PR) - ∫ w, target w ∂PL|)
    (hvL : variance target PL ≤ |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| ^ 2 / 512)
    (hvR : variance target PR ≤ |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| ^ 2 / 512) :
    (3 / 8 : ℝ≥0∞) ≤ ⨆ w, K w
      {x | |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| / 4 ≤ |g x - target w|} := by
  apply fuzzy_kernel_three_eighths L R PL PR K hPL hPR target ht g hg _ _ hH
  · exact prior_concentration_of_variance PL target htL _ hsep hvL
  · exact prior_concentration_of_variance PR target htR _ hsep hvR

theorem prior_concentration_strong {W : Type*} [MeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] (target : W → ℝ) (ht : MemLp target 2 P)
    (sep : ℝ) (hs : 0 < sep) (hv : variance target P ≤ sep ^ 2 / 1024) :
    P.real {w | sep / 4 < |target w - ∫ w, target w ∂P|} ≤ 1 / 64 := by
  have htail := meas_ge_le_variance_div_sq ht (c := sep / 4) (by positivity)
  have hq : variance target P / (sep / 4) ^ 2 ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < (sep / 4) ^ 2)).mpr
    nlinarith
  have hENN : P {w | sep / 4 < |target w - ∫ w, target w ∂P|} ≤
      ENNReal.ofReal (1 / 64 : ℝ) :=
    (measure_mono (show {w | sep / 4 < |target w - ∫ w, target w ∂P|} ⊆
      {w | sep / 4 ≤ |target w - ∫ w, target w ∂P|} from by
        intro w hw
        change sep / 4 < |target w - ∫ w, target w ∂P| at hw
        change sep / 4 ≤ |target w - ∫ w, target w ∂P|
        exact hw.le)).trans
      (htail.trans (ENNReal.ofReal_le_ofReal hq))
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 64)] using hreal


/-- A strict testing margin survives the exponentially small loss from
using the first fixed number of points of a Poisson process. -/
theorem fuzzy_kernel_variance_strong {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    {μ : Measure Ω} (L R : DensityLaw μ) (PL PR : Measure W)
    [IsProbabilityMeasure PL] [IsProbabilityMeasure PR]
    (K : Kernel W Ω) [IsMarkovKernel K]
    (hPL : (PL ⊗ₘ K).map Prod.snd = L.measure) (hPR : (PR ⊗ₘ K).map Prod.snd = R.measure)
    (target : W → ℝ) (ht : Measurable target) (htL : MemLp target 2 PL) (htR : MemLp target 2 PR)
    (g : Ω → ℝ) (hg : Measurable g)
    (hH : hellingerSquared L R ≤ 1 / 128)
    (hsep : 0 < |(∫ w, target w ∂PR) - ∫ w, target w ∂PL|)
    (hvL : variance target PL ≤ |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| ^ 2 / 1024)
    (hvR : variance target PR ≤ |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| ^ 2 / 1024) :
    (13 / 32 : ℝ≥0∞) ≤ ⨆ w, K w
      {x | |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| / 4 ≤ |g x - target w|} := by
  have hCL := prior_concentration_strong PL target htL _ hsep hvL
  have hCR := prior_concentration_strong PR target htR _ hsep hvR
  have hbudget : 2 * (13 / 32 : ℝ) ≤ 7 / 8 - 4 * hellingerSquared L R -
      PL.real {w | |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| / 4 <
        |target w - ∫ w, target w ∂PL|} -
      PR.real {w | |(∫ w, target w ∂PR) - ∫ w, target w ∂PL| / 4 <
        |target w - ∫ w, target w ∂PR|} := by linarith
  have h := fuzzy_kernel_error_budget L R PL PR K hPL hPR target ht g hg
    (∫ w, target w ∂PL) (∫ w, target w ∂PR) (13 / 32) hbudget
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 32),
    ENNReal.ofReal_ofNat] using h

end RoughRegime.GeneralTesting
