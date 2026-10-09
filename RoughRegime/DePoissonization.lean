module

public import RoughRegime.PoissonKernelMixtures


@[expose] public section
/-! Parameter-independent first-n extraction from a Poisson count-and-mark
experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Y : Type*} [MeasurableSpace Y]

 def firstMarks {n m : ℕ} (h : n ≤ m) (xs : Fin m → Y) : Fin n → Y :=
   fun i => xs (Fin.castLE h i)

 theorem firstMarks_measurable {n m : ℕ} (h : n ≤ m) : Measurable (@firstMarks Y n m h) :=
   measurable_pi_iff.mpr fun _ => measurable_pi_apply _

 theorem firstMarks_preserving (P : Measure Y) [IsProbabilityMeasure P]
    {n m : ℕ} (h : n ≤ m) : MeasurePreserving (@firstMarks Y n m h)
      (Measure.pi (fun _ : Fin m => P)) (Measure.pi (fun _ : Fin n => P)) := by
  refine ⟨firstMarks_measurable h, ?_⟩
  have hi := iIndepFun_pi (μ := fun _ : Fin m => P) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp (Fin.castLE_injective h)
  have he := hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (Fin.castLE h i)).aemeasurable)
  unfold firstMarks
  simpa only [(measurePreserving_eval (fun _ : Fin m => P) _).map_eq] using he

 def liftEstimator (n : ℕ) (g : (Fin n → Y) → ℝ) (fallback : ℝ)
    (q : PointConfiguration Y) : ℝ := if h : n ≤ q.1 then g (firstMarks h q.2) else fallback

 theorem liftEstimator_measurable (n : ℕ) (g : (Fin n → Y) → ℝ) (hg : Measurable g) (fallback : ℝ) :
    Measurable (liftEstimator n g fallback) := by
  apply measurable_point_function
  intro m
  by_cases h : n ≤ m
  · simpa only [liftEstimator, dite_eq_left h, Function.comp_def] using hg.comp (firstMarks_measurable h)
  · simp only [liftEstimator, dite_eq_right h]
    exact measurable_const

 theorem referenceProcess_apply (P : Measure Y) [IsProbabilityMeasure P] (rate : ℝ≥0)
    (s : Set (PointConfiguration Y)) (hs : MeasurableSet s) :
    referenceProcess P rate s = ∑' m, ENNReal.ofReal (Lower.poissonMass rate m) *
      (Measure.pi (fun _ : Fin m => P)) ((@Sigma.mk ℕ (fun k => Fin k → Y) m) ⁻¹' s) := by
  rw [referenceProcess, Measure.sum_apply _ hs]
  simp_rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_point_mk _) hs]

 theorem liftEstimator_tail_le (P : Measure Y) [IsProbabilityMeasure P] (rate : ℝ≥0)
    (n : ℕ) (g : (Fin n → Y) → ℝ) (hg : Measurable g) (fallback target δ : ℝ) :
    referenceProcess P rate {q | δ ≤ |liftEstimator n g fallback q - target|} ≤
      ProbabilityTheory.poissonMeasure rate {m | m < n} +
        (Measure.pi (fun _ : Fin n => P)) {xs | δ ≤ |g xs - target|} := by
  let E : Set (Fin n → Y) := {xs | δ ≤ |g xs - target|}
  have hE : MeasurableSet E := measurableSet_le measurable_const (hg.sub measurable_const).abs
  have hG : MeasurableSet {q | δ ≤ |liftEstimator n g fallback q - target|} :=
    measurableSet_le measurable_const ((liftEstimator_measurable n g hg fallback).sub measurable_const).abs
  have hBad : MeasurableSet {m : ℕ | m < n} :=
    measurableSet_lt measurable_id measurable_const
  have hpois : ProbabilityTheory.poissonMeasure rate {m | m < n} =
      ∑' m, ENNReal.ofReal (Lower.poissonMass rate m) * (if m < n then 1 else 0) := by
    rw [ProbabilityTheory.poissonMeasure, Measure.sum_apply _ hBad]
    apply tsum_congr
    intro m
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hBad]
    by_cases hm : m < n <;> simp [Lower.poissonMass, hm]
  have hmass : (∑' m, ENNReal.ofReal (Lower.poissonMass rate m)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => Lower.poissonMass_nonneg rate rate.2 m)
      (Lower.poissonMass_hasSum rate).summable, (Lower.poissonMass_hasSum rate).tsum_eq]
    norm_num
  rw [referenceProcess_apply P rate _ hG, hpois]
  have hpoint (m : ℕ) : (Measure.pi (fun _ : Fin m => P))
      ((@Sigma.mk ℕ (fun k => Fin k → Y) m) ⁻¹' {q | δ ≤ |liftEstimator n g fallback q - target|}) ≤
      (if m < n then 1 else 0) + (Measure.pi (fun _ : Fin n => P)) E := by
    by_cases h : n ≤ m
    · have he := (firstMarks_preserving P h).map_eq
      rw [← he, Measure.map_apply (firstMarks_measurable h) hE]
      simp only [show ¬m < n from Nat.not_lt.mpr h, ite_false, zero_add]
      have heq : ((@Sigma.mk ℕ (fun k => Fin k → Y) m) ⁻¹'
          {q | δ ≤ |liftEstimator n g fallback q - target|}) = firstMarks h ⁻¹' E := by
        ext xs
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, liftEstimator, dite_eq_left h, E]
      rw [heq]
    · simp only [show m < n from Nat.lt_of_not_ge h, ite_true]
      calc
        _ ≤ (Measure.pi (fun _ : Fin m => P)) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ _ := le_add_right le_rfl
  calc
    _ ≤ ∑' m, ENNReal.ofReal (Lower.poissonMass rate m) *
        ((if m < n then 1 else 0) + (Measure.pi (fun _ : Fin n => P)) E) :=
      ENNReal.tsum_le_tsum fun m => by gcongr; exact hpoint m
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]

 theorem poisson_count_below_half (n : ℕ) :
    (ProbabilityTheory.poissonMeasure (2 * (n : ℝ≥0))).real {m | m < n} ≤
      Real.exp (-(1 - Real.log 2) * n) := by
  let rate : ℝ≥0 := 2 * n
  have hi : Integrable (fun m : ℕ => (1 / 2 : ℝ) ^ m) (ProbabilityTheory.poissonMeasure rate) :=
    bounded_integrable _ _ (measurable_of_countable _) 1 (fun m => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (by norm_num) (by norm_num))
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := ProbabilityTheory.poissonMeasure rate)
    (Filter.Eventually.of_forall (fun m : ℕ => by positivity : ∀ m : ℕ, 0 ≤ (1 / 2 : ℝ) ^ m))
    hi ((1 / 2 : ℝ) ^ n)
  rw [poisson_count_generating] at hm
  have hs : {m : ℕ | m < n} ⊆ {m : ℕ | (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m} := by
    intro m hmn
    change (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt hmn)
  have hb := mul_le_mul_of_nonneg_left (measureReal_mono (μ := ProbabilityTheory.poissonMeasure rate) hs)
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n)
  have hquot : (ProbabilityTheory.poissonMeasure rate).real {m | m < n} ≤
      Real.exp ((rate : ℝ) * ((1 / 2 : ℝ) - 1)) / (1 / 2 : ℝ) ^ n :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hb.trans hm)
  apply hquot.trans_eq
  have hpow : (1 / 2 : ℝ) ^ n = Real.exp ((n : ℝ) * (-Real.log 2)) := by
    rw [Real.exp_nat_mul, ← Real.log_inv, Real.exp_log (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    norm_num
  rw [hpow, ← Real.exp_sub]
  congr 1
  dsimp [rate]
  norm_num
  ring

 theorem poisson_count_bad_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (ProbabilityTheory.poissonMeasure (2 * (n : ℝ≥0))).real {m | m < n})
      Filter.atTop (nhds 0) := by
  have hc : 0 < 1 - Real.log 2 := by
    have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) poisson_count_below_half
  have hn : Filter.Tendsto (fun n : ℕ => -(1 - Real.log 2) * (n : ℝ)) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp hn

variable {Seed : Type*} [MeasurableSpace Seed]

def liftEstimatorWithSeed (n : ℕ) (g : ((Fin n → Y) × Seed) → ℝ) (fallback : ℝ)
    (q : PointConfiguration Y × Seed) : ℝ :=
  if h : n ≤ q.1.1 then g (firstMarks h q.1.2, q.2) else fallback

theorem liftEstimatorWithSeed_measurable (n : ℕ) (g : ((Fin n → Y) × Seed) → ℝ)
    (hg : Measurable g) (fallback : ℝ) : Measurable (liftEstimatorWithSeed n g fallback) := by
  have hm : Measurable (fun q : Seed × PointConfiguration Y => liftEstimatorWithSeed n g fallback (q.2, q.1)) := by
    apply measurable_point_product_function
    intro m
    by_cases h : n ≤ m
    · simpa only [liftEstimatorWithSeed, dite_eq_left h, Function.comp_def] using
        hg.comp (((firstMarks_measurable h).comp measurable_snd).prodMk measurable_fst)
    · simp only [liftEstimatorWithSeed, dite_eq_right h]
      exact measurable_const
  exact hm.comp measurable_swap

theorem liftEstimatorWithSeed_tail_le (P : Measure Y) [IsProbabilityMeasure P]
    (R : Measure Seed) [IsProbabilityMeasure R] (rate : ℝ≥0)
    (n : ℕ) (g : ((Fin n → Y) × Seed) → ℝ) (hg : Measurable g) (fallback target δ : ℝ) :
    ((referenceProcess P rate).prod R) {q | δ ≤ |liftEstimatorWithSeed n g fallback q - target|} ≤
      ProbabilityTheory.poissonMeasure rate {m | m < n} +
        ((Measure.pi (fun _ : Fin n => P)).prod R) {q | δ ≤ |g q - target|} := by
  have hE : MeasurableSet {q | δ ≤ |g q - target|} :=
    measurableSet_le measurable_const (hg.sub measurable_const).abs
  have hG : MeasurableSet {q | δ ≤ |liftEstimatorWithSeed n g fallback q - target|} :=
    measurableSet_le measurable_const ((liftEstimatorWithSeed_measurable n g hg fallback).sub measurable_const).abs
  rw [Measure.prod_apply_symm hG]
  calc
    _ ≤ MeasureTheory.lintegral R (fun seed : Seed => ProbabilityTheory.poissonMeasure rate {m | m < n} +
        (Measure.pi (fun _ : Fin n => P)) {xs | δ ≤ |g (xs, seed) - target|}) :=
      lintegral_mono fun seed => liftEstimator_tail_le P rate n (fun xs => g (xs, seed))
        (hg.comp (measurable_id.prodMk measurable_const)) fallback target δ
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        Measure.prod_apply_symm (μ := Measure.pi (fun _ : Fin n => P)) (ν := R) hE]
      rfl


/-- The genuine count-and-mark reduction preserves the source testing
constant, using the strict Poisson testing margin. The estimator may use
an arbitrary independent probability seed. -/
theorem depoissonized_worst_tail {W : Type*} (P : W → ProbabilityMeasure Y)
    (R : Measure Seed) [IsProbabilityMeasure R] (rate : ℝ≥0)
    (n : ℕ) (g : ((Fin n → Y) × Seed) → ℝ) (hg : Measurable g)
    (fallback : ℝ) (target : W → ℝ) (δ : ℝ)
    (hstrong : (13 / 32 : ℝ≥0∞) ≤ ⨆ w,
      ((referenceProcess (P w) rate).prod R)
        {q | δ ≤ |liftEstimatorWithSeed n g fallback q - target w|})
    (hcount : ProbabilityTheory.poissonMeasure rate {m | m < n} ≤ (1 / 32 : ℝ≥0∞)) :
    (3 / 8 : ℝ≥0∞) ≤ ⨆ w,
      ((Measure.pi (fun _ : Fin n => (P w : Measure Y))).prod R)
        {q | δ ≤ |g q - target w|} := by
  have hsup : (⨆ w, ((referenceProcess (P w) rate).prod R)
      {q | δ ≤ |liftEstimatorWithSeed n g fallback q - target w|}) ≤
      (1 / 32 : ℝ≥0∞) + ⨆ w,
        ((Measure.pi (fun _ : Fin n => (P w : Measure Y))).prod R)
          {q | δ ≤ |g q - target w|} := by
    apply iSup_le
    intro w
    have hw := liftEstimatorWithSeed_tail_le (Y := Y) (Seed := Seed)
      (P w : Measure Y) R rate n g hg fallback (target w) δ
    have he : ((Measure.pi (fun _ : Fin n => (P w : Measure Y))).prod R)
        {q | δ ≤ |g q - target w|} ≤ ⨆ w : W,
        ((Measure.pi (fun _ : Fin n => (P w : Measure Y))).prod R)
          {q | δ ≤ |g q - target w|} := le_iSup (fun w : W =>
            ((Measure.pi (fun _ : Fin n => (P w : Measure Y))).prod R)
              {q | δ ≤ |g q - target w|}) w
    exact hw.trans (add_le_add hcount he)
  apply ENNReal.le_of_add_le_add_left (a := (1 / 32 : ℝ≥0∞)) (by norm_num)
  have hmargin : (1 / 32 : ℝ≥0∞) + 3 / 8 = 13 / 32 := by
    have hr : (1 / 32 : ℝ) + 3 / 8 = 13 / 32 := by norm_num
    have he := congrArg ENNReal.ofReal hr
    simpa only [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (by norm_num : (0 : ℝ) ≤ 3 / 8),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 32),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_one] using he
  rw [hmargin]
  exact hstrong.trans hsup

/-- For the paper's Poisson mean2n, the fixed sample comparison eventually
has the required loss at most1/32. -/
theorem poisson_count_eventually_small : ∀ᶠ n : ℕ in Filter.atTop,
    ProbabilityTheory.poissonMeasure (2 * (n : ℝ≥0)) {m | m < n} ≤ (1 / 32 : ℝ≥0∞) := by
  have hsmall := poisson_count_bad_tendsto_zero.eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 32))
  filter_upwards [hsmall] with n hn
  have hfinite : ProbabilityTheory.poissonMeasure (2 * (n : ℝ≥0)) {m | m < n} ≠ ⊤ :=
    measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal hfinite (by norm_num)).mp
  change (ProbabilityTheory.poissonMeasure (2 * (n : ℝ≥0)) {m | m < n}).toReal <
    (1 / 32 : ℝ) at hn
  simpa using hn.le

end RoughRegime.PoissonMeasure
