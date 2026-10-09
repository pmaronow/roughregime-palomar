module

public import RoughRegime.PoissonNormalization


@[expose] public section
/-! The full independent-pair comparison expressed using literal physical
coefficients on the two-block measure, rather than normalized densities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
variable {p : ℕ} [NeZero p] (ν : Fin p → Measure H) (μ : Measure X) (κ : Measure Z)
variable [∀ i, IsProbabilityMeasure (ν i)] [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]

def AffinePhaseField.physicalGammaMaximum (F : Fin p → AffinePhaseField H X)
    (Au Av : ℝ) (M j : ℕ) : ℝ :=
  finiteMaximum fun i => (F i).gammaNorm (ν i) ((2 : ENNReal) • μ) Au Av M j

def physicalComparisonConstant (K A T : ℝ) : ℝ :=
  1 + K * T + K * A * T + K * T ^ 2 * A ^ 2 + K * T ^ 4

theorem AffinePhaseField.physical_pair_comparison (F : Fin p → AffinePhaseField H X)
    (hm : ∀ i, (F i).IsMeasurable) (Au Av Craw C S a A T Λ : ℝ)
    (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hCr : 0 ≤ Craw) (hC : 0 ≤ C) (hS : 0 ≤ S) (hA : 0 ≤ A) (ha : a ^ 2 ≤ A)
    (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) (hb : ∀ i, (F i).Bounded Craw) (hscale : |a| * Craw ≤ C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ i q, (∫ y, ((F i).scale a).markedFactor Au Av s q y ∂μ.prod κ) = 0)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ i q y, c ≤ 1 + ((F i).scale a).markedFactor Au Av s q y)
    (M : ℕ) (rate : ℝ≥0) (R : ℝ) (hRate : (rate : ℝ) ≤ R) (hRateScale : (rate : ℝ) ≤ T * Λ) :
    let K := comparisonConstant C S c R
    let Cstar := physicalComparisonConstant K A T
    let Fn := fun i => (F i).scale a
    let L := fun i => (Fn i).poissonLaw (ν i) μ κ ((F i).scale_isMeasurable (hm i) a) Au Av C S
      hAu hAu1 hAv hAv1 hC hS
      ⟨fun h x => (((F i).scale_bounded a Craw (hb i)).c h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).a h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).b h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).hu h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).hv h x).trans hscale⟩
      s hs hbs (hzero i) c hc (hlow i) M rate true
    let Rlaw := fun i => (Fn i).poissonLaw (ν i) μ κ ((F i).scale_isMeasurable (hm i) a) Au Av C S
      hAu hAu1 hAv hAv1 hC hS
      ⟨fun h x => (((F i).scale_bounded a Craw (hb i)).c h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).a h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).b h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).hu h x).trans hscale,
       fun h x => (((F i).scale_bounded a Craw (hb i)).hv h x).trans hscale⟩
      s hs hbs (hzero i) c hc (hlow i) M rate false
    1 ≤ Cstar ∧ GeneralTesting.hellingerSquared (LowerMeasure.productDensityLaw L)
      (LowerMeasure.productDensityLaw Rlaw) ≤
      Cstar * p * Λ ^ 2 * (∑' j, if M ≤ j then
        (Cstar * Λ) ^ j / j.factorial * AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j else 0) +
      Cstar * p * Λ ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
        ((Cstar * Λ) ^ M / M.factorial) := by
  let Fn := fun i => (F i).scale a
  have hmFn (i : Fin p) : (Fn i).IsMeasurable := (F i).scale_isMeasurable (hm i) a
  have hbFn (i : Fin p) : (Fn i).Bounded C := by
    have hi := (F i).scale_bounded a Craw (hb i)
    exact ⟨fun h x => (hi.c h x).trans hscale, fun h x => (hi.a h x).trans hscale,
      fun h x => (hi.b h x).trans hscale, fun h x => (hi.hu h x).trans hscale,
      fun h x => (hi.hv h x).trans hscale⟩
  let K := comparisonConstant C S c R
  let Cstar := physicalComparisonConstant K A T
  have hK : 0 ≤ K := (le_trans zero_le_one (comparisonConstant_bounds C S c R hc).1)
  have hn0 : 0 ≤ K * T := by positivity
  have hn1 : 0 ≤ K * A * T := by positivity
  have hn2 : 0 ≤ K * T ^ 2 * A ^ 2 := by positivity
  have hn3 : 0 ≤ K * T ^ 4 := by positivity
  have hCKAT : K * A * T ≤ Cstar := by dsimp [Cstar, physicalComparisonConstant]; linarith
  have hChead : K * T ^ 2 * A ^ 2 ≤ Cstar := by dsimp [Cstar, physicalComparisonConstant]; linarith
  have hCrem : K * T ^ 4 ≤ Cstar := by dsimp [Cstar, physicalComparisonConstant]; linarith
  have hCstar1 : 1 ≤ Cstar := by dsimp [Cstar, physicalComparisonConstant]; linarith
  have hCstar : 0 ≤ Cstar := zero_le_one.trans hCstar1
  have hmax (j : ℕ) : AffinePhaseField.pairGammaMaximum ν μ Fn Au Av M j ≤
      A ^ (j + 2) * AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j := by
    change finiteMaximum (fun i => (Fn i).gammaNorm (ν i) μ Au Av M j) ≤ _
    unfold finiteMaximum
    apply Finset.sup'_le
    intro i _
    exact ((F i).gammaNorm_normalized_le_physical (ν i) μ a A Au Av hA ha M j).trans
      (mul_le_mul_of_nonneg_left (le_finiteMaximum (fun i => (F i).gammaNorm (ν i) ((2 : ENNReal) • μ) Au Av M j) i) (pow_nonneg hA _))
  have hγ (j : ℕ) : 0 ≤ AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j :=
    finiteMaximum_nonneg _ (fun i => (F i).gammaNorm_nonneg (ν i) _ Au Av M j)
  have hsPhys (z : ℝ) (hz : 0 ≤ z) : Summable (fun j => if M ≤ j then
      z ^ j / j.factorial * AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j else 0) :=
    PoissonSeriesBounds.summable_cutoff _ (finiteMaximum_series_summable _
      (fun i => (F i).gammaNorm_nonneg (ν i) _ Au Av M) z hz
      (fun i => (F i).physical_gammaSeries_summable (ν i) μ Au Av Craw hAu hAv hCr (hb i) M z hz)) M
  have hsNorm := PoissonSeriesBounds.summable_cutoff _ (finiteMaximum_series_summable _
    (fun i => (Fn i).gammaNorm_nonneg (ν i) μ Au Av M) (K * rate) (by positivity)
    (fun i => (Fn i).gammaSeries_summable (ν i) μ Au Av C hAu hAv hC (hbFn i) M (K * rate) (by positivity))) M
  have hbase : K * (rate : ℝ) * A ≤ Cstar * Λ := by
    calc
      _ ≤ K * (T * Λ) * A := by gcongr
      _ = (K * A * T) * Λ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCKAT hΛ
  have hseries : (∑' j, if M ≤ j then (K * (rate : ℝ)) ^ j / j.factorial *
      AffinePhaseField.pairGammaMaximum ν μ Fn Au Av M j else 0) ≤
      A ^ 2 * (∑' j, if M ≤ j then (Cstar * Λ) ^ j / j.factorial *
      AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j else 0) := by
    rw [← tsum_mul_left]
    apply hsNorm.tsum_le_tsum _ ((hsPhys (Cstar * Λ) (by positivity)).mul_left (A ^ 2))
    intro j
    split_ifs
    · have hp : (K * (rate : ℝ) * A) ^ j ≤ (Cstar * Λ) ^ j :=
        pow_le_pow_left₀ (by positivity) hbase j
      calc
        _ ≤ (K * (rate : ℝ)) ^ j / j.factorial *
          (A ^ (j + 2) * AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j) :=
            mul_le_mul_of_nonneg_left (hmax j) (by positivity)
        _ = A ^ 2 * ((K * (rate : ℝ) * A) ^ j / j.factorial *
          AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j) := by rw [pow_add, mul_pow]; ring
        _ ≤ _ := by
          gcongr
          exact hγ j
    · simp
  have hrate : K * (rate : ℝ) ≤ Cstar * Λ := by
    have hKA : K * T ≤ Cstar := by
      dsimp [Cstar, physicalComparisonConstant]
      linarith
    exact (mul_le_mul_of_nonneg_left hRateScale hK).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hKA hΛ)
  have hfull := AffinePhaseField.pair_product_hellinger_uniform ν μ κ Fn hmFn Au Av C S hAu hAu1 hAv hAv1
    hC hS hbFn s hs hbs hzero c hc hlow M rate R hRate
  refine ⟨hCstar1, hfull.trans ?_⟩
  apply add_le_add
  · calc
      _ ≤ K * p * (T * Λ) ^ 2 * (A ^ 2 * ∑' j, if M ≤ j then (Cstar * Λ) ^ j / j.factorial *
          AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j else 0) := by
        gcongr
        exact tsum_nonneg fun j => by
          have hj := hγ j
          have hn : 0 ≤ AffinePhaseField.pairGammaMaximum ν μ Fn Au Av M j :=
            finiteMaximum_nonneg _ (fun i => (Fn i).gammaNorm_nonneg (ν i) μ Au Av M j)
          split_ifs <;> positivity
      _ = (K * T ^ 2 * A ^ 2) * p * Λ ^ 2 * (∑' j, if M ≤ j then (Cstar * Λ) ^ j / j.factorial *
          AffinePhaseField.physicalGammaMaximum ν μ F Au Av M j else 0) := by ring
      _ ≤ _ := by
        gcongr
        exact tsum_nonneg fun j => by
          have hj := hγ j
          have hn : 0 ≤ AffinePhaseField.pairGammaMaximum ν μ Fn Au Av M j :=
            finiteMaximum_nonneg _ (fun i => (Fn i).gammaNorm_nonneg (ν i) μ Au Av M j)
          split_ifs <;> positivity
  · calc
      _ ≤ K * p * (T * Λ) ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
          ((Cstar * Λ) ^ M / M.factorial) := by gcongr
      _ = (K * T ^ 4) * p * Λ ^ 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
          ((Cstar * Λ) ^ M / M.factorial) := by ring
      _ ≤ _ := by gcongr

end RoughRegime.PoissonMeasure
