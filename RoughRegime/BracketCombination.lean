module

public import RoughRegime.ModelLipschitzCombination


@[expose] public section
/-! Finite upper-bracket composition with the literal selected minimum index
and maximum exponent among the components attaining that minimum. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace RoughRegime.Model

theorem finite_upperBracket_transfer {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (T : ProbabilityMeasure Ω → ℝ) (Ti : Fin m → ProbabilityMeasure Ω → ℝ)
    (C : Set (ProbabilityMeasure Ω)) (Si : Fin m → BracketParameters) (νi : Fin m → ℝ)
    (S : BracketParameters) (ν L : ℝ) (hν : 2 ≤ ν) (hL : 0 < L)
    (hlo : ∀ i, (Si i).lo = S.lo) (hhi : ∀ i, (Si i).hi = S.hi)
    (htheta : ∀ i, S.theta ≤ (Si i).theta)
    (hexponent : ∀ i, S.theta = (Si i).theta → νi i ≤ ν)
    (hupper : ∀ i, UpperBracket (Ti i) C (Si i) (νi i))
    (htransfer : ∀ n, minimaxRMSE n T C ≤ ENNReal.ofReal L * ∑ i, minimaxRMSE n (Ti i) C) :
    UpperBracket T C S ν := by
  classical
  choose c hc n0 hn0 hbound using fun i => (hupper i).2
  have hrate : ∀ i n, upperBracketScale (Si i) (νi i) n =
      RateCombination.upperRate n (Si i).theta (Rates.tau S.lo S.hi) (νi i) := by
    intro i n
    unfold upperBracketScale RateCombination.upperRate
    rw [hlo i,hhi i]
  have hnumeric : ∀ᶠ n : ℕ in atTop,
      (∑ i, c i * RateCombination.upperRate n (Si i).theta (Rates.tau S.lo S.hi) (νi i)) ≤
        (∑ i, c i) * RateCombination.upperRate n S.theta (Rates.tau S.lo S.hi) ν := by
    have h := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (RateCombination.finite_rate_sum_eventually_le (fun i => (Si i).theta) νi c
        S.theta (Rates.tau S.lo S.hi) ν 0 htheta hexponent (fun i => (hc i).le) le_rfl)
    simpa only [zero_mul,add_zero] using h
  have hlarge : ∀ᶠ n : ℕ in atTop, ∀ i, n0 i ≤ n := eventually_all.2
    (fun i => eventually_ge_atTop (n0 i))
  have hcsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ => (hc i).le)
  have he : ∀ᶠ n : ℕ in atTop,
      minimaxRMSE n T C ≤ ENNReal.ofReal ((L*((∑ i,c i)+1))*upperBracketScale S ν n) := by
    filter_upwards [hnumeric,hlarge,eventually_gt_atTop 1] with n hnumeric hlarge hn
    have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
    have hr : 0 < RateCombination.upperRate n S.theta (Rates.tau S.lo S.hi) ν :=
      RateCombination.upperRate_positive _ _ _ _ hnR
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ c i * RateCombination.upperRate n (Si i).theta (Rates.tau S.lo S.hi) (νi i) :=
      fun i _ => mul_nonneg (hc i).le (RateCombination.upperRate_positive _ _ _ _ hnR).le
    calc
      minimaxRMSE n T C ≤ ENNReal.ofReal L * ∑ i, minimaxRMSE n (Ti i) C := htransfer n
      _ ≤ ENNReal.ofReal L * ∑ i, ENNReal.ofReal
          (c i * RateCombination.upperRate n (Si i).theta (Rates.tau S.lo S.hi) (νi i)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => by
          simpa only [hrate] using hbound i n (hlarge i))) (zero_le)
      _ = ENNReal.ofReal (L * ∑ i, c i *
          RateCombination.upperRate n (Si i).theta (Rates.tau S.lo S.hi) (νi i)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg hnonneg, ← ENNReal.ofReal_mul hL.le]
      _ ≤ ENNReal.ofReal (L * ((∑ i, c i) *
          RateCombination.upperRate n S.theta (Rates.tau S.lo S.hi) ν)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnumeric hL.le)
      _ ≤ ENNReal.ofReal ((L*((∑ i,c i)+1))*upperBracketScale S ν n) := by
        apply ENNReal.ofReal_le_ofReal
        change L*((∑ i,c i)*RateCombination.upperRate n S.theta (Rates.tau S.lo S.hi) ν) ≤
          (L*((∑ i,c i)+1))*RateCombination.upperRate n S.theta (Rates.tau S.lo S.hi) ν
        nlinarith only [mul_nonneg hL.le hr.le]
  obtain ⟨n1,hn1⟩ := eventually_atTop.1 he
  exact ⟨hν,L*((∑ i,c i)+1),mul_pos hL (by linarith),max 3 n1,le_max_left _ _,
    fun n hn => hn1 n ((le_max_right _ _).trans hn)⟩

end RoughRegime.Model
