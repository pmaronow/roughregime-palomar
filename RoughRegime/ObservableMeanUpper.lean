module

public import RoughRegime.SampleMeanBound
public import RoughRegime.BracketCombination


@[expose] public section
/-! Actual bounded observable sample means satisfy every application upper
bracket rate, since the root-n term is dominated by the literal piecewise rate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Model

theorem observableMean_minimax {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (hn : 0 < n) (f : Ω → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M)
    (C : Set (ProbabilityMeasure Ω)) :
    minimaxRMSE n (fun P => ∫ x, f x ∂(P : Measure Ω)) C ≤ ENNReal.ofReal (M / Real.sqrt n) := by
  apply (iInf_le _ (sampleMeanEstimator n f hf)).trans
  apply iSup_le
  intro P
  apply iSup_le
  intro _
  exact sampleMeanEstimator_eLpNorm_error n hn P f hf M hM hb

theorem observableMean_upperBracket {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M)
    (C : Set (ProbabilityMeasure Ω)) (S : BracketParameters) (ν : ℝ) (hν : 2 ≤ ν) :
    UpperBracket (fun P => ∫ x, f x ∂(P : Measure Ω)) C S ν := by
  have he : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^(-(1/2 : ℝ)) ≤ upperBracketScale S ν n := by
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (RateCombination.rootN_eventually_le S.theta (Rates.tau S.lo S.hi) ν)
  obtain ⟨n0,hn0⟩ := eventually_atTop.1 he
  refine ⟨hν,M+1,by linarith,max 3 n0,le_max_left _ _,?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hr := hn0 n ((le_max_right _ _).trans hn)
  have hrate : 0 ≤ upperBracketScale S ν n := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hr
  apply (observableMean_minimax n hnpos f hf M hM hb C).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    M / Real.sqrt n = M*(n : ℝ)^(-(1/2 : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    _ ≤ M * upperBracketScale S ν n := mul_le_mul_of_nonneg_left hr hM
    _ ≤ (M+1)*upperBracketScale S ν n := mul_le_mul_of_nonneg_right (by linarith) hrate

end RoughRegime.Model
