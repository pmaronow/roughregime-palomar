module

public import RoughRegime.Applications


@[expose] public section
/-! Explicit score construction from the residual covariance in Section 7.
The inverse covariance is constructed by its two-dimensional formula, rather
than taking existence of scores as a hypothesis. -/

noncomputable section
open scoped BigOperators

namespace RoughRegime.Scores

open RoughRegime.Applications

variable {ι : Type*} [Fintype ι]

theorem expectation_linear_combination (π f g : ι → ℝ) (c d : ℝ) :
    expectation π (fun i ↦ c * f i + d * g i) =
      c * expectation π f + d * expectation π g := by
  unfold expectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;> simp_rw [mul_left_comm (π _)] <;> rw [Finset.mul_sum]

theorem expectation_divide (π f : ι → ℝ) (c : ℝ) :
    expectation π (fun i ↦ f i / c) = expectation π f / c := by
  unfold expectation
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]

def scoreU (π rU rV : ι → ℝ) : ι → ℝ :=
  let uu := expectation π (fun i ↦ rU i ^ 2)
  let uv := expectation π (fun i ↦ rU i * rV i)
  let vv := expectation π (fun i ↦ rV i ^ 2)
  fun i ↦ (vv * rU i - uv * rV i) / (uu * vv - uv ^ 2)

def scoreV (π rU rV : ι → ℝ) : ι → ℝ :=
  let uu := expectation π (fun i ↦ rU i ^ 2)
  let uv := expectation π (fun i ↦ rU i * rV i)
  let vv := expectation π (fun i ↦ rV i ^ 2)
  fun i ↦ (uu * rV i - uv * rU i) / (uu * vv - uv ^ 2)

theorem score_mean_zero (π rU rV : ι → ℝ)
    (hU : expectation π rU = 0) (hV : expectation π rV = 0) :
    expectation π (scoreU π rU rV) = 0 ∧ expectation π (scoreV π rU rV) = 0 := by
  unfold scoreU scoreV
  constructor <;> rw [expectation_divide]
  · have h := expectation_linear_combination π rU rV
      (expectation π (fun i ↦ rV i ^ 2)) (-expectation π (fun i ↦ rU i * rV i))
    have h0 : expectation π (fun i ↦ (expectation π (fun j ↦ rV j ^ 2)) * rU i -
        (expectation π (fun j ↦ rU j * rV j)) * rV i) = 0 := by
      simpa only [hU, hV, mul_zero, add_zero, neg_mul, sub_eq_add_neg] using h
    rw [h0, zero_div]
  · have h := expectation_linear_combination π rV rU
      (expectation π (fun i ↦ rU i ^ 2)) (-expectation π (fun i ↦ rU i * rV i))
    have h0 : expectation π (fun i ↦ (expectation π (fun j ↦ rU j ^ 2)) * rV i -
        (expectation π (fun j ↦ rU j * rV j)) * rU i) = 0 := by
      simpa only [hU, hV, mul_zero, add_zero, neg_mul, sub_eq_add_neg] using h
    rw [h0, zero_div]

/-- The two scores have the identity cross-moment matrix. -/
theorem score_cross_moments (π rU rV : ι → ℝ)
    (hdet : expectation π (fun i ↦ rU i ^ 2) * expectation π (fun i ↦ rV i ^ 2) -
      expectation π (fun i ↦ rU i * rV i) ^ 2 ≠ 0) :
    expectation π (fun i ↦ rU i * scoreU π rU rV i) = 1 ∧
    expectation π (fun i ↦ rV i * scoreU π rU rV i) = 0 ∧
    expectation π (fun i ↦ rU i * scoreV π rU rV i) = 0 ∧
    expectation π (fun i ↦ rV i * scoreV π rU rV i) = 1 := by
  let uu := expectation π (fun i ↦ rU i ^ 2)
  let uv := expectation π (fun i ↦ rU i * rV i)
  let vv := expectation π (fun i ↦ rV i ^ 2)
  have hsym : expectation π (fun i ↦ rV i * rU i) = uv := by
    unfold uv expectation
    apply Finset.sum_congr rfl
    intro i _
    ring
  have huU : expectation π (fun i ↦ rU i * scoreU π rU rV i) =
      (vv * uu - uv * uv) / (uu * vv - uv ^ 2) := by
    have he : (fun i ↦ rU i * scoreU π rU rV i) =
        (fun i ↦ (vv * (rU i ^ 2) + (-uv) * (rU i * rV i)) / (uu * vv - uv ^ 2)) := by
      funext i
      unfold scoreU
      dsimp [uu, uv, vv]
      ring
    rw [he, expectation_divide, expectation_linear_combination]
    dsimp [uu, uv, vv]
    ring
  have hvU : expectation π (fun i ↦ rV i * scoreU π rU rV i) =
      (vv * uv - uv * vv) / (uu * vv - uv ^ 2) := by
    have he : (fun i ↦ rV i * scoreU π rU rV i) =
        (fun i ↦ (vv * (rV i * rU i) + (-uv) * (rV i ^ 2)) / (uu * vv - uv ^ 2)) := by
      funext i
      unfold scoreU
      dsimp [uu, uv, vv]
      ring
    rw [he, expectation_divide, expectation_linear_combination, hsym]
    dsimp [vv]
    ring
  have huV : expectation π (fun i ↦ rU i * scoreV π rU rV i) =
      (uu * uv - uv * uu) / (uu * vv - uv ^ 2) := by
    have he : (fun i ↦ rU i * scoreV π rU rV i) =
        (fun i ↦ (uu * (rU i * rV i) + (-uv) * (rU i ^ 2)) / (uu * vv - uv ^ 2)) := by
      funext i
      unfold scoreV
      dsimp [uu, uv, vv]
      ring
    rw [he, expectation_divide, expectation_linear_combination]
    dsimp [uu, uv]
    ring
  have hvV : expectation π (fun i ↦ rV i * scoreV π rU rV i) =
      (uu * vv - uv * uv) / (uu * vv - uv ^ 2) := by
    have he : (fun i ↦ rV i * scoreV π rU rV i) =
        (fun i ↦ (uu * (rV i ^ 2) + (-uv) * (rV i * rU i)) / (uu * vv - uv ^ 2)) := by
      funext i
      unfold scoreV
      dsimp [uu, uv, vv]
      ring
    rw [he, expectation_divide, expectation_linear_combination, hsym]
    dsimp [vv]
    ring
  change uu * vv - uv ^ 2 ≠ 0 at hdet
  rw [huU, hvU, huV, hvV]
  constructor
  · apply (div_eq_one_iff_eq hdet).mpr
    ring
  constructor
  · simp [mul_comm]
  constructor
  · simp [mul_comm]
  · apply (div_eq_one_iff_eq hdet).mpr
    ring

theorem diagonal_score (π r : ι → ℝ) (hr : expectation π r = 0)
    (hvar : expectation π (fun i ↦ r i ^ 2) ≠ 0) :
    let s := fun i ↦ r i / expectation π (fun i ↦ r i ^ 2)
    expectation π s = 0 ∧ expectation π (fun i ↦ r i * s i) = 1 := by
  dsimp
  constructor
  · rw [expectation_divide, hr]
    simp
  · have he : (fun i ↦ r i * (r i / expectation π (fun j ↦ r j ^ 2))) =
        (fun i ↦ r i ^ 2 / expectation π (fun j ↦ r j ^ 2)) := by
      funext i
      ring
    rw [he, expectation_divide, div_self hvar]

end RoughRegime.Scores
