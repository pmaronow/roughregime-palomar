module

public import RoughRegime.Separated


@[expose] public section
/-!
# Lemma 9: the separated window sum

This module proves the paper's finite-set window estimate with its stated
Gaussian constant. The integral comparison uses mathlib's proved Gaussian
integral, rather than an assumed numerical estimate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace RoughRegime.Window

/-- A Gaussian is decreasing on the nonnegative half-line. -/
theorem gaussian_antitone {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hs : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).2 hxy
  nlinarith [mul_le_mul_of_nonneg_left hs hc]

/-- The elementary Gaussian partial-sum bound used in the window estimate. -/
theorem gaussian_sum_range_le (c : ℝ) (hc : 0 < c) (N : ℕ) :
    (∑ k ∈ Finset.range N, Real.exp (-c * (k : ℝ) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / 2 := by
  cases N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ N =>
      rw [Finset.sum_range_succ']
      have hcomp :=
        (gaussian_antitone hc.le).mono (Icc_subset_Ici_self :
          Icc (0 : ℝ) (N : ℝ) ⊆ Ici 0) |>.sum_range_le_integral
          (integrable_exp_neg_mul_sq hc).integrableOn
          (fun t _ => (Real.exp_pos _).le)
      calc
        (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) +
            Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2)
          ≤ (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) + 1 := by
              simpa using add_le_add_right hcomp 1
        _ = 1 + Real.sqrt (Real.pi / c) / 2 := by
              rw [integral_gaussian_Ioi]
              ring

/-- Rewriting the Gaussian constant for a positive lattice spacing. -/
theorem gaussian_constant_spacing (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    Real.sqrt (Real.pi / (c * δ ^ 2)) = Real.sqrt (Real.pi / c) / δ := by
  have halg : Real.pi / (c * δ ^ 2) = (Real.pi / c) / δ ^ 2 := by
    field_simp
  rw [halg, Real.sqrt_div (div_nonneg Real.pi_pos.le hc.le),
    Real.sqrt_sq_eq_abs, abs_of_pos hδ]

/-- Completing the square in the window exponent. -/
theorem window_complete_square (θ τ B x : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hx : 0 < x) :
    θ * x + τ * B / x = 2 * Real.sqrt (θ * τ * B) +
      θ * (x - Real.sqrt (θ * τ * B) / θ) ^ 2 / x := by
  have hz : Real.sqrt (θ * τ * B) ^ 2 = θ * τ * B :=
    Real.sq_sqrt (by positivity)
  field_simp [ne_of_gt hθ, ne_of_gt hx]
  nlinarith [hz]

/-- The original window summand is bounded by a centered Gaussian. -/
theorem window_pointwise (θ τ B X x : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hx : 0 < x) (hxX : x ≤ X) :
    Real.exp (-θ * x - τ * B / x) ≤
      Real.exp (-2 * Real.sqrt (θ * τ * B)) *
        Real.exp (-(θ / X) * (x - Real.sqrt (θ * τ * B) / θ) ^ 2) := by
  have hsq := window_complete_square θ τ B x hθ hτ hB hx
  have hfrac := div_le_div_of_nonneg_left
    (a := θ * (x - Real.sqrt (θ * τ * B) / θ) ^ 2)
    (by positivity) hx hxX
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have halg : θ * (x - Real.sqrt (θ * τ * B) / θ) ^ 2 / X =
      θ / X * (x - Real.sqrt (θ * τ * B) / θ) ^ 2 := by ring
  rw [halg] at hfrac
  linarith

/-- Translating a separated finite set preserves its separation. -/
theorem separated_translate (S : Finset ℝ) (δ a : ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∀ u ∈ S.image (fun x => x - a), ∀ v ∈ S.image (fun x => x - a),
      u ≠ v → δ ≤ |u - v| := by
  classical
  intro u hu v hv huv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hxy : x ≠ y := by
    intro h
    exact huv (congrArg (fun z => z - a) h)
  have h := hsep x hx y hy hxy
  convert h using 1
  congr 1
  ring

/-- Reflection about a center preserves separation. -/
theorem separated_reflect (S : Finset ℝ) (δ a : ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    ∀ u ∈ S.image (fun x => a - x), ∀ v ∈ S.image (fun x => a - x),
      u ≠ v → δ ≤ |u - v| := by
  classical
  intro u hu v hv huv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have hxy : x ≠ y := by
    intro h
    exact huv (congrArg (fun z => a - z) h)
  have h := hsep x hx y hy hxy
  rw [abs_sub_comm x y] at h
  convert h using 1
  congr 1
  ring

/-- A nonnegative separated Gaussian sum is bounded by the half Gaussian integral. -/
theorem gaussian_half_sum (S : Finset ℝ) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c)
    (hnonneg : ∀ x ∈ S, 0 ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-c * x ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range S.card,
          Real.exp (-(c * δ ^ 2) * (k : ℝ) ^ 2) :=
        separated_gaussian_sum_le S hδ hc hnonneg hsep
    _ ≤ 1 + Real.sqrt (Real.pi / (c * δ ^ 2)) / 2 :=
        gaussian_sum_range_le (c * δ ^ 2) (by positivity) S.card
    _ = 1 + Real.sqrt (Real.pi / c) / δ / 2 := by
        rw [gaussian_constant_spacing c δ hc hδ]

/-- A Gaussian sum over an arbitrary separated finite set, centered at a. -/
theorem gaussian_centered_sum (S : Finset ℝ) {δ c : ℝ} (a : ℝ)
    (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-c * (x - a) ^ 2)) ≤
      2 + Real.sqrt (Real.pi / c) / δ := by
  classical
  let P := S.filter (fun x => a ≤ x)
  let N := S.filter (fun x => ¬a ≤ x)
  have hPsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hPnonneg : ∀ u ∈ P.image (fun x => x - a), 0 ≤ u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact sub_nonneg.mpr (Finset.mem_filter.mp hx).2
  have hNnonneg : ∀ u ∈ N.image (fun x => a - x), 0 ≤ u := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    exact sub_nonneg.mpr (not_le.mp (Finset.mem_filter.mp hx).2).le
  have hP := gaussian_half_sum (P.image (fun x => x - a)) hδ hc hPnonneg
    (separated_translate P δ a hPsep)
  have hN := gaussian_half_sum (N.image (fun x => a - x)) hδ hc hNnonneg
    (separated_reflect N δ a hNsep)
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hP
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hN
  have hN' : (∑ x ∈ N, Real.exp (-c * (x - a) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
    convert hN using 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ring
  have hsplit : (∑ x ∈ S, Real.exp (-c * (x - a) ^ 2)) =
      (∑ x ∈ P, Real.exp (-c * (x - a) ^ 2)) +
      (∑ x ∈ N, Real.exp (-c * (x - a) ^ 2)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun x => a ≤ x)
      (fun x => Real.exp (-c * (x - a) ^ 2))).symm
  rw [hsplit]
  linarith

/-- Lemma 9 (Window sum), with exactly the constant stated in the paper. -/
theorem window_sum (S : Finset ℝ) (θ τ B X : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hX : 0 < X)
    (hS : ∀ x ∈ S, 0 < x ∧ x ≤ X)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.log 2 ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-θ * x - τ * B / x)) ≤
      (2 + Real.sqrt (Real.pi * X / θ) / Real.log 2) *
        Real.exp (-2 * Real.sqrt (θ * τ * B)) := by
  have hδ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 0 < θ / X := div_pos hθ hX
  have hgauss := gaussian_centered_sum S (Real.sqrt (θ * τ * B) / θ) hδ hc hsep
  have halg : Real.pi / (θ / X) = Real.pi * X / θ := by
    field_simp
  calc
    _ ≤ ∑ x ∈ S, Real.exp (-2 * Real.sqrt (θ * τ * B)) *
        Real.exp (-(θ / X) * (x - Real.sqrt (θ * τ * B) / θ) ^ 2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact window_pointwise θ τ B X x hθ hτ hB (hS x hx).1 (hS x hx).2
    _ = Real.exp (-2 * Real.sqrt (θ * τ * B)) *
        ∑ x ∈ S, Real.exp (-(θ / X) * (x - Real.sqrt (θ * τ * B) / θ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-2 * Real.sqrt (θ * τ * B)) *
        (2 + Real.sqrt (Real.pi / (θ / X)) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hgauss (Real.exp_pos _).le
    _ = (2 + Real.sqrt (Real.pi * X / θ) / Real.log 2) *
        Real.exp (-2 * Real.sqrt (θ * τ * B)) := by
      rw [halg]
      ring

/-- The same result written for an arbitrary finite subset of the real line. -/
theorem window_sum_finite_set (S : Set ℝ) (hfinite : S.Finite) (θ τ B X : ℝ)
    (hθ : 0 < θ) (hτ : 0 < τ) (hB : 0 < B) (hX : 0 < X)
    (hS : S ⊆ Set.Ioc 0 X)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.log 2 ≤ |x - y|) :
    (∑ x ∈ hfinite.toFinset, Real.exp (-θ * x - τ * B / x)) ≤
      (2 + Real.sqrt (Real.pi * X / θ) / Real.log 2) *
        Real.exp (-2 * Real.sqrt (θ * τ * B)) := by
  apply window_sum hfinite.toFinset θ τ B X hθ hτ hB hX
  · intro x hx
    exact hS (hfinite.mem_toFinset.mp hx)
  · intro x hx y hy hxy
    exact hsep x (hfinite.mem_toFinset.mp hx) y (hfinite.mem_toFinset.mp hy) hxy

end RoughRegime.Window
