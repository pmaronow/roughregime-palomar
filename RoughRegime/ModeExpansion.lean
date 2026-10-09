module

public import RoughRegime.CoefficientFourier


@[expose] public section
/-! Exact finite Fourier expansions and low-degree angular orthogonality. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.Lattice
open scoped BigOperators

 def modeFrequency (o : Fin 3) : ℤ := (o.val : ℤ) - 1

 def modeCoefficient (c a b : ℝ) (o : Fin 3) : ℂ :=
  if o = 0 then ((a : ℂ) + (b : ℂ) * Complex.I) / 2
  else if o = 1 then (c : ℂ) else ((a : ℂ) - (b : ℂ) * Complex.I) / 2

 def affineAngular (c a b θ : ℝ) : ℝ := c + a * Real.cos θ + b * Real.sin θ

 theorem affineAngular_expansion (c a b θ : ℝ) :
    (affineAngular c a b θ : ℂ) =
      ∑ o : Fin 3, modeCoefficient c a b o *
        Complex.exp ((((modeFrequency o : ℤ) : ℝ) * θ : ℝ) * Complex.I) := by
  rw [Fin.sum_univ_three]
  norm_num [modeCoefficient, modeFrequency]
  rw [Complex.exp_ofReal_mul_I]
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  unfold affineAngular
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

 theorem modeFrequency_abs_le_one (o : Fin 3) : |modeFrequency o| ≤ 1 := by
  fin_cases o <;> norm_num [modeFrequency]

 theorem angular_mode_integrable (n : ℤ) :
    Integrable (fun θ : ℝ => Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)) angleUniform := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun θ => by rw [Complex.norm_exp_ofReal_mul_I])

/-- The exact coefficient of any frequency in a product of j arbitrary
first-mode affine trigonometric functions. -/
 theorem affine_product_angular_coefficient (j : ℕ) (c a b : Fin j → ℝ) (n : ℤ) :
    (∫ θ, Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) ∂angleUniform) =
      ∑ o : Fin j → Fin 3, (∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
        (if n + (∑ k, modeFrequency (o k)) = 0 then 1 else 0) := by
  have heq (θ : ℝ) : Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) =
      ∑ o : Fin j → Fin 3, (∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
        Complex.exp ((((n + ∑ k, modeFrequency (o k) : ℤ) : ℝ) * θ : ℝ) * Complex.I) := by
    simp_rw [affineAngular_expansion]
    rw [Fintype.prod_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o ho
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    have hs : (∑ k : Fin j, (((modeFrequency (o k) : ℤ) : ℝ) * θ : ℝ) * Complex.I) =
        (((∑ k : Fin j, modeFrequency (o k) : ℤ) : ℝ) * θ : ℝ) * Complex.I := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [hs]
    have he : Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
        ((∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
          Complex.exp ((((∑ k, modeFrequency (o k) : ℤ) : ℝ) * θ : ℝ) * Complex.I)) =
        (∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
          (Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
            Complex.exp ((((∑ k, modeFrequency (o k) : ℤ) : ℝ) * θ : ℝ) * Complex.I)) := by ring
    rw [he, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ (fun o _ =>
    (angular_mode_integrable (n + ∑ k, modeFrequency (o k))).const_mul _)]
  apply Finset.sum_congr rfl
  intro o ho
  rw [integral_const_mul, integral_exp_integer_frequency]

 theorem affine_product_angular_coefficient_zero (j M : ℕ) (c a b : Fin j → ℝ)
    (hj : j < M) (n : ℤ) (hn : n = M ∨ n = -(M : ℤ)) :
    (∫ θ, Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) ∂angleUniform) = 0 := by
  rw [affine_product_angular_coefficient]
  apply Finset.sum_eq_zero
  intro o ho
  have hfreq := mode_sum_ne_frequency Finset.univ (fun k : Fin j => modeFrequency (o k)) M
    (fun k _ => modeFrequency_abs_le_one (o k)) (by simpa using hj)
  have hz : n + (∑ k, modeFrequency (o k)) ≠ 0 := by rcases hn with rfl | rfl <;> omega
  simp [hz]

 theorem affineAngular_abs_bound (c a b θ : ℝ) :
    |affineAngular c a b θ| ≤ |c| + |a| + |b| := by
  unfold affineAngular
  apply (abs_add_le _ _).trans
  have h1 : |c + a * Real.cos θ| ≤ |c| + |a| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have ha : |a| * |Real.cos θ| ≤ |a| := mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)
    linarith
  have h2 : |b * Real.sin θ| ≤ |b| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one θ)
  linarith

 theorem affine_product_mode_integrable (j : ℕ) (c a b : Fin j → ℝ) (n : ℤ) :
    Integrable (fun θ => Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ))) angleUniform := by
  have hc : Continuous (fun θ => Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ))) := by
    unfold affineAngular
    fun_prop
  apply Integrable.of_bound hc.aestronglyMeasurable (∏ k, (|c k| + |a k| + |b k|))
  apply Filter.Eventually.of_forall
  intro θ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
  apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
  intro k hk
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact affineAngular_abs_bound _ _ _ _

 theorem cosine_expansion (θ : ℝ) :
    (Real.cos θ : ℂ) = (1 / 2 : ℂ) *
      (Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem integral_cos_affine_product_coefficient (j M : ℕ) (c a b : Fin j → ℝ) :
    (∫ θ, (Real.cos ((M : ℝ) * θ) : ℂ) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) ∂angleUniform) =
      (1 / 2 : ℂ) *
        (∑ o : Fin j → Fin 3, (∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
          (if (M : ℤ) + (∑ k, modeFrequency (o k)) = 0 then 1 else 0) +
        ∑ o : Fin j → Fin 3, (∏ k, modeCoefficient (c k) (a k) (b k) (o k)) *
          (if -(M : ℤ) + (∑ k, modeFrequency (o k)) = 0 then 1 else 0)) := by
  have heq (θ : ℝ) : (Real.cos ((M : ℝ) * θ) : ℂ) *
      (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) =
      (1 / 2 : ℂ) *
        (Complex.exp ((((M : ℤ) : ℝ) * θ : ℝ) * Complex.I) *
          (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) +
        Complex.exp ((((-(M : ℤ)) : ℝ) * θ : ℝ) * Complex.I) *
          (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ))) := by
    rw [cosine_expansion]
    push_cast
    simp only [neg_mul]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  have hpint := affine_product_mode_integrable j c a b (M : ℤ)
  have hmint := affine_product_mode_integrable j c a b (-(M : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast] at hpint hmint ⊢
  rw [integral_add hpint hmint]
  have hpcoef := affine_product_angular_coefficient j c a b (M : ℤ)
  have hmcoef := affine_product_angular_coefficient j c a b (-(M : ℤ))
  simpa only [Int.cast_neg, Int.cast_natCast] using congrArg (fun z : ℂ => (1 / 2 : ℂ) * z)
    (congrArg₂ (· + ·) hpcoef hmcoef)

/-- Actual uniform-angle orthogonality used in the admissible-prior Poisson
comparison and lattice coefficient vanishing, for arbitrary affine coefficients. -/
 theorem integral_cos_affine_product_zero (j M : ℕ) (c a b : Fin j → ℝ) (hj : j < M) :
    (∫ θ, Real.cos ((M : ℝ) * θ) *
      (∏ k, (c k + a k * Real.cos θ + b k * Real.sin θ)) ∂angleUniform) = 0 := by
  have heq (θ : ℝ) : ((Real.cos ((M : ℝ) * θ) *
      (∏ k, affineAngular (c k) (a k) (b k) θ) : ℝ) : ℂ) =
      (1 / 2 : ℂ) *
        (Complex.exp ((((M : ℤ) : ℝ) * θ : ℝ) * Complex.I) *
          (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ)) +
        Complex.exp ((((-(M : ℤ)) : ℝ) * θ : ℝ) * Complex.I) *
          (∏ k, (affineAngular (c k) (a k) (b k) θ : ℂ))) := by
    rw [Complex.ofReal_mul, Complex.ofReal_prod, cosine_expansion]
    push_cast
    simp only [neg_mul]
    ring
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  change (∫ θ, ((Real.cos ((M : ℝ) * θ) *
    (∏ k, affineAngular (c k) (a k) (b k) θ) : ℝ) : ℂ) ∂angleUniform) = (0 : ℂ)
  simp_rw [heq]
  rw [integral_const_mul]
  have hpint := affine_product_mode_integrable j c a b (M : ℤ)
  have hmint := affine_product_mode_integrable j c a b (-(M : ℤ))
  have hpzero := affine_product_angular_coefficient_zero j M c a b hj (M : ℤ) (Or.inl rfl)
  have hmzero := affine_product_angular_coefficient_zero j M c a b hj (-(M : ℤ)) (Or.inr rfl)
  simp only [Int.cast_neg, Int.cast_natCast] at hpint hmint hpzero hmzero ⊢
  rw [integral_add hpint hmint, hpzero, hmzero]
  simp

end RoughRegime.LatticePriors
