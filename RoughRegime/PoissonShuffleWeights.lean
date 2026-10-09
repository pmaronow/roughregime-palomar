module

public import RoughRegime.PoissonProcess


@[expose] public section
/-! The exact Poisson/multinomial cancellation behind uniform shuffling of
independent count-and-mark processes. -/
noncomputable section
open scoped BigOperators NNReal ENNReal
namespace RoughRegime.PoissonMeasure

/-- The count weight after averaging over all orderings is the global Poisson
weight times the iid mixture-label weight. Individual rates may vanish. -/
theorem poisson_shuffle_weight_real {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (count : ι → ℕ) (h : 0 < ∑ i, rate i) :
    (∏ i, Lower.poissonMass (rate i) (count i)) *
        (∏ i, ((count i).factorial : ℝ)) / ((∑ i, count i).factorial : ℝ) =
      Lower.poissonMass (∑ i, rate i) (∑ i, count i) *
        ∏ i, (rate i / (∑ j, rate j)) ^ count i := by
  classical
  have hf : (∏ i, ((count i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : (∑ i, rate i) ≠ 0 := h.ne'
  have hprod : (∏ i, Real.exp (-rate i)) = Real.exp (-(∑ i, rate i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp only [Lower.poissonMass, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    div_pow, Finset.prod_pow_eq_pow_sum, hprod]
  field_simp

/-- Extended-real form used directly for probability measures and shuffle
kernel weights. -/
theorem poisson_shuffle_weight {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) (count : ι → ℕ) (h : 0 < ∑ i, rate i) :
    (∏ i, ENNReal.ofReal (Lower.poissonMass (rate i) (count i))) *
        (∏ i, ((count i).factorial : ℝ≥0∞)) / ((∑ i, count i).factorial : ℝ≥0∞) =
      ENNReal.ofReal (Lower.poissonMass (∑ i, rate i) (∑ i, count i)) *
        ∏ i, (((rate i / (∑ j, rate j)) : ℝ≥0) : ℝ≥0∞) ^ count i := by
  classical
  have hl : ((∏ i, ENNReal.ofReal (Lower.poissonMass (rate i) (count i))) *
      (∏ i, ((count i).factorial : ℝ≥0∞)) /
      ((∑ i, count i).factorial : ℝ≥0∞)) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top)
        (ENNReal.prod_ne_top fun i _ => ENNReal.natCast_ne_top _)
    · exact_mod_cast Nat.factorial_ne_zero (∑ i, count i)
  have hr : ENNReal.ofReal (Lower.poissonMass (∑ i, rate i) (∑ i, count i)) *
      (∏ i, (((rate i / (∑ j, rate j)) : ℝ≥0) : ℝ≥0∞) ^ count i) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top fun i _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)
  apply (ENNReal.toReal_eq_toReal_iff' hl hr).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_prod,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.coe_toReal]
  have hm (i : ι) : (ENNReal.ofReal (Lower.poissonMass (rate i) (count i))).toReal =
      Lower.poissonMass (rate i) (count i) :=
    ENNReal.toReal_ofReal (Lower.poissonMass_nonneg _ (rate i).2 _)
  have ht : (ENNReal.ofReal (Lower.poissonMass (∑ i, rate i) (∑ i, count i))).toReal =
      Lower.poissonMass (∑ i, rate i) (∑ i, count i) :=
    ENNReal.toReal_ofReal (Lower.poissonMass_nonneg _ (Finset.sum_nonneg fun i _ => (rate i).2) _)
  simp only [hm, ht]
  simp only [NNReal.coe_div, NNReal.coe_sum]
  exact poisson_shuffle_weight_real (fun i => (rate i : ℝ)) count (by exact_mod_cast h)

end RoughRegime.PoissonMeasure
