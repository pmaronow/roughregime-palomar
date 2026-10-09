module

public import RoughRegime.DyadicUniform


@[expose] public section
/-! Actual tensor law of all dyadic digits of a uniform cube and finite
expectation formulas. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace RoughRegime.DyadicDigits

def unitUniform : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

def cubeUniform (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => unitUniform)

instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform]

instance cubeUniform_probability (d : ℕ) : IsProbabilityMeasure (cubeUniform d) := by
  unfold cubeUniform
  infer_instance

/-- All bits of all coordinates. -/
def cubeBits (J d : ℕ) (x : Fin d → ℝ) : Fin d → Fin J → Bool :=
  fun q => pointBits J (x q)

theorem cubeBits_measurable (J d : ℕ) : Measurable (cubeBits J d) := by
  unfold cubeBits
  apply Measurable.of_eval
  intro q
  exact (pointBits_measurable J).comp (measurable_pi_apply q)

theorem cubeBits_fiber (J d : ℕ) (b : Fin d → Fin J → Bool) :
    {x | cubeBits J d x = b} =
      Set.pi Set.univ (fun q => {y : ℝ | pointBits J y = b q}) := by
  ext x
  simp only [mem_ofPred_eq, mem_pi, mem_univ, forall_true_left]
  exact funext_iff

/-- Exact joint cube digit probabilities: every dJ-bit string has mass2^(-dJ). -/
theorem cubeBits_probability (J d : ℕ) (b : Fin d → Fin J → Bool) :
    cubeUniform d {x | cubeBits J d x = b} =
      ENNReal.ofReal (((2 : ℝ) ^ (-(J : ℤ))) ^ d) := by
  rw [cubeBits_fiber, cubeUniform, Measure.pi_pi]
  simp only [unitUniform, pointBits_probability, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

/-- Finite expectation is the actual average over all coordinate digit strings. -/
theorem integral_cubeBits {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (J d : ℕ) (f : (Fin d → Fin J → Bool) → E) :
    (∫ x, f (cubeBits J d x) ∂cubeUniform d) =
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) • ∑ b, f b := by
  rw [← integral_map_of_stronglyMeasurable (cubeBits_measurable J d)
    (StronglyMeasurable.of_discrete), integral_fintype (Integrable.of_finite)]
  have hm (b : Fin d → Fin J → Bool) :
      (Measure.map (cubeBits J d) (cubeUniform d)).real {b} =
        ((2 : ℝ) ^ (-(J : ℤ))) ^ d := by
    rw [measureReal_def, Measure.map_apply (cubeBits_measurable J d) (measurableSet_singleton b)]
    change (cubeUniform d {x | cubeBits J d x = b}).toReal = _
    rw [cubeBits_probability, ENNReal.toReal_ofReal (by positivity)]
  simp_rw [hm]
  rw [Finset.smul_sum]

/-- Factorization of actual digit-dependent products. -/
theorem integral_cube_digit_product (J d : ℕ)
    (f : Fin d → Fin J → Bool → ℂ) :
    (∫ x, (∏ q, ∏ i, f q i (cubeBits J d x q i)) ∂cubeUniform d) =
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) •
        (∏ q, ∏ i, (f q i true + f q i false)) := by
  rw [integral_cubeBits J d (fun b => ∏ q, ∏ i, f q i (b q i))]
  congr 1
  rw [← Fintype.prod_sum (fun q (b : Fin J → Bool) => ∏ i, f q i (b i))]
  apply Finset.prod_congr rfl
  intro q _
  rw [← Fintype.prod_sum (fun i (b : Bool) => f q i b)]
  simp only [Fintype.sum_bool]

/-- Real counterpart used for the source's mismatch penalty products. -/
theorem integral_cube_digit_product_real (J d : ℕ)
    (f : Fin d → Fin J → Bool → ℝ) :
    (∫ x, (∏ q, ∏ i, f q i (cubeBits J d x q i)) ∂cubeUniform d) =
      (((2 : ℝ) ^ (-(J : ℤ))) ^ d) *
        (∏ q, ∏ i, (f q i true + f q i false)) := by
  rw [integral_cubeBits J d (fun b => ∏ q, ∏ i, f q i (b q i))]
  rw [smul_eq_mul]
  congr 1
  rw [← Fintype.prod_sum (fun q (b : Fin J → Bool) => ∏ i, f q i (b i))]
  apply Finset.prod_congr rfl
  intro q _
  rw [← Fintype.prod_sum (fun i (b : Bool) => f q i b)]
  simp only [Fintype.sum_bool]

end RoughRegime.DyadicDigits
