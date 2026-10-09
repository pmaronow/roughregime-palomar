module

public import RoughRegime.GateLaw
public import RoughRegime.DyadicTensorCollars


@[expose] public section
/-! Gate expectations under the actual independent lattice PMF prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RoughRegime.LatticeFourier

/-- Actual product-law expectation factorization. -/
theorem integral_product_pi {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℤ) [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℤ → ℝ) :
    (∫ x, (∏ i, f i (x i)) ∂Measure.pi μ) = ∏ i, ∫ z, f i z ∂μ i := by
  have hm (i : ι) : Measurable (f i) := measurable_of_countable _
  have hi := iIndepFun_pi (μ := μ) (X := f) (fun i => (hm i).aemeasurable)
  rw [hi.integral_fun_prod_eq_prod_integral
    (fun i => ((hm i).comp (measurable_pi_apply i)).aestronglyMeasurable)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_apply i) (hm i).stronglyMeasurable,
    (measurePreserving_eval μ i).map_eq]

/-- The PMF expectation is the convergent real weighted sample sum. -/
theorem latticeLaw_gate_expectation (Q M : ℕ) (η lam : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η)
    (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    (∫ z, RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)
      ∂(latticeLaw Q M η hQ hM hη hband).toMeasure) =
      ∑' z : ℤ, latticeWeight Q M η z *
        RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z) := by
  have hm : Measurable (fun z : ℤ =>
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z)) := measurable_of_countable _
  have hi : Integrable (fun z : ℤ =>
      RoughRegime.Lattice.gate Q (lam * η) (latticeStep M * z))
      (latticeLaw Q M η hQ hM hη hband).toMeasure := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (RoughRegime.Lattice.gate_nonneg _ _ _)]
    exact RoughRegime.Lattice.gate_le_one _ _ _
  rw [PMF.integral_eq_tsum _ _ hi]
  apply tsum_congr
  intro z
  rw [latticeLaw_apply, ENNReal.toReal_ofReal
    (latticeWeight_nonneg Q M η hQ hM hη z), smul_eq_mul]

variable {ι : Type*} [Fintype ι]

/-- Independent coefficients with exactly the laws constructed in Lemma13. -/
def gatePrior (Q M : ℕ) (η : ι → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M)
    (hη : ∀ i, 0 < η i) (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) : Measure (ι → ℤ) :=
  Measure.pi (fun i => (latticeLaw Q M (η i) hQ hM (hη i) (hband i)).toMeasure)

instance gatePrior_probability (Q M : ℕ) (η : ι → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M)
    (hη : ∀ i, 0 < η i) (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    IsProbabilityMeasure (gatePrior Q M η hQ hM hη hband) := by
  unfold gatePrior
  infer_instance

def jointGate (Q M : ℕ) (η lam : ι → ℝ) (x : ι → ℤ) : ℝ :=
  ∏ i, RoughRegime.Lattice.gate Q (lam i * η i) (latticeStep M * x i)

theorem jointGate_bounds (Q M : ℕ) (η lam : ι → ℝ) (x : ι → ℤ) :
    0 ≤ jointGate Q M η lam x ∧ jointGate Q M η lam x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => RoughRegime.Lattice.gate_nonneg _ _ _)
  · exact Finset.prod_le_one₀ (fun i _ => RoughRegime.Lattice.gate_nonneg _ _ _)
      (fun i _ => RoughRegime.Lattice.gate_le_one _ _ _)

theorem jointGate_measurable (Q M : ℕ) (η lam : ι → ℝ) : Measurable (jointGate Q M η lam) := by
  unfold jointGate
  apply Finset.measurable_prod
  intro i _
  exact (measurable_of_countable (fun z : ℤ =>
    RoughRegime.Lattice.gate Q (lam i * η i) (latticeStep M * z))).comp (measurable_pi_apply i)

/-- The first moment of the actual gate product has the claimed deficit sum. -/
theorem jointGate_expectation_lower (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i) (hlam : ∀ i, 1 ≤ lam i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    1 - (∑ i, (Q : ℝ) * sincSecondMoment Q / (3 * lam i ^ 2)) ≤
      ∫ x, jointGate Q M η lam x ∂gatePrior Q M η (by omega) hM hη hband := by
  classical
  let μ (i : ι) : Measure ℤ := (latticeLaw Q M (η i) (by omega) hM (hη i) (hband i)).toMeasure
  let f (i : ι) (z : ℤ) : ℝ := RoughRegime.Lattice.gate Q (lam i * η i) (latticeStep M * z)
  have hm (i : ι) : Measurable (f i) := measurable_of_countable _
  have hi (i : ι) : Integrable (f i) (μ i) := by
    apply Integrable.of_bound (hm i).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (RoughRegime.Lattice.gate_nonneg _ _ _)]
    exact RoughRegime.Lattice.gate_le_one _ _ _
  have h0 (i : ι) : 0 ≤ ∫ z, f i z ∂μ i :=
    integral_nonneg (fun z => RoughRegime.Lattice.gate_nonneg _ _ _)
  have h1 (i : ι) : (∫ z, f i z ∂μ i) ≤ 1 := by
    have hh := integral_mono_ae (hi i) (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall fun z => RoughRegime.Lattice.gate_le_one Q (lam i * η i) (latticeStep M * z))
    simpa using hh
  have hd (i : ι) : 1 - (∫ z, f i z ∂μ i) ≤
      (Q : ℝ) * sincSecondMoment Q / (3 * lam i ^ 2) := by
    change 1 - (∫ z, RoughRegime.Lattice.gate Q (lam i * η i) (latticeStep M * z)
      ∂(latticeLaw Q M (η i) (by omega) hM (hη i) (hband i)).toMeasure) ≤ _
    rw [latticeLaw_gate_expectation]
    exact sampled_gate_deficit Q M (η i) (lam i) hQ hM (hη i) (hlam i) (hband i)
  change 1 - (∑ i, _) ≤ ∫ x, (∏ i, f i (x i)) ∂Measure.pi μ
  rw [integral_product_pi]
  have hp := RoughRegime.Lattice.one_sub_product_le_sum Finset.univ
    (fun i => ∫ z, f i z ∂μ i) (fun i _ => h0 i) (fun i _ => h1 i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hd i)
  linarith

/-- The actual second moment satisfies Jensen's square inequality. -/
theorem jointGate_second_moment_lower (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ)) :
    (∫ x, jointGate Q M η lam x ∂gatePrior Q M η hQ hM hη hband) ^ 2 ≤
      ∫ x, jointGate Q M η lam x ^ 2 ∂gatePrior Q M η hQ hM hη hband := by
  have hmem : MemLp (jointGate Q M η lam) 2 (gatePrior Q M η hQ hM hη hband) := by
    apply MemLp.of_bound (jointGate_measurable Q M η lam).aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (jointGate_bounds Q M η lam x).1]
    exact (jointGate_bounds Q M η lam x).2
  have hv := variance_nonneg (jointGate Q M η lam) (gatePrior Q M η hQ hM hη hband)
  rw [variance_eq_sub hmem] at hv
  exact sub_nonneg.mp hv

/-- The actual level-indexed prior has E S≥3/4 with the source lambdaStar budget. -/
theorem levelGate_expectation_three_quarters (Q M J d : ℕ) (η : Fin J × Fin d → ℝ)
    (hQ : 2 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (lamstar : ℝ) (hlam : 1 ≤ lamstar)
    (hbudget : 8 * Q * d * sincSecondMoment Q / 3 ≤ lamstar ^ 2) :
    (3 / 4 : ℝ) ≤ ∫ x, jointGate Q M η
      (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) x
      ∂gatePrior Q M η (by omega) hM hη hband := by
  have hlpos : 0 < lamstar := by linarith
  let C : ℝ := (Q : ℝ) * sincSecondMoment Q / (3 * lamstar ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sincSecondMoment_nonneg Q (by omega))) (by positivity)
  have hlam_i (i : Fin J × Fin d) : 1 ≤ lamstar * ((i.1 : ℝ) + 1) := by
    have hi : 0 ≤ (i.1 : ℝ) := by positivity
    nlinarith
  have he (i : Fin J × Fin d) :
      (Q : ℝ) * sincSecondMoment Q / (3 * (lamstar * ((i.1 : ℝ) + 1)) ^ 2) =
        C / ((i.1 : ℝ) + 1) ^ 2 := by
    dsimp [C]
    field_simp
  have hs := RoughRegime.DyadicDigits.levelWidth_sum_le J d C hC
  have hb : 2 * (d : ℝ) * C ≤ 1 / 4 := by
    dsimp [C]
    have hd : 0 < 3 * lamstar ^ 2 := by positivity
    have hn : 8 * (Q : ℝ) * d * sincSecondMoment Q ≤ 3 * lamstar ^ 2 := by
      nlinarith [hbudget]
    have hh : (8 * (Q : ℝ) * d * sincSecondMoment Q) / (3 * lamstar ^ 2) ≤ 1 :=
      (div_le_one hd).mpr hn
    calc
      2 * (d : ℝ) * ((Q : ℝ) * sincSecondMoment Q / (3 * lamstar ^ 2)) =
          ((8 * (Q : ℝ) * d * sincSecondMoment Q) / (3 * lamstar ^ 2)) / 4 := by ring
      _ ≤ 1 / 4 := div_le_div_of_nonneg_right hh (by norm_num)
  have hg := jointGate_expectation_lower Q M η
    (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) hQ hM hη hlam_i hband
  simp_rw [he] at hg
  linarith

/-- The source's E S²≥9/16 follows for the same actual independent prior. -/
theorem levelGate_second_moment_nine_sixteenths (Q M J d : ℕ)
    (η : Fin J × Fin d → ℝ) (hQ : 2 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (lamstar : ℝ) (hlam : 1 ≤ lamstar)
    (hbudget : 8 * Q * d * sincSecondMoment Q / 3 ≤ lamstar ^ 2) :
    (9 / 16 : ℝ) ≤ ∫ x, jointGate Q M η
      (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) x ^ 2
      ∂gatePrior Q M η (by omega) hM hη hband := by
  have hmean := levelGate_expectation_three_quarters Q M J d η hQ hM hη hband lamstar hlam hbudget
  have hsecond := jointGate_second_moment_lower Q M η
    (fun i : Fin J × Fin d => lamstar * ((i.1 : ℝ) + 1)) (by omega) hM hη hband
  nlinarith

end RoughRegime.LatticeFourier
