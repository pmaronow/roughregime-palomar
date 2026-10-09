module

public import RoughRegime.AnalyticCoefficients
public import RoughRegime.SeriesBounds


@[expose] public section
/-! Genuine analytic representation of ordinary formal series from generating identities. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RoughRegime.PowerSeriesAnalytic
open RoughRegime.AnalyticCoefficients RoughRegime.SeriesBounds

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- Weight ordinary formal coefficients by powers of the complex generating variable. -/
def weightedCoefficients (f : PowerSeries R) (z : ℂ) (k : ℕ) : R :=
  z ^ k • PowerSeries.coeff k f

lemma weightedCoefficients_mul (f g : PowerSeries R) (z : ℂ) :
    weightedCoefficients (f * g) z = convolution (weightedCoefficients f z) (weightedCoefficients g z) := by
  funext k
  rw [weightedCoefficients, PowerSeries.coeff_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [weightedCoefficients]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, he]

lemma weightedCoefficients_monomial (a : R) (d : ℕ) (z : ℂ) (k : ℕ) :
    weightedCoefficients (PowerSeries.monomial d a) z k = if k = d then z ^ d • a else 0 := by
  simp only [weightedCoefficients, PowerSeries.coeff_monomial]
  split_ifs with hk
  · subst k
    rfl
  · exact smul_zero _

lemma weighted_monomial_summable_norm (a : R) (d : ℕ) (z : ℂ) :
    Summable (fun k => ‖weightedCoefficients (PowerSeries.monomial d a) z k‖) := by
  apply summable_of_ne_finset_zero (s := {d})
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [weightedCoefficients_monomial, hk]

lemma weighted_monomial_tsum (a : R) (d : ℕ) (z : ℂ) :
    (∑' k, weightedCoefficients (PowerSeries.monomial d a) z k) = z ^ d • a := by
  simp only [weightedCoefficients_monomial]
  exact tsum_ite_eq d (fun _ => z ^ d • a)

lemma weightedCoefficients_add (f g : PowerSeries R) (z : ℂ) :
    weightedCoefficients (f + g) z = weightedCoefficients f z + weightedCoefficients g z := by
  funext k
  simp only [weightedCoefficients, map_add, smul_add, Pi.add_apply]

lemma weightedCoefficients_sub (f g : PowerSeries R) (z : ℂ) :
    weightedCoefficients (f - g) z = weightedCoefficients f z - weightedCoefficients g z := by
  funext k
  simp only [weightedCoefficients, map_sub, smul_sub, Pi.sub_apply]

omit [NormedAlgebra ℂ R] in
lemma weighted_one_eq_monomial :
    (1 : PowerSeries R) = PowerSeries.monomial 0 (1 : R) := by
  rw [PowerSeries.monomial_zero_eq_C, map_one]

/-- Evaluate the finite denominator polynomial in the genuine common generating variable. -/
def quadraticDenominator (a b : R) (z : ℂ) : R := 1 + z • a + z ^ 2 • b

def quadraticDenominatorSeries (a b : R) : PowerSeries R :=
  1 + PowerSeries.C a * PowerSeries.X ^ 1 + PowerSeries.C b * PowerSeries.X ^ 2

def quadraticNumeratorSeries (b : R) : PowerSeries R := 1 - PowerSeries.C b * PowerSeries.X ^ 2

lemma quadraticDenominator_coeff_zero (a b : R) (z : ℂ) (k : ℕ) (hk : 3 ≤ k) :
    weightedCoefficients (quadraticDenominatorSeries a b) z k = 0 := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  have h2 : k ≠ 2 := by omega
  simp [weightedCoefficients, quadraticDenominatorSeries, map_add,
    PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, h0, h1, h2]

lemma quadraticDenominator_summable_norm (a b : R) (z : ℂ) :
    Summable (fun k => ‖weightedCoefficients (quadraticDenominatorSeries a b) z k‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro k hk
  rw [quadraticDenominator_coeff_zero a b z k (by simpa only [Finset.mem_range, not_lt] using hk), norm_zero]

lemma quadraticDenominator_tsum (a b : R) (z : ℂ) :
    (∑' k, weightedCoefficients (quadraticDenominatorSeries a b) z k) = quadraticDenominator a b z := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk =>
    quadraticDenominator_coeff_zero a b z k (by simpa only [Finset.mem_range, not_lt] using hk))]
  norm_num [weightedCoefficients, quadraticDenominatorSeries, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, Finset.sum_range_succ, quadraticDenominator]

lemma quadraticNumerator_tsum (b : R) (z : ℂ) :
    (∑' k, weightedCoefficients (quadraticNumeratorSeries b) z k) = 1 - z ^ 2 • b := by
  have hz (k : ℕ) (hk : k ∉ Finset.range 3) :
      weightedCoefficients (quadraticNumeratorSeries b) z k = 0 := by
    have h3 : 3 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have h0 : k ≠ 0 := by omega
    have h2 : k ≠ 2 := by omega
    simp [weightedCoefficients, quadraticNumeratorSeries, map_sub,
      PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, h0, h2]
  rw [tsum_eq_sum hz]
  norm_num [weightedCoefficients, quadraticNumeratorSeries, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, Finset.sum_range_succ, sub_eq_add_neg]

/-- A formal generating identity and positive radius produce the actual analytic rational kernel. -/
theorem hasFPowerSeriesAt_of_quadratic_generating_identity [CompleteSpace R]
    (f : PowerSeries R) (a b : R)
    (hr : 0 < (coefficientSeries (fun k => PowerSeries.coeff k f)).radius)
    (hidentity : quadraticDenominatorSeries a b * f = quadraticNumeratorSeries b) :
    HasFPowerSeriesAt
      (fun z : ℂ => Ring.inverse (quadraticDenominator a b z) * (1 - z ^ 2 • b))
      (coefficientSeries (fun k => PowerSeries.coeff k f)) 0 := by
  let p := coefficientSeries (fun k => PowerSeries.coeff k f)
  have hp : HasFPowerSeriesAt p.sum p 0 := (p.hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  apply hp.congr
  have hQ : Continuous (quadraticDenominator a b) := by
    unfold quadraticDenominator
    fun_prop
  have hQ0 : quadraticDenominator a b 0 = 1 := by simp [quadraticDenominator]
  have hu : ∀ᶠ z in 𝓝 (0 : ℂ), IsUnit (quadraticDenominator a b z) := by
    exact (hQ.tendsto' 0 1 hQ0).eventually (Units.isOpen.mem_nhds isUnit_one)
  filter_upwards [hu, Metric.eball_mem_nhds (0 : ℂ) hr] with z hz hy
  have hs : Summable (fun k => ‖weightedCoefficients f z k‖) := by
    simpa only [p, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      coefficientSeries_coeff, weightedCoefficients] using p.summable_norm_apply hy
  have hprod : quadraticDenominator a b z * p.sum z = 1 - z ^ 2 • b := by
    rw [← quadraticNumerator_tsum b z, ← hidentity, weightedCoefficients_mul,
      convolution_tsum _ _ (quadraticDenominator_summable_norm a b z) hs,
      quadraticDenominator_tsum]
    congr 1
    apply tsum_congr
    intro k
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, p,
      coefficientSeries_coeff, weightedCoefficients]
  calc
    p.sum z = (Ring.inverse (quadraticDenominator a b z) * quadraticDenominator a b z) * p.sum z := by
      rw [Ring.inverse_mul_cancel _ hz, one_mul]
    _ = _ := by rw [mul_assoc, hprod]

end RoughRegime.PowerSeriesAnalytic
