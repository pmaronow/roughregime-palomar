module

public import Mathlib
public import RoughRegime.LiftVariance


@[expose] public section
/-! Degree tuning and assembly of the actual polynomial-lift estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.UpperTuning

/-- The factorial bound used to pass from Lemma 8 to `up:variance-levels`. -/
lemma factorial_le_degree_power (R r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R) :
    r.factorial ≤ R ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Nat.factorial_succ, Nat.succ_sub_one]
    have hpred : r - 1 + 1 = r := by omega
    calc
      (r + 1) * r.factorial ≤ R * R ^ (r - 1) :=
        Nat.mul_le_mul (by omega) (ih (by omega))
      _ = R ^ r := by simpa only [Nat.succ_eq_add_one, hpred] using (pow_succ' R (r - 1)).symm

lemma varianceTerm_le_geometric (Cv K n : ℝ) (hCv : 0 ≤ Cv) (hK : 0 ≤ K) (hn : 0 < n)
    (R r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R) :
    RoughRegime.LiftVariance.varianceTerm Cv K n r ≤
      Cv / n * (Cv * R * K / n) ^ (r - 1) := by
  have hf : (r.factorial : ℝ) ≤ (R : ℝ) ^ (r - 1) := by
    exact_mod_cast factorial_le_degree_power R r hr hrR
  calc
    _ ≤ Cv ^ r * (R : ℝ) ^ (r - 1) * (K / n) ^ (r - 1) / n := by
      unfold RoughRegime.LiftVariance.varianceTerm
      exact mul_le_mul_of_nonneg_left hf (by positivity) |> fun h =>
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) hn.le
    _ = _ := by
      have hsplit : r - 1 + 1 = r := by omega
      have hpow : Cv ^ r = Cv ^ (r - 1) * Cv := by
        simpa only [hsplit] using (pow_succ Cv (r - 1))
      rw [hpow]
      simp only [div_pow, mul_pow]
      ring

/-- The displayed level-variance bound follows algebraically from the full
Lemma 8 variance bound. -/
theorem variance_levels_of_variance_bound (v Cv K n a : ℝ)
    (hCv : 0 ≤ Cv) (hK : 0 ≤ K) (hn : 0 < n) (R : ℕ)
    (hv : v ≤ Cv * a / n +
      ∑ j ∈ Finset.range (R - 1), RoughRegime.LiftVariance.varianceTerm Cv K n (j + 2)) :
    v ≤ Cv / n * (a + ∑ j ∈ Finset.range (R - 1), (Cv * R * K / n) ^ (j + 1)) := by
  calc
    v ≤ Cv * a / n +
        ∑ j ∈ Finset.range (R - 1), Cv / n * (Cv * R * K / n) ^ (j + 1) := by
      refine hv.trans (add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_))
      have hrR : j + 2 ≤ R := by have := Finset.mem_range.mp hj; omega
      have h := varianceTerm_le_geometric Cv K n hCv hK hn R (j + 2) (by omega) hrR
      simpa only [show j + 2 - 1 = j + 1 by omega] using h
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A coarse bound valid on all levels, including the high-resolution levels. -/
theorem geometric_variance_bound (Cv n a y : ℝ) (hCv : 0 ≤ Cv) (hn : 0 < n)
    (ha : a ≤ 1) (hy : 0 ≤ y) (R : ℕ) (hR : 0 < R) :
    Cv / n * (a + ∑ j ∈ Finset.range (R - 1), y ^ (j + 1)) ≤
      Cv * R / n * max 1 y ^ (R - 1) := by
  have hmax : 1 ≤ max 1 y := le_max_left _ _
  have hpow : 1 ≤ max 1 y ^ (R - 1) := one_le_pow₀ hmax
  have hsum : (∑ j ∈ Finset.range (R - 1), y ^ (j + 1)) ≤
      (R - 1 : ℕ) * max 1 y ^ (R - 1) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (R - 1), max 1 y ^ (R - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (pow_le_pow_left₀ hy (le_max_right _ _) _).trans
          (pow_le_pow_right₀ hmax (by have := Finset.mem_range.mp hj; omega))
      _ = _ := by simp
  have hcast : ((R - 1 : ℕ) : ℝ) + 1 = R := by
    exact_mod_cast (show R - 1 + 1 = R by omega)
  have hinside : a + ∑ j ∈ Finset.range (R - 1), y ^ (j + 1) ≤
      (R : ℝ) * max 1 y ^ (R - 1) := by nlinarith [ha.trans hpow]
  calc
    _ ≤ Cv / n * ((R : ℝ) * max 1 y ^ (R - 1)) :=
      mul_le_mul_of_nonneg_left hinside (by positivity)
    _ = _ := by ring

lemma monomialLift_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n q p : ℕ}
    (σ : Fin q → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) : MemLp (RoughRegime.Upper.monomialLift σ X) 2 μ := by
  classical
  let D : ℝ := (n.descFactorial q : ℝ)⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (ω : Ω) : ‖RoughRegime.Upper.monomialLift σ X ω‖ ≤
      D * Fintype.card (Fin q ↪ Fin n) * M ^ q := by
    unfold RoughRegime.Upper.monomialLift
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hD]
    calc
      _ ≤ D * ∑ e : Fin q ↪ Fin n, ‖∏ i : Fin q, X (e i) ω (σ i)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hD
      _ ≤ D * ∑ _e : Fin q ↪ Fin n, M ^ q := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Finset.sum_le_sum
        intro e he
        simp only [Real.norm_eq_abs, Finset.abs_prod]
        have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => abs_nonneg (X (e i) ω (σ i)))
          (fun i (_ : i ∈ Finset.univ) => hb (e i) ω (σ i))
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  exact MemLp.of_bound
    (RoughRegime.Upper.monomialLift_integrable μ σ X hm M hM hb).aestronglyMeasurable _
    (Filter.Eventually.of_forall hbound)

lemma polynomialLift_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n p : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ)
    (hm : ∀ j, Measurable (X j)) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ j ω i, |X j ω i| ≤ M) : MemLp (RoughRegime.Upper.polynomialLift F X) 2 μ := by
  classical
  unfold RoughRegime.Upper.polynomialLift
  exact memLp_finsetSum _ (fun α _ => (monomialLift_memLp μ _ X hm M hM hb).const_mul _)

lemma lpNorm_centered_eq_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hm : AEStronglyMeasurable X μ) :
    lpNorm (fun ω => X ω - ∫ ω, X ω ∂μ) 2 μ = Real.sqrt (variance X μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (f := fun ω => X ω - ∫ ω, X ω ∂μ)
    (by norm_num) (by norm_num) (hm.sub aestronglyMeasurable_const)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← variance_eq_integral hm.aemeasurable, Real.sqrt_eq_rpow]

/-- The standard deviations of estimates made from the same sample still satisfy
Minkowski's inequality; independence across levels is unnecessary. -/
theorem sqrt_variance_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    Real.sqrt (variance (fun ω => ∑ i, X i ω) μ) ≤ ∑ i, Real.sqrt (variance (X i) μ) := by
  classical
  have hsum : MemLp (fun ω => ∑ i, X i ω) 2 μ := memLp_finsetSum _ (fun i _ => hX i)
  have hint (i : ι) : Integrable (X i) μ := (hX i).integrable (by norm_num)
  rw [← lpNorm_centered_eq_sqrt_variance μ _ hsum.aestronglyMeasurable]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => hint i), ← Finset.sum_sub_distrib]
  have heq : (fun ω => ∑ i, (X i ω - ∫ ω, X i ω ∂μ)) = ∑ i, (fun ω => X i ω - ∫ ω, X i ω ∂μ) := by
    funext ω
    simp
  rw [heq]
  have h := lpNorm_sum_le (fun i (_ : i ∈ Finset.univ) =>
    (hX i).sub (memLp_const (∫ ω, X i ω ∂μ))) (by norm_num : (1 : ENNReal) ≤ 2)
  change lpNorm (∑ i, (fun ω => X i ω - ∫ ω, X i ω ∂μ)) 2 μ ≤
    ∑ i, lpNorm (fun ω => X i ω - ∫ ω, X i ω ∂μ) 2 μ at h
  simp_rw [lpNorm_centered_eq_sqrt_variance μ _ (hX _).aestronglyMeasurable] at h
  exact h

/-- Root mean square error is at most bias plus standard deviation. -/
theorem root_mean_square_le_bias_add_sd {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) :
    lpNorm (fun ω => X ω - t) 2 μ ≤ |(∫ ω, X ω ∂μ) - t| + Real.sqrt (variance X μ) := by
  let c := (∫ ω, X ω ∂μ) - t
  have heq : (fun ω => X ω - t) = (fun ω => X ω - ∫ ω, X ω ∂μ) + (fun _ => c) := by
    funext ω
    dsimp [c]
    ring
  rw [heq]
  have h := lpNorm_add_le (g := fun _ => c)
    (hX.sub (memLp_const (∫ ω, X ω ∂μ))) (by norm_num : (1 : ENNReal) ≤ 2)
  refine h.trans_eq ?_
  change lpNorm (fun ω => X ω - ∫ ω, X ω ∂μ) 2 μ + lpNorm (fun _ => c) 2 μ = _
  rw [lpNorm_centered_eq_sqrt_variance μ X hX.aestronglyMeasurable]
  simp [lpNorm_const', c, Real.norm_eq_abs, add_comm]

/-- The multilevel estimator is an explicit finite sum of the distinct-sample lifts. -/
def polynomialEstimator {Ω ι : Type*} [Fintype ι] {n : ℕ} {p : ι → ℕ}
    (F : ∀ j, MvPolynomial (Fin (p j)) ℝ)
    (X : ∀ j, Fin n → Ω → Fin (p j) → ℝ) (ω : Ω) : ℝ :=
  ∑ j, RoughRegime.Upper.polynomialLift (F j) (X j) ω

lemma polynomialEstimator_mean {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {p : ι → ℕ}
    (F : ∀ j, MvPolynomial (Fin (p j)) ℝ) (hdeg : ∀ j, (F j).totalDegree ≤ n)
    (X : ∀ j, Fin n → Ω → Fin (p j) → ℝ)
    (hi : ∀ j, iIndepFun (X j) μ) (hm : ∀ j i, Measurable (X j i))
    (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) (hb : ∀ j i ω k, |X j i ω k| ≤ M j)
    (m : ∀ j, Fin (p j) → ℝ) (hmean : ∀ j i k, ∫ ω, X j i ω k ∂μ = m j k) :
    (∫ ω, polynomialEstimator F X ω ∂μ) = ∑ j, MvPolynomial.eval (m j) (F j) := by
  unfold polynomialEstimator
  rw [integral_finsetSum Finset.univ (fun j _ =>
    (polynomialLift_memLp μ (F j) (X j) (hm j) (M j) (hM j) (hb j)).integrable (by norm_num))]
  exact Finset.sum_congr rfl (fun j _ =>
    RoughRegime.Upper.polynomialLift_unbiased μ (F j) (X j) (hdeg j) (hi j) (hm j)
      (M j) (hM j) (hb j) (m j) (hmean j))

lemma approximation_sum_bias {ι : Type*} [Fintype ι] (a ψ ε : ι → ℝ) (t δ : ℝ)
    (happrox : ∀ j, |a j - ψ j| ≤ ε j) (hterminal : |(∑ j, ψ j) - t| ≤ δ) :
    |(∑ j, a j) - t| ≤ δ + ∑ j, ε j := by
  have heq : (∑ j, a j) - t = (∑ j, (a j - ψ j)) + ((∑ j, ψ j) - t) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ j, (a j - ψ j)| + |(∑ j, ψ j) - t| := abs_add_le _ _
    _ ≤ (∑ j, |a j - ψ j|) + δ :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) hterminal
    _ ≤ (∑ j, ε j) + δ := add_le_add (Finset.sum_le_sum (fun j _ => happrox j)) le_rfl
    _ = _ := add_comm _ _

/-- Exact finite-sample bias and root mean square assembly for the explicit
multilevel polynomial estimator. The approximation hypotheses concern actual
population polynomial evaluations; the stochastic term is the actual level variance. -/
theorem polynomialEstimator_risk {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} {p : ι → ℕ}
    (F : ∀ j, MvPolynomial (Fin (p j)) ℝ) (hdeg : ∀ j, (F j).totalDegree ≤ n)
    (X : ∀ j, Fin n → Ω → Fin (p j) → ℝ)
    (hi : ∀ j, iIndepFun (X j) μ) (hm : ∀ j i, Measurable (X j i))
    (M : ι → ℝ) (hM : ∀ j, 0 ≤ M j) (hb : ∀ j i ω k, |X j i ω k| ≤ M j)
    (m : ∀ j, Fin (p j) → ℝ) (hmean : ∀ j i k, ∫ ω, X j i ω k ∂μ = m j k)
    (ψ ε : ι → ℝ) (t δ : ℝ)
    (happrox : ∀ j, |MvPolynomial.eval (m j) (F j) - ψ j| ≤ ε j)
    (hterminal : |(∑ j, ψ j) - t| ≤ δ) :
    |(∫ ω, polynomialEstimator F X ω ∂μ) - t| ≤ δ + ∑ j, ε j ∧
    lpNorm (fun ω => polynomialEstimator F X ω - t) 2 μ ≤
      δ + ∑ j, ε j + ∑ j, Real.sqrt (variance (RoughRegime.Upper.polynomialLift (F j) (X j)) μ) := by
  have hL (j : ι) : MemLp (RoughRegime.Upper.polynomialLift (F j) (X j)) 2 μ :=
    polynomialLift_memLp μ (F j) (X j) (hm j) (M j) (hM j) (hb j)
  have hE : MemLp (polynomialEstimator F X) 2 μ := memLp_finsetSum _ (fun j _ => hL j)
  have hmeanE := polynomialEstimator_mean μ F hdeg X hi hm M hM hb m hmean
  have hbias : |(∫ ω, polynomialEstimator F X ω ∂μ) - t| ≤ δ + ∑ j, ε j := by
    rw [hmeanE]
    exact approximation_sum_bias _ ψ ε t δ happrox hterminal
  refine ⟨hbias, ?_⟩
  exact (root_mean_square_le_bias_add_sd μ _ hE t).trans (add_le_add hbias
    (sqrt_variance_sum_le μ (fun j => RoughRegime.Upper.polynomialLift (F j) (X j)) hL))

end RoughRegime.UpperTuning
