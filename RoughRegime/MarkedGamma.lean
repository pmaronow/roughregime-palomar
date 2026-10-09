module

public import RoughRegime.GammaBounds


@[expose] public section
/-! Full marked lattice coefficients, with both spatial bump arguments and
all two-block labels, using the paper's Lebesgue × counting measure. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits
open scoped BigOperators

 variable {J d j : ℕ}

 def markedGamma (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : Fin j → (Fin d → ℝ) → ℝ)
    (z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) : ℝ :=
  Au * Av * bump z.1.1 * bump z.1.2 *
    spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w z.2

 def markedSpatialMeasure (d j : ℕ) :
    Measure (((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) :=
  ((cubeUniform d).prod (cubeUniform d)).prod
    (Measure.pi (fun _ : Fin j => cubeUniform d))

 theorem markedGamma_square_integral (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (c w : Fin j → (Fin d → ℝ) → ℝ) :
    (∫ z, markedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z ^ 2
      ∂markedSpatialMeasure d j) =
      Au ^ 2 * Av ^ 2 * (∫ x, bump x ^ 2 ∂cubeUniform d) ^ 2 *
        (∫ x, spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w x ^ 2
          ∂Measure.pi (fun _ : Fin j => cubeUniform d)) := by
  have heq : (fun z => markedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z ^ 2) =
      fun z => (Au ^ 2 * Av ^ 2 * (bump z.1.1 ^ 2 * bump z.1.2 ^ 2)) *
        spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w z.2 ^ 2 := by
    funext z
    unfold markedGamma
    ring
  rw [heq]
  unfold markedSpatialMeasure
  rw [integral_prod_mul (fun z : (Fin d → ℝ) × (Fin d → ℝ) => Au ^ 2 * Av ^ 2 * (bump z.1 ^ 2 * bump z.2 ^ 2))
    (fun x => spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w x ^ 2),
    integral_const_mul, integral_prod_mul (fun x => bump x ^ 2) (fun x => bump x ^ 2)]
  ring

 theorem bump_square_integral_range (bump : (Fin d → ℝ) → ℝ)
    (hb : ∀ x, |bump x| ≤ 1) :
    0 ≤ (∫ x, bump x ^ 2 ∂cubeUniform d) ∧ (∫ x, bump x ^ 2 ∂cubeUniform d) ≤ 1 := by
  constructor
  · exact integral_nonneg (fun x => sq_nonneg _)
  · have hh : ‖∫ x, bump x ^ 2 ∂cubeUniform d‖ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const (μ := cubeUniform d)
        (f := fun x => bump x ^ 2) (Filter.Eventually.of_forall (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have h := hb x
          have hp := mul_le_mul h h (abs_nonneg _) zero_le_one
          nlinarith [sq_abs (bump x)]))
    rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))] at hh

 theorem markedGamma_L2Squared (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L)
    (hb : ∀ k x φ θ, |phasedAngular (c k x) (w k x) φ θ| ≤ L)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    (∫ z, markedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z ^ 2
      ∂markedSpatialMeasure d j) ≤
      if M ≤ j then 4 * Au ^ 2 * Av ^ 2 * (3 * Real.exp 1 * L ^ 2) ^ j * Real.exp (CE * M) *
        gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  rw [markedGamma_square_integral]
  have hr := bump_square_integral_range bump hbump
  have hsq : (∫ x, bump x ^ 2 ∂cubeUniform d) ^ 2 ≤ 1 := by nlinarith
  have hG := spatialLatticeGamma_L2Squared U Q M γ η lam hd hQ hM hM1 hη hlam hband hγ hγ1
    c w hc hw L CE hL hCE hcL hwL hb hbudget
  have hnonneg : 0 ≤ ∫ x, spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w x ^ 2
      ∂Measure.pi (fun _ : Fin j => cubeUniform d) := integral_nonneg (fun x => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg Au) (sq_nonneg Av))) hnonneg
  simp only [mul_one] at h1
  have h2 := mul_le_mul_of_nonneg_left hG (mul_nonneg (sq_nonneg Au) (sq_nonneg Av))
  have hh := h1.trans h2
  by_cases hj : M ≤ j
  · simp only [ite_eq_left hj] at hh ⊢
    convert hh using 1 <;> ring
  · simpa only [ite_eq_right hj, mul_zero] using hh

/-- The square L² norm on both spatial bump marks and j likelihood marks.
The finite sum is the actual two-block counting measure in every coordinate. -/
 def labeledGammaL2Squared (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ labels : Fin (j + 2) → Bool,
    ∫ z, markedGamma U Q M γ η lam hQ hM hη hband Au Av bump (c labels) (w labels) z ^ 2
      ∂markedSpatialMeasure d j

 def gammaConstant (L : ℝ) : ℝ := 16 * (1 + 6 * Real.exp 1 * L ^ 2)

 theorem gammaConstant_ge_one (L : ℝ) : 1 ≤ gammaConstant L := by
  unfold gammaConstant
  nlinarith [Real.exp_pos (1 : ℝ), sq_nonneg L]

 theorem gammaConstant_bound (L : ℝ) (j : ℕ) :
    16 * (6 * Real.exp 1 * L ^ 2) ^ j ≤ gammaConstant L ^ (j + 1) := by
  let A := 6 * Real.exp 1 * L ^ 2
  have hA : 0 ≤ A := by positivity
  have hC : 1 + A ≤ gammaConstant L := by
    unfold gammaConstant
    dsimp only [A]
    nlinarith [Real.exp_pos (1 : ℝ), sq_nonneg L]
  have hbase : A ≤ gammaConstant L := (le_add_of_nonneg_left zero_le_one).trans hC
  have hp := pow_le_pow_left₀ hA hbase j
  have h16 : 16 ≤ gammaConstant L := by
    unfold gammaConstant
    nlinarith [Real.exp_pos (1 : ℝ), sq_nonneg L]
  have hh := mul_le_mul h16 hp (pow_nonneg hA j) (zero_le_one.trans (gammaConstant_ge_one L))
  change 16 * A ^ j ≤ gammaConstant L ^ (j + 1)
  simpa only [pow_succ, mul_comm] using hh

 theorem labeledGamma_coefficient_bound (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1)
    (c w : (Fin (j + 2) → Bool) → Fin j → (Fin d → ℝ) → ℝ)
    (hc : ∀ labels k, Continuous (c labels k)) (hw : ∀ labels k, Continuous (w labels k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ labels k x, |c labels k x| ≤ L) (hwL : ∀ labels k x, |w labels k x| ≤ L)
    (hb : ∀ labels k x φ θ, |phasedAngular (c labels k x) (w labels k x) φ θ| ≤ L)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    labeledGammaL2Squared U Q M γ η lam hQ hM hη hband Au Av bump c w ≤
      if M ≤ j then gammaConstant L ^ (j + 1) * Au ^ 2 * Av ^ 2 * Real.exp (CE * M) *
        gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  unfold labeledGammaL2Squared
  have hh := Finset.sum_le_sum (fun (labels : Fin (j + 2) → Bool) (_ : labels ∈ Finset.univ) =>
    markedGamma_L2Squared U Q M γ η lam hd hQ hM hM1 hη hlam hband hγ hγ1
      Au Av bump hbump (c labels) (w labels) (hc labels) (hw labels) L CE hL hCE
      (hcL labels) (hwL labels) (hb labels) hbudget)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hh
  by_cases hj : M ≤ j
  · simp only [ite_eq_left hj] at hh ⊢
    have heq : (2 : ℝ) ^ (j + 2) *
        (4 * Au ^ 2 * Av ^ 2 * (3 * Real.exp 1 * L ^ 2) ^ j * Real.exp (CE * M) *
          gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j) =
        (16 * (6 * Real.exp 1 * L ^ 2) ^ j) *
          (Au ^ 2 * Av ^ 2 * Real.exp (CE * M) * gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j) := by
      rw [pow_add]
      have hpow : (6 * Real.exp 1 * L ^ 2) ^ j = (2 : ℝ) ^ j * (3 * Real.exp 1 * L ^ 2) ^ j := by
        rw [← mul_pow]
        congr 1
        ring
      rw [hpow]
      ring
    rw [heq] at hh
    have hnn : 0 ≤ Au ^ 2 * Av ^ 2 * Real.exp (CE * M) * gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j :=
      mul_nonneg (by positivity) (gammaSpatialFactor_nonneg _ (by positivity) M j)
    have hmul := mul_le_mul_of_nonneg_right (gammaConstant_bound L j) hnn
    exact hh.trans (by convert hmul using 1 <;> ring)
  · simpa only [ite_eq_right hj, mul_zero] using hh

end RoughRegime.LatticePriors
