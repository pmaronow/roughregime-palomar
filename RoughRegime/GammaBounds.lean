module

public import RoughRegime.ModePatterns


@[expose] public section
/-! Norm estimates for the literal lattice likelihood coefficients. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open RoughRegime.Lattice RoughRegime.LatticeFourier RoughRegime.DyadicDigits
open scoped BigOperators

 theorem cube_cell_weight_eq_inverse (J d : ℕ) :
    ((2 : ℝ) ^ (-(J : ℤ))) ^ d = ((2 : ℝ) ^ (d * J))⁻¹ := by
  simp only [zpow_neg, zpow_natCast, inv_pow, ← pow_mul]
  rw [Nat.mul_comm]

 theorem cell_saving_pow_bound (R : ℝ) (hR : 1 ≤ R) (M N j : ℕ) (hMN : M ≤ N) (hNj : N ≤ j) :
    R * (R⁻¹ * Real.exp 1) ^ N ≤ (Real.exp 1) ^ j * (R / R ^ M) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  rw [mul_pow, inv_pow]
  have hp := pow_le_pow_right₀ hR hMN
  have hq := pow_le_pow_right₀ he1 hNj
  have hi : (R ^ N)⁻¹ ≤ (R ^ M)⁻¹ := inv_anti₀ (pow_pos hR0 M) hp
  have hh := mul_le_mul hi hq (by positivity) (by positivity)
  have hh' := mul_le_mul_of_nonneg_left hh hR0.le
  convert hh' using 1 <;> simp only [div_eq_mul_inv] <;> ring

 variable {J d j : ℕ}

 def spatialLatticeGamma (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ)) (c w : Fin j → (Fin d → ℝ) → ℝ)
    (x : Fin j → Fin d → ℝ) : ℝ :=
  latticeGamma Q M η lam hQ hM hη hband
    (fun k qi => spatialSelectors U J d j γ x qi k) (fun k => c k (x k)) (fun k => w k (x k))

 def spatialGammaTerm (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (c w : Fin j → (Fin d → ℝ) → ℝ)
    (ε : Bool) (o : Fin j → Fin 3) (x : Fin j → Fin d → ℝ) : ℂ :=
  latticeGammaTerm Q M η lam (fun k qi => spatialSelectors U J d j γ x qi k)
    (fun k => c k (x k)) (fun k => w k (x k)) ε o

 theorem spatial_patternCharacteristic_continuous (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ) (ε : Bool) (n p : Finset (Fin j))
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) :
    Continuous (fun x => patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)) := by
  unfold patternCharacteristic signedPatternFrequency patternFrequency
  apply continuous_finsetProd
  intro qi hqi
  apply (latticeCharacteristic_continuous Q M (η qi) (lam qi) hQ hM (hη qi) (hband qi)).comp
  have hc : Continuous (fun x => (∑ a ∈ n, spatialSelectors U J d j γ x qi a) -
      ∑ a ∈ p, spatialSelectors U J d j γ x qi a) :=
    (continuous_finsetSum _ (fun a _ => spatialSelectors_continuous U J d j γ hγ hγ1 qi a)).sub
      (continuous_finsetSum _ (fun a _ => spatialSelectors_continuous U J d j γ hγ hγ1 qi a))
  cases ε
  · exact hc
  · exact hc.neg

 theorem spatialGammaTerm_as_pattern (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (ε : Bool) (o : Fin j → Fin 3) (x : Fin j → Fin d → ℝ) :
    spatialGammaTerm U Q M γ η lam c w ε o x =
      observationModeProduct (fun k => c k (x k)) (fun k => w k (x k)) o *
        (if patternTotalFrequency M ε o = 0 then
          patternCharacteristic Q M η lam ε (patternMinus ε o) (patternPlus ε o)
            (spatialSelectors U J d j γ x) else 0) := by
  unfold spatialGammaTerm latticeGammaTerm patternCharacteristic
  congr 1
  split_ifs
  · apply Finset.prod_congr rfl
    intro qi hqi
    rw [observationPatternFrequency_as_signedPattern]
  · rfl

 theorem spatialGammaTerm_continuous (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ) (ε : Bool) (o : Fin j → Fin 3)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k)) :
    Continuous (spatialGammaTerm U Q M γ η lam c w ε o) := by
  have heq : spatialGammaTerm U Q M γ η lam c w ε o = fun x =>
      observationModeProduct (fun k => c k (x k)) (fun k => w k (x k)) o *
        (if patternTotalFrequency M ε o = 0 then
          patternCharacteristic Q M η lam ε (patternMinus ε o) (patternPlus ε o)
            (spatialSelectors U J d j γ x) else 0) :=
    funext (spatialGammaTerm_as_pattern U Q M γ η lam c w ε o)
  rw [heq]
  have hamp : Continuous (fun x : Fin j → Fin d → ℝ =>
      observationModeProduct (fun k => c k (x k)) (fun k => w k (x k)) o) := by
    unfold observationModeProduct
    apply continuous_finsetProd
    intro k hk
    unfold modeAmplitude
    split_ifs
    · exact Complex.continuous_ofReal.comp ((hc k).comp (continuous_apply k))
    · exact Complex.continuous_ofReal.comp ((hw k).comp (continuous_apply k))
  by_cases hzero : patternTotalFrequency M ε o = 0
  · simp only [ite_eq_left hzero]
    exact hamp.mul (spatial_patternCharacteristic_continuous U Q M γ η lam ε _ _ hQ hM hη hband hγ hγ1)
  · simp only [ite_eq_right hzero, mul_zero]
    exact continuous_const

 theorem spatialGammaTerm_norm_bound (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ) (ε : Bool) (o : Fin j → Fin 3)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (c w : Fin j → (Fin d → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc : ∀ k x, |c k x| ≤ L) (hw : ∀ k x, |w k x| ≤ L) (x : Fin j → Fin d → ℝ) :
    ‖spatialGammaTerm U Q M γ η lam c w ε o x‖ ≤ L ^ j := by
  rw [spatialGammaTerm_as_pattern, norm_mul]
  have ha := observationModeProduct_norm_bound (fun k => c k (x k)) (fun k => w k (x k)) L hL
    (fun k => hc k (x k)) (fun k => hw k (x k)) o
  by_cases hzero : patternTotalFrequency M ε o = 0
  · rw [ite_eq_left hzero]
    have hh := mul_le_mul ha (patternCharacteristic_norm_le_one Q M η lam ε (patternMinus ε o) (patternPlus ε o) (spatialSelectors U J d j γ x) hQ hM hη hband)
      (norm_nonneg _) (pow_nonneg hL j)
    simpa using hh
  · simp [hzero, pow_nonneg hL j]

 theorem spatialGammaTerm_integral_bound (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ) (ε : Bool) (o : Fin j → Fin 3)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L)
    (hj : (j : ℝ) < M + Real.sqrt M)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    (∫ x, ‖spatialGammaTerm U Q M γ η lam c w ε o x‖
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      (L * Real.exp 1) ^ j * Real.exp (CE * M) *
        ((2 : ℝ) ^ (d * J) / ((2 : ℝ) ^ (d * J)) ^ M) := by
  let μ := Measure.pi (fun _ : Fin j => cubeUniform d)
  let R : ℝ := 2 ^ (d * J)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by positivity
  have hresult : 0 ≤ (L * Real.exp 1) ^ j * Real.exp (CE * M) * (R / R ^ M) := by positivity
  by_cases hzero : patternTotalFrequency M ε o = 0
  · let n := patternMinus ε o
    let p := patternPlus ε o
    let k := p.card
    have hn : n.card = M + k := patternMinus_card M ε o hzero
    have hcard : M + 2 * k ≤ j := by
      have hh := modePattern_card_bound ε o
      change n.card + p.card ≤ j at hh
      omega
    have hk2 : 2 * (k : ℝ) < Real.sqrt M := patternPlus_small M ε o hzero hj
    have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hsqrtM : Real.sqrt M ≤ M := (Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩)
    have hkM : 2 * (k : ℝ) < M := hk2.trans_le hsqrtM
    have hk : (k : ℝ) ≤ Real.sqrt M := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hpc := spatial_patternCharacteristic_continuous U Q M γ η lam ε n p hQ hM hη hband hγ hγ1
    have hpi : Integrable (fun x => ‖patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)‖) μ := by
      apply Integrable.of_bound hpc.norm.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact patternCharacteristic_norm_le_one Q M η lam ε n p _ hQ hM hη hband)
    have hfi : Integrable (fun x => ‖spatialGammaTerm U Q M γ η lam c w ε o x‖) μ := by
      apply Integrable.of_bound
        (spatialGammaTerm_continuous U Q M γ η lam ε o hQ hM hη hband hγ hγ1 c w hc hw).norm.aestronglyMeasurable (L ^ j)
      exact Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact spatialGammaTerm_norm_bound U Q M γ η lam ε o hQ hM hη hband c w L hL hcL hwL x)
    have hmono : (∫ x, ‖spatialGammaTerm U Q M γ η lam c w ε o x‖ ∂μ) ≤
        L ^ j * (∫ x, ‖patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)‖ ∂μ) := by
      rw [← integral_const_mul]
      apply integral_mono hfi (hpi.const_mul _)
      intro x
      dsimp only
      rw [spatialGammaTerm_as_pattern, ite_eq_left hzero, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (observationModeProduct_norm_bound _ _ L hL (fun k => hcL k (x k)) (fun k => hwL k (x k)) o) (norm_nonneg _)
    have hpattern := spatial_pattern_integral_bound U J d j Q M k γ η lam ε n p
      (patternMinusPlus_disjoint ε o) hd hQ hM hkM hγ hγ1 hη hlam hband hn rfl
    have hpattern' := hpattern.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbudget k hk)) hR0.le) (by positivity))
    rw [cube_cell_weight_eq_inverse] at hpattern'
    have hsave := cell_saving_pow_bound R hR M (M + 2 * k) j (by omega) hcard
    have hsave' := mul_le_mul_of_nonneg_left hsave (Real.exp_pos (CE * M)).le
    have hfinish := hmono.trans (mul_le_mul_of_nonneg_left hpattern' (pow_nonneg hL j))
    have hfinish' := hfinish.trans (mul_le_mul_of_nonneg_left
      (by simpa only [R, mul_assoc] using hsave') (pow_nonneg hL j))
    simpa only [μ, R, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hfinish'
  · have heq : (fun x => ‖spatialGammaTerm U Q M γ η lam c w ε o x‖) = 0 := by
      funext x
      simp [spatialGammaTerm_as_pattern, hzero]
    rw [heq]
    simpa using hresult

 theorem spatialLatticeGamma_continuous (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k)) :
    Continuous (spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w) := by
  have heq : spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w = fun x =>
      (∑ ε : Bool, ∑ o : Fin j → Fin 3, spatialGammaTerm U Q M γ η lam c w ε o x).re := by
    funext x
    have hh := latticeGamma_expansion Q M η lam hQ hM hη hband
      (fun k qi => spatialSelectors U J d j γ x qi k) (fun k => c k (x k)) (fun k => w k (x k))
    exact congrArg Complex.re hh
  rw [heq]
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro ε hε
  apply continuous_finsetSum
  intro o ho
  exact spatialGammaTerm_continuous U Q M γ η lam ε o hQ hM hη hband hγ hγ1 c w hc hw

 theorem spatialLatticeGamma_integrable (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L : ℝ) (hL : 0 ≤ L) (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L) :
    Integrable (spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w)
      (Measure.pi (fun _ : Fin j => cubeUniform d)) := by
  have hterm (ε : Bool) (o : Fin j → Fin 3) : Integrable
      (spatialGammaTerm U Q M γ η lam c w ε o) (Measure.pi (fun _ : Fin j => cubeUniform d)) := by
    apply Integrable.of_bound
      (spatialGammaTerm_continuous U Q M γ η lam ε o hQ hM hη hband hγ hγ1 c w hc hw).aestronglyMeasurable (L ^ j)
    exact Filter.Eventually.of_forall (spatialGammaTerm_norm_bound U Q M γ η lam ε o hQ hM hη hband c w L hL hcL hwL)
  have hi := (integrable_finsetSum Finset.univ (fun ε _ =>
    integrable_finsetSum Finset.univ (fun o _ => hterm ε o))).re
  have heq : (fun x => (∑ ε : Bool, ∑ o : Fin j → Fin 3,
      spatialGammaTerm U Q M γ η lam c w ε o x).re) =
      spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w := by
    funext x
    exact (congrArg Complex.re (latticeGamma_expansion Q M η lam hQ hM hη hband
      (fun k qi => spatialSelectors U J d j γ x qi k) (fun k => c k (x k)) (fun k => w k (x k)))).symm
  change Integrable (fun x => (∑ ε : Bool, ∑ o : Fin j → Fin 3, spatialGammaTerm U Q M γ η lam c w ε o x).re) _ at hi
  rwa [heq] at hi

 theorem spatialLatticeGamma_L1_moderate (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L)
    (hj : (j : ℝ) < M + Real.sqrt M)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    (∫ x, |spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x|
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      2 * (3 * Real.exp 1 * L) ^ j * Real.exp (CE * M) *
        ((2 : ℝ) ^ (d * J) / ((2 : ℝ) ^ (d * J)) ^ M) := by
  let μ := Measure.pi (fun _ : Fin j => cubeUniform d)
  let F := spatialGammaTerm (j := j) U Q M γ η lam c w
  have hterm (ε : Bool) (o : Fin j → Fin 3) : Integrable (fun x => ‖F ε o x‖) μ := by
    apply Integrable.of_bound
      (spatialGammaTerm_continuous U Q M γ η lam ε o hQ hM hη hband hγ hγ1 c w hc hw).norm.aestronglyMeasurable (L ^ j)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact spatialGammaTerm_norm_bound U Q M γ η lam ε o hQ hM hη hband c w L hL hcL hwL x)
  have hi := (spatialLatticeGamma_integrable (j := j) U Q M γ η lam hQ hM hη hband hγ hγ1 c w hc hw L hL hcL hwL).abs
  have hs := integrable_finsetSum Finset.univ (fun ε _ =>
    integrable_finsetSum Finset.univ (fun o _ => hterm ε o))
  have hmono : (∫ x, |spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x| ∂μ) ≤
      ∫ x, ∑ ε : Bool, ∑ o : Fin j → Fin 3, ‖F ε o x‖ ∂μ := by
    apply integral_mono hi hs
    intro x
    dsimp only
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    change ‖(latticeGamma Q M η lam hQ hM hη hband _ _ _ : ℂ)‖ ≤ _
    rw [latticeGamma_expansion]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ε _ => norm_sum_le _ _))
  rw [integral_finsetSum Finset.univ (fun ε _ => integrable_finsetSum Finset.univ (fun o _ => hterm ε o))] at hmono
  simp_rw [integral_finsetSum Finset.univ (fun o _ => hterm _ o)] at hmono
  have hb := Finset.sum_le_sum (fun (ε : Bool) (_ : ε ∈ Finset.univ) =>
    Finset.sum_le_sum (fun (o : Fin j → Fin 3) (_ : o ∈ Finset.univ) =>
      spatialGammaTerm_integral_bound U Q M γ η lam ε o hd hQ hM hM1 hη hlam hband hγ hγ1 c w hc hw
        L CE hL hCE hcL hwL hj hbudget))
  have hh := hmono.trans hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hh
  convert hh using 1 <;> simp only [mul_pow] <;> ring

 def gammaSpatialFactor (R : ℝ) (M j : ℕ) : ℝ :=
    R ^ (1 - (M : ℝ) + ((j : ℝ) - M) * Real.sqrt M)

 theorem gammaSpatialFactor_nonneg (R : ℝ) (hR : 0 ≤ R) (M j : ℕ) : 0 ≤ gammaSpatialFactor R M j :=
  Real.rpow_nonneg hR _

 theorem ratio_le_gammaSpatialFactor (R : ℝ) (hR : 1 ≤ R) (M j : ℕ) (hj : M ≤ j) :
    R / R ^ M ≤ gammaSpatialFactor R M j := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have heq : R / R ^ M = R ^ (1 - (M : ℝ)) := by
    rw [Real.rpow_sub hR0, Real.rpow_one, Real.rpow_natCast]
  rw [heq]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hjr : (M : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith [Real.sqrt_nonneg (M : ℝ)]

 theorem one_le_gammaSpatialFactor_high (R : ℝ) (hR : 1 ≤ R) (M j : ℕ)
    (hj : (M : ℝ) + Real.sqrt M ≤ j) : 1 ≤ gammaSpatialFactor R M j := by
  apply Real.one_le_rpow hR
  have hs := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hm := mul_le_mul_of_nonneg_right (show Real.sqrt M ≤ (j : ℝ) - M by linarith) (Real.sqrt_nonneg M)
  nlinarith

 theorem spatialLatticeGamma_abs_bound (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (c w : Fin j → (Fin d → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ k x φ θ, |phasedAngular (c k x) (w k x) φ θ| ≤ L)
    (x : Fin j → Fin d → ℝ) :
    |spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w x| ≤ 2 * L ^ j :=
  latticeGamma_abs_bound Q M η lam hQ hM hη hband _ _ _ L hL
    (fun _z θ k => hb k (x k) _ θ)

 theorem spatialLatticeGamma_L1 (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L)
    (hb : ∀ k x φ θ, |phasedAngular (c k x) (w k x) φ θ| ≤ L)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    (∫ x, |spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x|
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      if M ≤ j then 2 * (3 * Real.exp 1 * L) ^ j * Real.exp (CE * M) *
        gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  by_cases hMj : M ≤ j
  · rw [ite_eq_left hMj]
    let R : ℝ := 2 ^ (d * J)
    have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
    by_cases hj : (j : ℝ) < M + Real.sqrt M
    · have hh := spatialLatticeGamma_L1_moderate U Q M γ η lam hd hQ hM hM1 hη hlam hband hγ hγ1
        c w hc hw L CE hL hCE hcL hwL hj hbudget
      exact hh.trans (mul_le_mul_of_nonneg_left (ratio_le_gammaSpatialFactor R hR M j hMj) (by positivity))
    · have hp : (∫ x, |spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x|
          ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤ 2 * L ^ j := by
        have hn : ‖∫ x, |spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x|
            ∂Measure.pi (fun _ : Fin j => cubeUniform d)‖ ≤ 2 * L ^ j := by
          simpa using
            norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin j => cubeUniform d))
              (f := fun x => |spatialLatticeGamma U Q M γ η lam hQ hM hη hband c w x|)
              (Filter.Eventually.of_forall (fun x => by
                simp only [Real.norm_eq_abs, abs_abs]
                exact spatialLatticeGamma_abs_bound U Q M γ η lam hQ hM hη hband c w L hL hb x))
        rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))] at hn
      have hbase : L ≤ 3 * Real.exp 1 * L := by
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
        nlinarith
      have hpow := pow_le_pow_left₀ hL hbase j
      have hexp : 1 ≤ Real.exp (CE * M) := Real.one_le_exp_iff.mpr (mul_nonneg hCE (Nat.cast_nonneg _))
      have hfactor := one_le_gammaSpatialFactor_high R hR M j (le_of_not_gt hj)
      have h1 : 2 * L ^ j ≤ 2 * (3 * Real.exp 1 * L) ^ j := mul_le_mul_of_nonneg_left hpow (by norm_num)
      have h2 : 2 * (3 * Real.exp 1 * L) ^ j ≤
          2 * (3 * Real.exp 1 * L) ^ j * Real.exp (CE * M) := le_mul_of_one_le_right (by positivity) hexp
      have h3 : 2 * (3 * Real.exp 1 * L) ^ j * Real.exp (CE * M) ≤
          2 * (3 * Real.exp 1 * L) ^ j * Real.exp (CE * M) * gammaSpatialFactor R M j :=
        le_mul_of_one_le_right (by positivity) hfactor
      exact hp.trans (h1.trans (h2.trans h3))
  · rw [ite_eq_right hMj]
    have heq : spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w = 0 := by
      funext x
      exact latticeGamma_zero Q M η lam hQ hM hη hband _ _ _ (Nat.lt_of_not_ge hMj)
    simp [heq]

 theorem spatialLatticeGamma_L2Squared (U : SmoothStep) (Q M : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hM1 : 1 ≤ M)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hc : ∀ k, Continuous (c k)) (hw : ∀ k, Continuous (w k))
    (L CE : ℝ) (hL : 0 ≤ L) (hCE : 0 ≤ CE)
    (hcL : ∀ k x, |c k x| ≤ L) (hwL : ∀ k x, |w k x| ≤ L)
    (hb : ∀ k x φ θ, |phasedAngular (c k x) (w k x) φ θ| ≤ L)
    (hbudget : ∀ k : ℕ, (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) ≤ CE * M) :
    (∫ x, (spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w x) ^ 2
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      if M ≤ j then 4 * (3 * Real.exp 1 * L ^ 2) ^ j * Real.exp (CE * M) *
        gammaSpatialFactor ((2 : ℝ) ^ (d * J)) M j else 0 := by
  let μ := Measure.pi (fun _ : Fin j => cubeUniform d)
  let G := spatialLatticeGamma (j := j) U Q M γ η lam hQ hM hη hband c w
  have hsup : ∀ x, |G x| ≤ 2 * L ^ j :=
    spatialLatticeGamma_abs_bound U Q M γ η lam hQ hM hη hband c w L hL hb
  have hi : Integrable G μ := spatialLatticeGamma_integrable U Q M γ η lam hQ hM hη hband hγ hγ1 c w hc hw L hL hcL hwL
  have hsq : Integrable (fun x => G x ^ 2) μ := by
    simpa only [pow_two] using hi.mul_bdd hi.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hsup x))
  have hmono : (∫ x, G x ^ 2 ∂μ) ≤ 2 * L ^ j * ∫ x, |G x| ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hsq (hi.abs.const_mul _)
    intro x
    dsimp only
    have hh := mul_le_mul_of_nonneg_right (hsup x) (abs_nonneg (G x))
    nlinarith [sq_abs (G x)]
  have hL1 := spatialLatticeGamma_L1 U Q M γ η lam hd hQ hM hM1 hη hlam hband hγ hγ1
    c w hc hw L CE hL hCE hcL hwL hb hbudget
  have hh := hmono.trans (mul_le_mul_of_nonneg_left hL1 (by positivity))
  by_cases hj : M ≤ j
  · simp only [ite_eq_left hj] at hh ⊢
    convert hh using 1 <;> simp only [pow_two, mul_pow] <;> ring
  · simpa only [ite_eq_right hj, mul_zero] using hh

 theorem source_spatialGamma_constants (d Q : ℕ) (hd : 0 < d)
    (gammaStar lambdaStar alpha0 s0 : ℝ)
    (hγ : 0 < gammaStar) (hlam : 0 < lambdaStar) (ha : 0 < alpha0) (hs0 : 0 < s0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (J M k : ℕ),
      (2 : ℝ) ^ ((J : ℝ) * s0) ≤ M → (k : ℝ) ≤ Real.sqrt M →
      (∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val *
        ((k : ℝ) + 6 * Q / sourceEta gammaStar lambdaStar alpha0 ((2 : ℝ) ^ ((J : ℝ) * s0)) qi.2.val)) ≤ CE * M := by
  obtain ⟨CE, hCE, hbound⟩ := source_pattern_budget_bound_exact d Q hd gammaStar lambdaStar alpha0 s0 hγ hlam ha hs0
  refine ⟨CE, hCE, ?_⟩
  intro J M k hmM hkM
  rw [Fintype.sum_prod_type]
  exact hbound J M k hmM hkM

end RoughRegime.LatticePriors
