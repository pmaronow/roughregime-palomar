module

public import RoughRegime.AliasPatterns
public import RoughRegime.LatticePenalties


@[expose] public section
/-! Actual product-cube integral bounds for individual lattice Fourier
patterns. These supply the R^(1-M) saving in the coefficient proof. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set MeasureTheory
open RoughRegime.Lattice RoughRegime.LatticeFourier RoughRegime.DyadicDigits
open scoped BigOperators

 theorem latticeCharacteristic_continuous (Q M : ℕ) (η lam : ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : 0 < η) (hband : 4 * (6 * Q / η) ≤ (M : ℝ)) :
    Continuous (latticeCharacteristic Q M η lam) := by
  unfold latticeCharacteristic
  apply continuous_tsum (fun z => by fun_prop) (latticeWeight_summable Q M η hQ hM hη hband)
  intro z w
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    abs_of_nonneg (mul_nonneg (latticeWeight_nonneg Q M η hQ hM hη z) (sq_nonneg _)), mul_one]
  exact mul_le_of_le_one_right (latticeWeight_nonneg Q M η hQ hM hη z)
    (pow_le_one₀ (gate_nonneg _ _ _) (gate_le_one _ _ _))

/-- Fubini factorization for disjoint sets of observation slots, under an
actual finite product probability law. -/
 theorem integral_disjoint_coordinate_products {κ X : Type*} [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (n p : Finset κ) (hdisjoint : Disjoint n p) (fn fp : X → ℝ) :
    (∫ x : κ → X, (∏ j ∈ n, fn (x j)) * (∏ j ∈ p, fp (x j))
      ∂Measure.pi (fun _ : κ => μ)) = (∫ y, fn y ∂μ) ^ n.card * (∫ y, fp y ∂μ) ^ p.card := by
  classical
  let f : κ → X → ℝ := fun j y => (if j ∈ n then fn y else 1) * (if j ∈ p then fp y else 1)
  have hprod (x : κ → X) : (∏ j ∈ n, fn (x j)) * (∏ j ∈ p, fp (x j)) = ∏ j, f j (x j) := by
    unfold f
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod]
  have hf (j : κ) : (∫ y, f j y ∂μ) =
      (if j ∈ n then (∫ y, fn y ∂μ) else 1) * (if j ∈ p then (∫ y, fp y ∂μ) else 1) := by
    by_cases hn : j ∈ n <;> by_cases hp : j ∈ p
    · exact False.elim ((Finset.disjoint_left.mp hdisjoint) hn hp)
    · simp [f, hn, hp]
    · simp [f, hn, hp]
    · simp [f, hn, hp]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]
  simp only [Finset.prod_const]

 def spatialSelectors (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (x : Fin j → Fin d → ℝ) (qi : Fin d × Fin J) (k : Fin j) : ℝ :=
  softDigit U (γ qi.1 qi.2) ((2 : ℝ) ^ (J - qi.2.val) * x k qi.1)

 def spatialPatternPenalty (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (n p : Finset (Fin j)) (e : (Fin d × Fin J) → Bool) (x : Fin j → Fin d → ℝ) : ℝ :=
  patternPenalty n p (spatialSelectors U J d j γ x) (fun qi => mismatchWeight d qi.2.val) e

 theorem spatialPatternPenalty_eq (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (n p : Finset (Fin j)) (e : (Fin d × Fin J) → Bool) (x : Fin j → Fin d → ℝ) :
    spatialPatternPenalty U J d j γ n p e x =
      (∏ k ∈ n, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => e (q, i)) (x k)) *
      (∏ k ∈ p, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => !(e (q, i))) (x k)) := by
  rw [spatialPatternPenalty, patternPenalty_eq_products]
  unfold spatialSelectors softDigitPenalty
  simp_rw [Fintype.prod_prod_type]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  apply Finset.prod_congr rfl
  intro q hq
  apply Finset.prod_congr rfl
  intro i hi
  by_cases he : e (q, i) = true
  · simp [he]
  · have hf : e (q, i) = false := Bool.eq_false_of_not_eq_true he
    simp [hf]

 theorem spatialPatternPenalty_integral_bound (U : SmoothStep) (J d j : ℕ)
    (γ : Fin d → Fin J → ℝ) (n p : Finset (Fin j)) (hdisjoint : Disjoint n p)
    (e : (Fin d × Fin J) → Bool) (hd : 0 < d)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) :
    (∫ x, spatialPatternPenalty U J d j γ n p e x
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      ((((2 : ℝ) ^ (-(J : ℤ))) ^ d) * Real.exp 1) ^ (n.card + p.card) := by
  simp_rw [spatialPatternPenalty_eq]
  rw [integral_disjoint_coordinate_products (cubeUniform d) n p hdisjoint]
  rw [pow_add]
  apply mul_le_mul
  · exact pow_le_pow_left₀ (integral_nonneg (fun x => softDigitPenalty_nonneg U J d γ _ _ x))
      (integral_softDigitPenalty_source_bound U J d γ _ hd hγ hγ1) n.card
  · exact pow_le_pow_left₀ (integral_nonneg (fun x => softDigitPenalty_nonneg U J d γ _ _ x))
      (integral_softDigitPenalty_source_bound U J d γ _ hd hγ hγ1) p.card
  · exact pow_nonneg (integral_nonneg (fun x => softDigitPenalty_nonneg U J d γ _ _ x)) p.card
  · positivity

 theorem spatialSelectors_continuous (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (qi : Fin d × Fin J) (k : Fin j) :
    Continuous (fun x => spatialSelectors U J d j γ x qi k) := by
  unfold spatialSelectors
  exact (softDigit_smooth U (γ qi.1 qi.2) (hγ qi.1 qi.2) (hγ1 qi.1 qi.2)).continuous.comp
    (continuous_const.mul ((continuous_apply qi.1).comp (continuous_apply k)))

 theorem spatialPatternPenalty_continuous (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (n p : Finset (Fin j)) (e : (Fin d × Fin J) → Bool)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4) :
    Continuous (spatialPatternPenalty U J d j γ n p e) := by
  have heq : spatialPatternPenalty U J d j γ n p e = fun x =>
      (∏ k ∈ n, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => e (q, i)) (x k)) *
      (∏ k ∈ p, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => !(e (q, i))) (x k)) :=
    funext (spatialPatternPenalty_eq U J d j γ n p e)
  rw [heq]
  apply Continuous.mul
  · apply continuous_finsetProd
    intro k hk
    exact (softDigitPenalty_continuous U J d γ _ _ hγ hγ1).comp (continuous_apply k)
  · apply continuous_finsetProd
    intro k hk
    exact (softDigitPenalty_continuous U J d γ _ _ hγ hγ1).comp (continuous_apply k)

 theorem spatialPatternPenalty_range (U : SmoothStep) (J d j : ℕ) (γ : Fin d → Fin J → ℝ)
    (n p : Finset (Fin j)) (e : (Fin d × Fin J) → Bool) (hd : 0 < d)
    (x : Fin j → Fin d → ℝ) :
    0 ≤ spatialPatternPenalty U J d j γ n p e x ∧ spatialPatternPenalty U J d j γ n p e x ≤ 1 := by
  rw [spatialPatternPenalty_eq]
  have hΩ : ∀ q : Fin d, ∀ i : Fin J, 0 ≤ mismatchWeight d i.val := fun _ i => mismatchWeight_nonneg d i.val hd
  have h0n : 0 ≤ ∏ k ∈ n, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => e (q, i)) (x k) :=
    Finset.prod_nonneg (fun k _ => softDigitPenalty_nonneg U J d γ _ _ (x k))
  have h0p : 0 ≤ ∏ k ∈ p, softDigitPenalty U J d γ (fun _ i => mismatchWeight d i.val) (fun q i => !(e (q, i))) (x k) :=
    Finset.prod_nonneg (fun k _ => softDigitPenalty_nonneg U J d γ _ _ (x k))
  constructor
  · exact mul_nonneg h0n h0p
  · calc
      _ ≤ 1 * 1 := mul_le_mul
        (Finset.prod_le_one₀ (fun k _ => softDigitPenalty_nonneg U J d γ _ _ (x k))
          (fun k _ => softDigitPenalty_le_one U J d γ _ _ hΩ (x k)))
        (Finset.prod_le_one₀ (fun k _ => softDigitPenalty_nonneg U J d γ _ _ (x k))
          (fun k _ => softDigitPenalty_le_one U J d γ _ _ hΩ (x k))) h0p zero_le_one
      _ = 1 := by norm_num

/-- Individual Fourier patterns, integrated against the actual j-fold cube
law, gain one inverse fine-cell count per nonzero observation mode. -/
 theorem spatial_pattern_integral_bound (U : SmoothStep) (J d j Q M k : ℕ)
    (γ : Fin d → Fin J → ℝ) (η lam : (Fin d × Fin J) → ℝ) (ε : Bool)
    (n p : Finset (Fin j)) (hdisjoint : Disjoint n p)
    (hd : 0 < d) (hQ : 1 ≤ Q) (hM : 0 < M) (hk : 2 * (k : ℝ) < M)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (hη : ∀ qi, 0 < η qi) (hlam : ∀ qi, 1 ≤ lam qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hn : n.card = M + k) (hp : p.card = k) :
    (∫ x, ‖patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)‖
      ∂Measure.pi (fun _ : Fin j => cubeUniform d)) ≤
      Real.exp (∑ qi, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)) *
        ((2 : ℝ) ^ (d * J)) *
        ((((2 : ℝ) ^ (-(J : ℤ))) ^ d) * Real.exp 1) ^ (M + 2 * k) := by
  let μ := Measure.pi (fun _ : Fin j => cubeUniform d)
  let budget := ∑ qi : Fin d × Fin J, mismatchWeight d qi.2.val * ((k : ℝ) + 6 * Q / η qi)
  have hμ : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hpc : Continuous (fun x => patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)) := by
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
  have hi : Integrable (fun x => ‖patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)‖) μ := by
    apply Integrable.of_bound hpc.norm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact patternCharacteristic_norm_le_one Q M η lam ε n p _ hQ hM hη hband)
  have hpen (e : (Fin d × Fin J) → Bool) : Integrable (spatialPatternPenalty U J d j γ n p e) μ := by
    apply Integrable.of_bound (spatialPatternPenalty_continuous U J d j γ n p e hγ hγ1).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (spatialPatternPenalty_range U J d j γ n p e hd x).1]
      exact (spatialPatternPenalty_range U J d j γ n p e hd x).2)
  have hib : Integrable (fun x => Real.exp budget * ∑ e, spatialPatternPenalty U J d j γ n p e x) μ :=
    (integrable_finsetSum _ (fun e _ => hpen e)).const_mul _
  have hmono : (∫ x, ‖patternCharacteristic Q M η lam ε n p (spatialSelectors U J d j γ x)‖ ∂μ) ≤
      ∫ x, Real.exp budget * ∑ e, spatialPatternPenalty U J d j γ n p e x ∂μ := by
    apply integral_mono hi hib
    intro x
    apply patternCharacteristic_penalty_bound Q M k η lam (fun qi => mismatchWeight d qi.2.val) ε n p _
      hQ hM hk hη hlam hband (fun qi => mismatchWeight_nonneg d qi.2.val hd) hn hp
    intro qi a
    exact softDigit_range U _ _ (hγ qi.1 qi.2) (hγ1 qi.1 qi.2)
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun e _ => hpen e)] at hmono
  have hs := Finset.sum_le_sum (fun (e : (Fin d × Fin J) → Bool) (_ : e ∈ Finset.univ) =>
    spatialPatternPenalty_integral_bound U J d j γ n p hdisjoint e hd hγ hγ1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, hn, hp] at hs
  have hcards : M + k + k = M + 2 * k := by omega
  rw [hcards] at hs
  have hfinal := hmono.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos budget).le)
  simpa only [μ, budget, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using hfinal

end RoughRegime.LatticePriors
