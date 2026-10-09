module

public import RoughRegime.PoissonNormalization
public import RoughRegime.OrdinaryGammaNorm


@[expose] public section
/-! The actual lattice construction as the affine phase field used by the
continuous-mark Poisson experiment. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory
open RoughRegime.LatticeFourier RoughRegime.DyadicDigits RoughRegime.PoissonMeasure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 variable {J d : ℕ}
 def sourceMarkPhase (U : SmoothStep) (M : ℕ) (γ : Fin d → Fin J → ℝ)
    (ξ : Fin d × Fin J → ℤ) (x : Fin d → ℝ) : ℝ :=
  ∑ qi : Fin d × Fin J, latticeStep M * ξ qi *
    softDigit U (γ qi.1 qi.2) ((2 : ℝ) ^ (J - qi.2.val) * x qi.1)

 def latticePhaseField (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (p0 r0 h : ℝ) (outer bump : (Fin d → ℝ) → ℝ) :
    AffinePhaseField (Fin d × Fin J → ℤ) ((Fin d → ℝ) × Bool) where
  c _ x := centeredZero p0 r0 outer x.1
  a ξ x := 2 * centeredWave h outer x.2 x.1 * Real.cos (sourceMarkPhase U M γ ξ x.1)
  b ξ x := -(2 * centeredWave h outer x.2 x.1 * Real.sin (sourceMarkPhase U M γ ξ x.1))
  hu ξ x := jointGate Q M η lam ξ * bump x.1
  hv ξ x := jointGate Q M η lam ξ * bump x.1

 theorem latticePhaseField_measurable (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (p0 r0 h : ℝ) (outer bump : (Fin d → ℝ) → ℝ)
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (ho : Continuous outer) (hb : Continuous bump) :
    (latticePhaseField U Q M γ η lam p0 r0 h outer bump).IsMeasurable := by
  have hs (qi : Fin d × Fin J) : Measurable (softDigit U (γ qi.1 qi.2)) :=
    (softDigit_smooth U _ (hγ qi.1 qi.2) (hγ1 qi.1 qi.2)).continuous.measurable
  have hcast : Measurable (fun n : ℤ => (n : ℝ)) := measurable_of_countable _
  have hsign : Measurable RoughRegime.Lower.sign := measurable_of_countable _
  have hg : Measurable (jointGate Q M η lam) := jointGate_measurable Q M η lam
  have hphase : Measurable (fun p : (Fin d × Fin J → ℤ) × ((Fin d → ℝ) × Bool) =>
      sourceMarkPhase U M γ p.1 p.2.1) := by
    unfold sourceMarkPhase
    fun_prop
  constructor
  all_goals unfold Function.uncurry latticePhaseField centeredZero centeredWave; fun_prop

 theorem latticePhaseField_bounded (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (p0 r0 h L : ℝ) (hL : 0 ≤ L)
    (outer bump : (Fin d → ℝ) → ℝ) (hbump : ∀ x, |bump x| ≤ 1)
    (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L) :
    (latticePhaseField U Q M γ η lam p0 r0 h outer bump).Bounded (1 + 2 * L) := by
  have hc (x : (Fin d → ℝ) × Bool) := centered_coefficients_bounds p0 r0 h L outer ho0 ho1 hp hh hrlo hrhi x.2 x.1
  have hgate (ξ : Fin d × Fin J → ℤ) : |jointGate Q M η lam ξ| ≤ 1 := by
    rw [abs_of_nonneg (jointGate_bounds Q M η lam ξ).1]
    exact (jointGate_bounds Q M η lam ξ).2
  constructor
  · intro ξ x; exact (hc x).1.trans (by linarith)
  · intro ξ x
    change |2 * centeredWave h outer x.2 x.1 * Real.cos _| ≤ _
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have ht := mul_le_mul (mul_le_mul_of_nonneg_left (hc x).2 (by norm_num : (0 : ℝ) ≤ 2))
      (Real.abs_cos_le_one (sourceMarkPhase U M γ ξ x.1)) (abs_nonneg _) (by positivity : 0 ≤ 2 * L)
    nlinarith
  · intro ξ x
    change |-(2 * centeredWave h outer x.2 x.1 * Real.sin _)| ≤ _
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have ht := mul_le_mul (mul_le_mul_of_nonneg_left (hc x).2 (by norm_num : (0 : ℝ) ≤ 2))
      (Real.abs_sin_le_one (sourceMarkPhase U M γ ξ x.1)) (abs_nonneg _) (by positivity : 0 ≤ 2 * L)
    nlinarith
  all_goals intro ξ x; change |jointGate Q M η lam ξ * bump x.1| ≤ _
            rw [abs_mul]
            have ht := mul_le_mul (hgate ξ) (hbump x.1) (abs_nonneg _) zero_le_one
            nlinarith

 theorem latticePhaseField_density (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (p0 r0 h : ℝ) (outer bump : (Fin d → ℝ) → ℝ)
    (ξ : Fin d × Fin J → ℤ) (θ : ℝ) (x : (Fin d → ℝ) × Bool) :
    (latticePhaseField U Q M γ η lam p0 r0 h outer bump).unsigned 1 1 0 (ξ, θ) x =
      phasedAngular (centeredZero p0 r0 outer x.1) (centeredWave h outer x.2 x.1)
        (sourceMarkPhase U M γ ξ x.1) θ := by
  simp only [AffinePhaseField.unsigned, latticePhaseField, ite_true]
  rw [phasedAngular_eq_affineAngular]
  rfl

 theorem leadingLabels_succ_succ (j : ℕ) (k : Fin j) : leadingLabels j k.succ.succ = 0 := by
  have h0 : k.succ.succ ≠ (0 : Fin (j + 2)) := by
    intro he
    have hv := congrArg Fin.val he
    change k.val + 1 + 1 = 0 at hv
    omega
  have h1 : k.succ.succ ≠ (1 : Fin (j + 2)) := by
    intro he
    have hv := congrArg Fin.val he
    change k.val + 1 + 1 = 1 % (j + 2) at hv
    have hm : 1 % (j + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  simp only [leadingLabels, h0, h1, ite_false]

 theorem latticePhaseField_unsigned_tensor (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (p0 r0 h Au Av : ℝ) (outer bump : (Fin d → ℝ) → ℝ)
    (j : ℕ) (p : (Fin d × Fin J → ℤ) × ℝ)
    (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    labeledTensor ((latticePhaseField U Q M γ η lam p0 r0 h outer bump).unsigned Au Av)
      (j + 2) (leadingLabels j) p xs =
      Au * Av * bump (xs 0).1 * bump (xs 1).1 * jointGate Q M η lam p.1 ^ 2 *
        ∏ k : Fin j, phasedAngular (centeredZero p0 r0 outer (xs k.succ.succ).1)
          (centeredWave h outer (xs k.succ.succ).2 (xs k.succ.succ).1)
          (sourceMarkPhase U M γ p.1 (xs k.succ.succ).1) p.2 := by
  unfold labeledTensor
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hzero : leadingLabels j 0 = 1 := by simp [leadingLabels]
  have hone : leadingLabels j (Fin.succ 0) = 2 := by
    simp [leadingLabels]
  rw [hzero, hone]
  have hz (k : Fin j) : leadingLabels j k.succ.succ = 0 := leadingLabels_succ_succ j k
  have hprod : (∏ k : Fin j,
      (latticePhaseField U Q M γ η lam p0 r0 h outer bump).unsigned Au Av (leadingLabels j k.succ.succ) p (xs k.succ.succ)) =
      ∏ k : Fin j, phasedAngular (centeredZero p0 r0 outer (xs k.succ.succ).1)
          (centeredWave h outer (xs k.succ.succ).2 (xs k.succ.succ).1)
          (sourceMarkPhase U M γ p.1 (xs k.succ.succ).1) p.2 := by
    apply Finset.prod_congr rfl
    intro k _
    rw [hz k]
    simp only [AffinePhaseField.unsigned, latticePhaseField, ite_true]
    rw [phasedAngular_eq_affineAngular]
    rfl
  rw [hprod]
  simp only [AffinePhaseField.unsigned, latticePhaseField]
  norm_num [Fin.ext_iff]
  ring

set_option maxHeartbeats 500000 in
 theorem latticePhaseField_leading_mixture (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M)
    (hη : ∀ qi, 0 < η qi) (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (p0 r0 h Au Av L : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hL : 0 ≤ L)
    (outer bump : (Fin d → ℝ) → ℝ) (ho : Continuous outer) (hbc : Continuous bump)
    (hbump : ∀ x, |bump x| ≤ 1) (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L)
    (j : ℕ) (xs : Fin (j + 2) → (Fin d → ℝ) × Bool) :
    labeledMixture (phaseBase (gatePrior Q M η hQ hM hη hband)) (phaseDifference M)
      ((latticePhaseField U Q M γ η lam p0 r0 h outer bump).feature Au Av)
      (j + 2) (leadingLabels j) xs =
      ordinarySignedGamma (j := j) U Q M γ η lam hQ hM hη hband Au Av bump
        (fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
        (fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)) xs := by
  let F := latticePhaseField U Q M γ η lam p0 r0 h outer bump
  let ν := gatePrior Q M η hQ hM hη hband
  let C := 1 + 2 * L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : F.IsMeasurable := latticePhaseField_measurable U Q M γ η lam p0 r0 h outer bump hγ hγ1 ho hbc
  have hb : F.Bounded C := latticePhaseField_bounded U Q M γ η lam p0 r0 h L hL outer bump hbump ho0 ho1 hp hh hrlo hrhi
  have he := F.labeled_parity hm ν Au Av C hAu hAu1 hAv hAv1 hC hb M (j + 2) (leadingLabels j) xs
  rw [leadingLabels_count_u, leadingLabels_count_v] at he
  simp only [odd_one, and_self, ite_true] at he
  let f := fun p : (Fin d × Fin J → ℤ) × ℝ => Real.cos ((M : ℝ) * p.2) *
    labeledTensor (F.unsigned Au Av) (j + 2) (leadingLabels j) p xs
  have hg : Measurable (jointGate Q M η lam) := jointGate_measurable Q M η lam
  have hphase (k : Fin j) : Measurable (fun ξ : Fin d × Fin J → ℤ =>
      sourceMarkPhase U M γ ξ (xs k.succ.succ).1) := measurable_of_countable _
  have hf : Measurable f := by
    dsimp only [f, F]
    simp_rw [latticePhaseField_unsigned_tensor]
    unfold phasedAngular
    fun_prop
  have hfb : ∀ p, |f p| ≤ (3 * C) ^ (j + 2) := by
    intro p
    have ht := labeledTensor_bound (F.unsigned Au Av) (3 * C)
      (fun l p x => F.unsigned_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb l p x)
      (j + 2) (leadingLabels j) p xs
    dsimp only [f]
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) ht (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hi : Integrable f (ν.prod LatticePriors.angleUniform) := bounded_integrable _ f hf _ hfb
  change labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
    (F.feature Au Av) (j + 2) (leadingLabels j) xs = _
  rw [he, integral_prod _ hi, ordinarySignedGamma_eq]
  dsimp only [f, F]
  simp_rw [latticePhaseField_unsigned_tensor]
  let A := Au * Av * bump (xs 0).1 * bump (xs 1).1
  have hpoint (ξ : Fin d × Fin J → ℤ) :
      (∫ θ, Real.cos ((M : ℝ) * θ) *
        (A * jointGate Q M η lam ξ ^ 2 *
          ∏ k : Fin j, phasedAngular (centeredZero p0 r0 outer (xs k.succ.succ).1)
            (centeredWave h outer (xs k.succ.succ).2 (xs k.succ.succ).1)
            (sourceMarkPhase U M γ ξ (xs k.succ.succ).1) θ) ∂LatticePriors.angleUniform) =
      A * (jointGate Q M η lam ξ ^ 2 *
        (∫ θ, Real.cos ((M : ℝ) * θ) *
          ∏ k : Fin j, phasedAngular (centeredZero p0 r0 outer (xs k.succ.succ).1)
            (centeredWave h outer (xs k.succ.succ).2 (xs k.succ.succ).1)
            (sourceMarkPhase U M γ ξ (xs k.succ.succ).1) θ ∂LatticePriors.angleUniform)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by ring
  change 2 * (∫ ξ, (∫ θ, Real.cos ((M : ℝ) * θ) *
    (A * jointGate Q M η lam ξ ^ 2 * ∏ k : Fin j,
      phasedAngular (centeredZero p0 r0 outer (xs k.succ.succ).1)
        (centeredWave h outer (xs k.succ.succ).2 (xs k.succ.succ).1)
        (sourceMarkPhase U M γ ξ (xs k.succ.succ).1) θ) ∂LatticePriors.angleUniform) ∂ν) = _
  simp_rw [hpoint]
  rw [integral_const_mul]
  unfold markedGamma spatialLatticeGamma latticeGamma splitSpatialMarks spatialMarkLabels
  dsimp only
  change 2 * (A * _) = A * (2 * _)
  dsimp only [ν]
  unfold sourceMarkPhase observationPhase spatialSelectors
  ring

 theorem latticePhaseField_gammaNorm_eq (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : Fin d × Fin J → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M)
    (hη : ∀ qi, 0 < η qi) (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (hγ : ∀ q i, 0 < γ q i) (hγ1 : ∀ q i, γ q i ≤ 1 / 4)
    (p0 r0 h Au Av L : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hL : 0 ≤ L)
    (outer bump : (Fin d → ℝ) → ℝ) (ho : Continuous outer) (hbc : Continuous bump)
    (hbump : ∀ x, |bump x| ≤ 1) (ho0 : ∀ x, 0 ≤ outer x) (ho1 : ∀ x, outer x ≤ 1)
    (hp : 0 ≤ p0 ∧ p0 ≤ L) (hh : 0 ≤ h) (hrlo : 0 ≤ r0 - h) (hrhi : r0 + h ≤ L) (j : ℕ) :
    (latticePhaseField U Q M γ η lam p0 r0 h outer bump).gammaNorm
      (gatePrior Q M η hQ hM hη hband) ((cubeUniform d).prod (Measure.count : Measure Bool)) Au Av M j =
      ∫ xs, ordinarySignedGamma (j := j) U Q M γ η lam hQ hM hη hband Au Av bump
        (fun (_ : Fin (j + 2) → Bool) (_ : Fin j) => centeredZero p0 r0 outer)
        (fun (labels : Fin (j + 2) → Bool) (k : Fin j) => centeredWave h outer (labels k.succ.succ)) xs ^ 2
        ∂Measure.pi (fun _ : Fin (j + 2) => (cubeUniform d).prod (Measure.count : Measure Bool)) := by
  unfold AffinePhaseField.gammaNorm labeledNormSquared
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro xs
  dsimp only
  rw [latticePhaseField_leading_mixture U Q M γ η lam hQ hM hη hband hγ hγ1 p0 r0 h Au Av L
    hAu hAu1 hAv hAv1 hL outer bump ho hbc hbump ho0 ho1 hp hh hrlo hrhi j xs]

end RoughRegime.LatticePriors
