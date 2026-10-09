module

public import RoughRegime.PoissonPhase
public import RoughRegime.MarkedGamma


@[expose] public section
/-! The literal signed-prior likelihood coefficient is the reduced lattice
coefficient used in the spatial norm estimates. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RoughRegime.PoissonMeasure
open RoughRegime.LatticePriors RoughRegime.LatticeFourier RoughRegime.Lattice
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] {j : ℕ}

 def signedLatticeGamma (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (Au Av bx byy : ℝ) : ℝ :=
  (∫ q : PhaseParameter (ι → ℤ),
    (Au * Lower.sign q.2.1 * jointGate Q M η lam q.1.1 * bx) *
    (Av * Lower.sign q.2.2 * jointGate Q M η lam q.1.1 * byy) *
    ∏ k, phasedAngular (c k) (w k) (observationPhase M s q.1.1 k) q.1.2
    ∂(phasePrior (gatePrior Q M η hQ hM hη hband) M 1 (by norm_num)).measure) -
  (∫ q : PhaseParameter (ι → ℤ),
    (Au * Lower.sign q.2.1 * jointGate Q M η lam q.1.1 * bx) *
    (Av * Lower.sign q.2.2 * jointGate Q M η lam q.1.1 * byy) *
    ∏ k, phasedAngular (c k) (w k) (observationPhase M s q.1.1 k) q.1.2
    ∂(phasePrior (gatePrior Q M η hQ hM hη hband) M (-1) (by norm_num)).measure)

 theorem signedLatticeGamma_eq (Q M : ℕ) (η lam : ι → ℝ)
    (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ i, 0 < η i)
    (hband : ∀ i, 4 * (6 * Q / η i) ≤ (M : ℝ))
    (s : Fin j → ι → ℝ) (c w : Fin j → ℝ) (Au Av bx byy : ℝ) :
    signedLatticeGamma Q M η lam hQ hM hη hband s c w Au Av bx byy =
      Au * Av * bx * byy * latticeGamma Q M η lam hQ hM hη hband s c w := by
  let ν := gatePrior Q M η hQ hM hη hband
  let f := fun p : (ι → ℤ) × ℝ => jointGate Q M η lam p.1 ^ 2 *
    ∏ k, phasedAngular (c k) (w k) (observationPhase M s p.1 k) p.2
  let C := ∏ k, (|c k| + 2 * |w k|)
  have hs (k : Fin j) : Measurable (fun z : ι → ℤ => observationPhase M s z k) :=
    measurable_of_countable _
  have hg : Measurable (fun z : ι → ℤ => jointGate Q M η lam z) := measurable_of_countable _
  have hm : Measurable f := by
    unfold f phasedAngular
    apply ((hg.comp measurable_fst).pow_const 2).mul
    apply Finset.measurable_prod
    intro k _
    fun_prop
  have hb : ∀ p, |f p| ≤ C := by
    intro p
    have hp : |∏ k, phasedAngular (c k) (w k) (observationPhase M s p.1 k) p.2| ≤ C := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro k _
      unfold phasedAngular
      calc
        |c k + 2 * w k * Real.cos _| ≤ |c k| + |2 * w k * Real.cos _| := abs_add_le _ _
        _ ≤ |c k| + 2 * |w k| := by
          gcongr
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    have hg' : |jointGate Q M η lam p.1 ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (jointGate_bounds Q M η lam p.1).1 (jointGate_bounds Q M η lam p.1).2
    change |jointGate Q M η lam p.1 ^ 2 * _| ≤ C
    rw [abs_mul]
    exact (mul_le_mul hg' hp (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
  have hC : 0 ≤ C := Finset.prod_nonneg (fun _ _ => by positivity)
  have hd := phasePrior_signed_difference ν M 1 1 f hm C hC hb
  simp only [odd_one, and_self, ite_true, pow_one] at hd
  have hf : Integrable (fun p : (ι → ℤ) × ℝ => Real.cos ((M : ℝ) * p.2) * f p)
      (ν.prod LatticePriors.angleUniform) := by
    apply bounded_integrable _ _ (by fun_prop) C
    intro p
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) (hb p) (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
  rw [integral_prod _ hf] at hd
  have he (q : PhaseParameter (ι → ℤ)) :
      (Au * Lower.sign q.2.1 * jointGate Q M η lam q.1.1 * bx) *
        (Av * Lower.sign q.2.2 * jointGate Q M η lam q.1.1 * byy) *
        ∏ k, phasedAngular (c k) (w k) (observationPhase M s q.1.1 k) q.1.2 =
      (Au * Av * bx * byy) * (Lower.sign q.2.1 * Lower.sign q.2.2 * f q.1) := by
    unfold f
    ring
  unfold signedLatticeGamma
  simp_rw [he]
  rw [integral_const_mul, integral_const_mul, ← mul_sub, hd]
  unfold latticeGamma
  congr 1
  have he' (z : ι → ℤ) : (∫ θ, Real.cos ((M : ℝ) * θ) * f (z, θ)
      ∂LatticePriors.angleUniform) = jointGate Q M η lam z ^ 2 *
      (∫ θ, Real.cos ((M : ℝ) * θ) *
        ∏ k, phasedAngular (c k) (w k) (observationPhase M s z k) θ ∂LatticePriors.angleUniform) := by
    rw [← integral_const_mul]
    congr 1
    funext θ
    unfold f
    ring
  simp_rw [he']
  rfl


variable {J d : ℕ}

/-- The full coefficient with both spatial bump arguments, defined directly
as a difference under genuine sampled phase/sign priors. -/
 def signedMarkedGamma (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : Fin j → (Fin d → ℝ) → ℝ)
    (z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) : ℝ :=
  signedLatticeGamma Q M η lam hQ hM hη hband
    (fun k qi => spatialSelectors U J d j γ z.2 qi k)
    (fun k => c k (z.2 k)) (fun k => w k (z.2 k)) Au Av (bump z.1.1) (bump z.1.2)

 theorem signedMarkedGamma_eq (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : Fin j → (Fin d → ℝ) → ℝ)
    (z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) :
    signedMarkedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z =
      markedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z := by
  unfold signedMarkedGamma markedGamma spatialLatticeGamma
  exact signedLatticeGamma_eq Q M η lam hQ hM hη hband _ _ _ _ _ _ _

 theorem signedMarkedGamma_zero (U : SmoothStep) (Q M : ℕ) (γ : Fin d → Fin J → ℝ)
    (η lam : (Fin d × Fin J) → ℝ) (hQ : 1 ≤ Q) (hM : 0 < M) (hη : ∀ qi, 0 < η qi)
    (hband : ∀ qi, 4 * (6 * Q / η qi) ≤ (M : ℝ))
    (Au Av : ℝ) (bump : (Fin d → ℝ) → ℝ)
    (c w : Fin j → (Fin d → ℝ) → ℝ) (hj : j < M)
    (z : ((Fin d → ℝ) × (Fin d → ℝ)) × (Fin j → Fin d → ℝ)) :
    signedMarkedGamma U Q M γ η lam hQ hM hη hband Au Av bump c w z = 0 := by
  rw [signedMarkedGamma_eq]
  unfold markedGamma spatialLatticeGamma
  rw [latticeGamma_zero Q M η lam hQ hM hη hband _ _ _ hj, mul_zero]

end RoughRegime.PoissonMeasure
