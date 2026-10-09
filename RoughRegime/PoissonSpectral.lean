module

public import RoughRegime.PoissonProcess
public import RoughRegime.ModeExpansion


@[expose] public section
/-! Actual continuous-angle low-degree coefficient cancellation in Lemma 11. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [MeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν]

theorem affine_factor_bound (c a b θ C : ℝ)
    (hC : 0 ≤ C) (hc : |c| ≤ C) (ha : |a| ≤ C) (hb : |b| ≤ C) :
    |c + a * Real.cos θ + b * Real.sin θ| ≤ 3 * C := by
  have hca := abs_add_le c (a * Real.cos θ)
  have hab := abs_add_le (c + a * Real.cos θ) (b * Real.sin θ)
  have ha' : |a * Real.cos θ| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul ha (Real.abs_cos_le_one θ) (abs_nonneg _) hC).trans_eq (mul_one C)
  have hb' : |b * Real.sin θ| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul hb (Real.abs_sin_le_one θ) (abs_nonneg _) hC).trans_eq (mul_one C)
  linarith

/-- The low-degree cancellation holds under an arbitrary independent latent
prior, using the actual normalized Lebesgue angle distribution. -/
theorem latent_affine_angular_zero (j M : ℕ) (hj : j < M)
    (w : H → ℝ) (c a b : Fin j → H → ℝ)
    (hw : Measurable w) (hc : ∀ i, Measurable (c i))
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbw : ∀ h, |w h| ≤ A) (hbc : ∀ i h, |c i h| ≤ C)
    (hba : ∀ i h, |a i h| ≤ C) (hbb : ∀ i h, |b i h| ≤ C) :
    (∫ q : H × ℝ, w q.1 * Real.cos ((M : ℝ) * q.2) *
      ∏ i, (c i q.1 + a i q.1 * Real.cos q.2 + b i q.1 * Real.sin q.2)
      ∂ν.prod LatticePriors.angleUniform) = 0 := by
  let f := fun q : H × ℝ => w q.1 * Real.cos ((M : ℝ) * q.2) *
    ∏ i, (c i q.1 + a i q.1 * Real.cos q.2 + b i q.1 * Real.sin q.2)
  have hm : Measurable f := by
    apply (((hw.comp measurable_fst).mul
      ((measurable_snd.const_mul (M : ℝ)).cos))).mul
    apply Finset.measurable_prod
    intro i _
    exact ((hc i).comp measurable_fst).add
      (((ha i).comp measurable_fst).mul measurable_snd.cos) |>.add
        (((hb i).comp measurable_fst).mul measurable_snd.sin)
  have hf : ∀ q : H × ℝ, |f q| ≤ A * (3 * C) ^ j := by
    rintro ⟨h, θ⟩
    have hp : |∏ i, (c i h + a i h * Real.cos θ + b i h * Real.sin θ)| ≤ (3 * C) ^ j := by
      rw [Finset.abs_prod]
      have h := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i : Fin j => |c i h + a i h * Real.cos θ + b i h * Real.sin θ|)
        (g := fun _ => 3 * C) (fun _ _ => abs_nonneg _)
        (fun i _ => affine_factor_bound _ _ _ _ C hC (hbc i h) (hba i h) (hbb i h))
      simpa using h
    have hw' : |w h * Real.cos ((M : ℝ) * θ)| ≤ A := by
      rw [abs_mul]
      exact (mul_le_mul (hbw h) (Real.abs_cos_le_one _) (abs_nonneg _) hA).trans_eq (mul_one A)
    dsimp [f]
    rw [abs_mul]
    exact mul_le_mul hw' hp (abs_nonneg _) hA
  have hi : Integrable f (ν.prod LatticePriors.angleUniform) :=
    bounded_integrable _ f hm (A * (3 * C) ^ j) hf
  change (∫ q, f q ∂ν.prod LatticePriors.angleUniform) = 0
  rw [integral_prod f hi]
  have hz (h : H) : (∫ θ, w h * Real.cos ((M : ℝ) * θ) *
      ∏ i, (c i h + a i h * Real.cos θ + b i h * Real.sin θ)
      ∂LatticePriors.angleUniform) = 0 := by
    have he : (fun θ => w h * Real.cos ((M : ℝ) * θ) *
        ∏ i, (c i h + a i h * Real.cos θ + b i h * Real.sin θ)) =
        fun θ => w h * (Real.cos ((M : ℝ) * θ) *
          ∏ i, (c i h + a i h * Real.cos θ + b i h * Real.sin θ)) := by
      funext θ
      ring
    rw [he, integral_const_mul,
      LatticePriors.integral_cos_affine_product_zero j M (fun i => c i h) (fun i => a i h)
        (fun i => b i h) hj, mul_zero]
  change (∫ h, ∫ θ, f (h, θ) ∂LatticePriors.angleUniform ∂ν) = 0
  simp only [f, hz, integral_zero]


/-- The same actual angular cancellation for any finite index type, including
subsets selected by a likelihood labeling. -/
theorem latent_affine_angular_zero_fintype {ι : Type*} [Fintype ι]
    (M : ℕ) (hj : Fintype.card ι < M)
    (w : H → ℝ) (c a b : ι → H → ℝ)
    (hw : Measurable w) (hc : ∀ i, Measurable (c i))
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbw : ∀ h, |w h| ≤ A) (hbc : ∀ i h, |c i h| ≤ C)
    (hba : ∀ i h, |a i h| ≤ C) (hbb : ∀ i h, |b i h| ≤ C) :
    (∫ q : H × ℝ, w q.1 * Real.cos ((M : ℝ) * q.2) *
      ∏ i : ι, (c i q.1 + a i q.1 * Real.cos q.2 + b i q.1 * Real.sin q.2)
      ∂ν.prod LatticePriors.angleUniform) = 0 := by
  let E := (Fintype.equivFin ι).symm
  have hp (q : H × ℝ) : (∏ i : ι, (c i q.1 + a i q.1 * Real.cos q.2 + b i q.1 * Real.sin q.2)) =
      ∏ i : Fin (Fintype.card ι), (c (E i) q.1 + a (E i) q.1 * Real.cos q.2 + b (E i) q.1 * Real.sin q.2) :=
    (E.prod_comp _).symm
  simp_rw [hp]
  exact latent_affine_angular_zero ν (Fintype.card ι) M hj w (fun i => c (E i))
    (fun i => a (E i)) (fun i => b (E i)) hw (fun i => hc (E i)) (fun i => ha (E i))
    (fun i => hb (E i)) A C hA hC hbw (fun i => hbc (E i)) (fun i => hba (E i)) (fun i => hbb (E i))

end RoughRegime.PoissonMeasure
