module

public import RoughRegime.DyadicTransport


@[expose] public section
/-! Genuine Hölder approximation on the paper's dyadic cells. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

theorem rectangleVolume_probability {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) : IsProbabilityMeasure (rectangleVolume o s) := by
  unfold rectangleVolume
  rw [← rectangleEmbed_map_cubeVolume o s hs]
  infer_instance

theorem ae_rectangleVolume_mem {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) :
    ∀ᵐ x ∂rectangleVolume o s, x ∈ rectangle o s :=
  Measure.ae_smul_measure (ae_restrict_mem (rectangle_measurable o s)) _

theorem dyadicOrigin_mem_rectangle {d j : ℕ} (c : DyadicCell d j) :
    dyadicOrigin c ∈ dyadicRectangle c := by
  intro i
  simp only [dyadicOrigin, WithLp.ofLp_toLp, mem_Icc]
  exact ⟨le_rfl, div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)⟩

theorem dyadic_holder_polynomial_error {d : ℕ} (hd : 0 < d) (t H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (c : DyadicCell d j) (f : Covariate d → ℝ),
      f ∈ holderBall t H → ∀ x ∈ dyadicRectangle c,
      |f x - polynomialEvaluation (holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)) x| ≤
        C * ((2 : ℝ) ^ (-(j : ℝ) / d)) ^ t := by
  let A : ℝ := (d : ℝ) ^ holderOrder t * H / (holderOrder t).factorial
  have hA : 0 ≤ A := by unfold A; positivity
  refine ⟨1 + A * (2 * Real.sqrt d) ^ t, by positivity, ?_⟩
  intro j c f hf x hx
  have ht := (holderBall_regular f t H hf).1
  have ho := dyadicOrigin_mem_rectangle c
  have he := holderTaylorPolynomial_error f t H hH hf (dyadicOrigin c) x
    (dyadicRectangle_subset_cube c ho) (dyadicRectangle_subset_cube c hx)
  have hdiam := dyadicRectangle_diameter hd c x (dyadicOrigin c) hx ho
  calc
    _ ≤ A * ‖x - dyadicOrigin c‖ ^ t := he
    _ ≤ A * (2 * Real.sqrt d * (2 : ℝ) ^ (-(j : ℝ) / d)) ^ t :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdiam ht.le) hA
    _ = (A * (2 * Real.sqrt d) ^ t) * ((2 : ℝ) ^ (-(j : ℝ) / d)) ^ t := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ _ := by gcongr; linarith

theorem holderFunction_memLp_dyadic {d j : ℕ} (c : DyadicCell d j) (f : Covariate d → ℝ)
    (t H : ℝ) (hH : 0 ≤ H) (hf : f ∈ holderBall t H) :
    MemLp f 2 (rectangleVolume (dyadicOrigin c) (dyadicSides c)) := by
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  have hc := (holderBall_regular f t H hf).2.continuousOn.mono (dyadicRectangle_subset_cube c)
  have hm : AEStronglyMeasurable f (rectangleVolume (dyadicOrigin c) (dyadicSides c)) := by
    apply AEStronglyMeasurable.smul_measure
    apply ContinuousOn.aestronglyMeasurable
    · exact hc.mono (by rw [← dyadicRectangle_eq_rectangle])
    · exact rectangle_measurable _ _
  apply MemLp.of_bound hm H
  filter_upwards [ae_rectangleVolume_mem (dyadicOrigin c) (dyadicSides c)] with x hx
  rw [Real.norm_eq_abs]
  exact holderNorm_bounds_values f t H hH hf x (dyadicRectangle_subset_cube c (by
    rwa [dyadicRectangle_eq_rectangle]))

def dyadicPolynomialLp {d j : ℕ} (c : DyadicCell d j) (p : MvPolynomial (Fin d) ℝ) :
    Lp ℝ 2 (rectangleVolume (dyadicOrigin c) (dyadicSides c)) :=
  rectangleLpTransport (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
    (polynomialToLp d (rectangleEmbedPolynomial (dyadicOrigin c) (dyadicSides c) p))

theorem dyadicPolynomialLp_ae {d j : ℕ} (c : DyadicCell d j) (p : MvPolynomial (Fin d) ℝ) :
    dyadicPolynomialLp c p =ᵐ[rectangleVolume (dyadicOrigin c) (dyadicSides c)] polynomialEvaluation p := by
  have hp := rectangleCoords_preserving (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  refine (Lp.coeFn_compMeasurePreserving _ hp).trans ?_
  refine (hp.quasiMeasurePreserving.ae_eq_comp (polynomialToLp_ae _)).trans ?_
  exact Filter.Eventually.of_forall (fun x => by
    simp only [Function.comp_apply]
    rw [rectangleEmbedPolynomial_eval,
      rectangleEmbed_coords _ _ (fun i => (dyadicSides_pos c i).ne')])

theorem dyadic_holder_L2_approximation {d : ℕ} (hd : 0 < d) (t H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (c : DyadicCell d j) (f : Covariate d → ℝ)
      (hf : f ∈ holderBall t H),
      ‖(holderFunction_memLp_dyadic c f t H hH hf).toLp f -
        dyadicPolynomialLp c (holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c))‖ ≤
          C * ((2 : ℝ) ^ (-(j : ℝ) / d)) ^ t := by
  obtain ⟨C, hC, hb⟩ := dyadic_holder_polynomial_error hd t H hH
  refine ⟨C, hC, ?_⟩
  intro j c f hf
  haveI := rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  apply (Lp.norm_le_of_ae_bound (C := C * ((2 : ℝ) ^ (-(j : ℝ) / d)) ^ t)
    (by positivity) ?_).trans_eq (by simp [measureUnivNNReal])
  filter_upwards [(holderFunction_memLp_dyadic c f t H hH hf).coeFn_toLp,
    dyadicPolynomialLp_ae c (holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)),
    Lp.coeFn_sub ((holderFunction_memLp_dyadic c f t H hH hf).toLp f)
      (dyadicPolynomialLp c (holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c))),
    ae_rectangleVolume_mem (dyadicOrigin c) (dyadicSides c)] with x hfval hpval hsub hx
  rw [hsub, Pi.sub_apply, hfval, hpval, Real.norm_eq_abs]
  exact hb j c f hf x (by rwa [dyadicRectangle_eq_rectangle])

end RoughRegime.Model
