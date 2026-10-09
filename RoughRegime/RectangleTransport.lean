module

public import RoughRegime.DyadicGeometry


@[expose] public section
/-! Exact affine transport of normalized Lebesgue measures on rectangles. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model

def rectangleScale {d : ℕ} (s : Fin d → ℝ) : Covariate d →ₗ[ℝ] Covariate d :=
  Matrix.toEuclideanLin (Matrix.diagonal s)

@[simp] theorem rectangleScale_apply {d : ℕ} (s : Fin d → ℝ) (x : Covariate d) (i : Fin d) :
    rectangleScale s x i = s i * x i := by
  simp [rectangleScale, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    Matrix.diagonal, dotProduct]

theorem rectangleScale_det {d : ℕ} (s : Fin d → ℝ) :
    LinearMap.det (rectangleScale s) = ∏ i, s i := by
  rw [rectangleScale, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin, Matrix.det_diagonal]

def rectangleEmbed {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) (x : Covariate d) : Covariate d :=
  o + rectangleScale s x

def rectangleCoords {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) (x : Covariate d) : Covariate d :=
  rectangleScale (fun i => (s i)⁻¹) (x - o)

def rectangle {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) : Set (Covariate d) :=
  {x | ∀ i, x i ∈ Icc (o i) (o i + s i)}

theorem rectangleEmbed_continuous {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) :
    Continuous (rectangleEmbed o s) :=
  continuous_const.add (rectangleScale s).continuous_of_finiteDimensional

theorem rectangleCoords_continuous {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) :
    Continuous (rectangleCoords o s) :=
  (rectangleScale (fun i => (s i)⁻¹)).continuous_of_finiteDimensional.comp
    (continuous_id.sub continuous_const)

theorem rectangleCoords_embed {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, s i ≠ 0) (x : Covariate d) :
    rectangleCoords o s (rectangleEmbed o s x) = x := by
  ext i
  simp [rectangleCoords, rectangleEmbed, inv_mul_cancel₀ (hs i), ← mul_assoc]

theorem rectangleEmbed_coords {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, s i ≠ 0) (x : Covariate d) :
    rectangleEmbed o s (rectangleCoords o s x) = x := by
  ext i
  simp [rectangleCoords, rectangleEmbed, mul_inv_cancel₀ (hs i), ← mul_assoc]

theorem rectangle_measurable {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) :
    MeasurableSet (rectangle o s) := by
  have he : rectangle o s = WithLp.ofLp ⁻¹' Icc (fun i => o i) (fun i => o i + s i) := by
    ext x
    simp only [rectangle, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [he]
  exact measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem rectangleEmbed_preimage {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) : rectangleEmbed o s ⁻¹' rectangle o s = cube d := by
  ext x
  simp only [mem_preimage, rectangle, cube, mem_ofPred_eq, rectangleEmbed,
    PiLp.add_apply, rectangleScale_apply, mem_Icc]
  constructor
  · intro hx i
    exact ⟨(mul_nonneg_iff_of_pos_left (hs i)).mp (by linarith [(hx i).1]),
      (mul_le_mul_iff_right₀ (hs i)).mp (by nlinarith [(hx i).2])⟩
  · intro hx i
    constructor <;> nlinarith [(hx i).1, (hx i).2, hs i]

theorem rectangleEmbed_map_volume {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) :
    volume.map (rectangleEmbed o s) = ENNReal.ofReal (1 / ∏ i, s i) • volume := by
  have hprod : (0 : ℝ) < ∏ i, s i := Finset.prod_pos (fun i _ => hs i)
  have hdet : LinearMap.det (rectangleScale s) ≠ 0 := by rw [rectangleScale_det]; exact hprod.ne'
  have ht : Measurable (fun x : Covariate d => o + x) :=
    (continuous_const.add continuous_id).measurable
  have hm : Measurable (rectangleScale s) := (rectangleScale s).continuous_of_finiteDimensional.measurable
  have he : rectangleEmbed o s = (fun x => o + x) ∘ rectangleScale s := rfl
  rw [he, ← Measure.map_map ht hm,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
    Measure.map_smul _ ht.aemeasurable,
    (measurePreserving_add_left volume o).map_eq]
  rw [rectangleScale_det, abs_of_pos (inv_pos.mpr hprod)]
  simp only [one_div]

theorem rectangleEmbed_map_cubeVolume {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) :
    (cubeVolume d).map (rectangleEmbed o s) =
      ENNReal.ofReal (1 / ∏ i, s i) • volume.restrict (rectangle o s) := by
  have h := Measure.restrict_map (μ := (volume : Measure (Covariate d)))
    (rectangleEmbed_continuous o s).measurable (rectangle_measurable o s)
  rw [rectangleEmbed_map_volume o s hs, rectangleEmbed_preimage o s hs,
    Measure.restrict_smul] at h
  exact h.symm

def rectangleVolume {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) : Measure (Covariate d) :=
  ENNReal.ofReal (1 / ∏ i, s i) • volume.restrict (rectangle o s)

theorem rectangleEmbed_preserving {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) :
    MeasurePreserving (rectangleEmbed o s) (cubeVolume d) (rectangleVolume o s) :=
  ⟨(rectangleEmbed_continuous o s).measurable, rectangleEmbed_map_cubeVolume o s hs⟩

theorem rectangleCoords_preserving {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) :
    MeasurePreserving (rectangleCoords o s) (rectangleVolume o s) (cubeVolume d) := by
  refine ⟨(rectangleCoords_continuous o s).measurable, ?_⟩
  unfold rectangleVolume
  rw [← rectangleEmbed_map_cubeVolume o s hs]
  rw [Measure.map_map (rectangleCoords_continuous o s).measurable
    (rectangleEmbed_continuous o s).measurable]
  have he : rectangleCoords o s ∘ rectangleEmbed o s = id :=
    funext (rectangleCoords_embed o s (fun i => (hs i).ne'))
  rw [he, Measure.map_id]

theorem rectangleCoords_mem_cube {d : ℕ} (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) (x : Covariate d) (hx : x ∈ rectangle o s) :
    rectangleCoords o s x ∈ cube d := by
  have he := rectangleEmbed_preimage o s hs
  rw [← he]
  simpa only [mem_preimage, rectangleEmbed_coords o s (fun i => (hs i).ne')] using hx

def rectangleLpTransport {d : ℕ} (o : Covariate d) (s : Fin d → ℝ) (hs : ∀ i, 0 < s i) :
    Lp ℝ 2 (cubeVolume d) →ₗᵢ[ℝ] Lp ℝ 2 (rectangleVolume o s) :=
  Lp.compMeasurePreservingₗᵢ ℝ (rectangleCoords o s) (rectangleCoords_preserving o s hs)

def rectangleBasis {d : ℕ} (k : ℕ) (o : Covariate d) (s : Fin d → ℝ)
    (hs : ∀ i, 0 < s i) (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    Lp ℝ 2 (rectangleVolume o s) :=
  rectangleLpTransport o s hs (polynomialToLp d (basisPolynomial d k i))

theorem rectangleBasis_orthonormal {d : ℕ} (k : ℕ) (o : Covariate d)
    (s : Fin d → ℝ) (hs : ∀ i, 0 < s i) : Orthonormal ℝ (rectangleBasis k o s hs) := by
  exact (rectangleLpTransport o s hs).orthonormal_comp_iff.mpr (basisPolynomial_orthonormal d k)

theorem rectangleBasis_uniform_bound {d : ℕ} (k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (o : Covariate d) (s : Fin d → ℝ),
      (∀ i, 0 < s i) → ∀ i x, x ∈ rectangle o s →
        |polynomialEvaluation (basisPolynomial d k i) (rectangleCoords o s x)| ≤ B := by
  obtain ⟨B, hB, hb⟩ := basisPolynomial_uniform_bound d k
  exact ⟨B, hB, fun o s hs i x hx => hb i _ (rectangleCoords_mem_cube o s hs x hx)⟩

end RoughRegime.Model
