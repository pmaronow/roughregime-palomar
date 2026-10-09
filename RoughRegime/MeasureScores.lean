module

public import RoughRegime.Model


@[expose] public section
/-! Actual bounded scores from the inverse residual covariance. The construction
uses integrals under the baseline probability measure, including non-finite spaces. -/

noncomputable section
open MeasureTheory

namespace RoughRegime.MeasureScores

variable {Z : Type*} [MeasurableSpace Z] (π : Measure Z)

def uu (r : Z → ℝ) : ℝ := ∫ z, r z ^ 2 ∂π
def uv (r s : Z → ℝ) : ℝ := ∫ z, r z * s z ∂π
def det (r s : Z → ℝ) : ℝ := uu π r * uu π s - uv π r s ^ 2

def scoreU (r s : Z → ℝ) (z : Z) : ℝ :=
  (uu π s * r z - uv π r s * s z) / det π r s
def scoreV (r s : Z → ℝ) (z : Z) : ℝ :=
  (uu π r * s z - uv π r s * r z) / det π r s

lemma bounded_integrable [IsProbabilityMeasure π] (r : Z → ℝ) (hr : Measurable r) (C : ℝ)
    (hbound : ∀ z, |r z| ≤ C) : Integrable r π := by
  apply Integrable.of_bound hr.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hbound z

lemma product_integrable [IsProbabilityMeasure π] (r s : Z → ℝ) (hr : Measurable r) (hs : Measurable s)
    (C : ℝ) (hC : 0 ≤ C) (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C) :
    Integrable (fun z => r z * s z) π := by
  apply bounded_integrable π _ (hr.mul hs) (C * C)
  intro z
  change |r z * s z| ≤ C * C
  rw [abs_mul]
  exact mul_le_mul (hbr z) (hbs z) (abs_nonneg _) hC

lemma square_integrable [IsProbabilityMeasure π] (r : Z → ℝ) (hr : Measurable r) (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ z, |r z| ≤ C) : Integrable (fun z => r z ^ 2) π := by
  simpa only [pow_two] using product_integrable π r r hr hr C hC hbr hbr

lemma scoreU_measurable (r s : Z → ℝ) (hr : Measurable r) (hs : Measurable s) :
    Measurable (scoreU π r s) :=
  ((hr.const_mul _).sub (hs.const_mul _)).div_const _

lemma scoreV_measurable (r s : Z → ℝ) (hr : Measurable r) (hs : Measurable s) :
    Measurable (scoreV π r s) :=
  ((hs.const_mul _).sub (hr.const_mul _)).div_const _

def scoreBound (r s : Z → ℝ) (C : ℝ) : ℝ :=
  ((|uu π r| + |uu π s| + |uv π r s|) * C) / |det π r s|

lemma scoreBound_nonneg (r s : Z → ℝ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ scoreBound π r s C := by unfold scoreBound; positivity

lemma scoreU_bound (r s : Z → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C) (z : Z) :
    |scoreU π r s z| ≤ scoreBound π r s C := by
  unfold scoreU scoreBound
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc
    |uu π s * r z - uv π r s * s z| ≤ |uu π s * r z| + |uv π r s * s z| := abs_sub _ _
    _ = |uu π s| * |r z| + |uv π r s| * |s z| := by rw [abs_mul, abs_mul]
    _ ≤ |uu π s| * C + |uv π r s| * C :=
      add_le_add (mul_le_mul_of_nonneg_left (hbr z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hbs z) (abs_nonneg _))
    _ ≤ (|uu π r| + |uu π s| + |uv π r s|) * C := by
      nlinarith [abs_nonneg (uu π r)]

lemma scoreV_bound (r s : Z → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C) (z : Z) :
    |scoreV π r s z| ≤ scoreBound π r s C := by
  unfold scoreV scoreBound
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc
    |uu π r * s z - uv π r s * r z| ≤ |uu π r * s z| + |uv π r s * r z| := abs_sub _ _
    _ = |uu π r| * |s z| + |uv π r s| * |r z| := by rw [abs_mul, abs_mul]
    _ ≤ |uu π r| * C + |uv π r s| * C :=
      add_le_add (mul_le_mul_of_nonneg_left (hbs z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hbr z) (abs_nonneg _))
    _ ≤ (|uu π r| + |uu π s| + |uv π r s|) * C := by
      nlinarith [abs_nonneg (uu π s)]

lemma scoreU_integrable [IsProbabilityMeasure π] (r s : Z → ℝ) (hr : Measurable r) (hs : Measurable s)
    (C : ℝ) (hC : 0 ≤ C) (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C) :
    Integrable (scoreU π r s) π :=
  bounded_integrable π _ (scoreU_measurable π r s hr hs) _ (scoreU_bound π r s C hC hbr hbs)

lemma scoreV_integrable [IsProbabilityMeasure π] (r s : Z → ℝ) (hr : Measurable r) (hs : Measurable s)
    (C : ℝ) (hC : 0 ≤ C) (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C) :
    Integrable (scoreV π r s) π :=
  bounded_integrable π _ (scoreV_measurable π r s hr hs) _ (scoreV_bound π r s C hC hbr hbs)

lemma score_mean_zero (r s : Z → ℝ) (hr : Integrable r π) (hs : Integrable s π)
    (hmr : (∫ z, r z ∂π) = 0) (hms : (∫ z, s z ∂π) = 0) :
    (∫ z, scoreU π r s z ∂π) = 0 ∧ (∫ z, scoreV π r s z ∂π) = 0 := by
  constructor
  · unfold scoreU
    rw [integral_div, integral_sub (hr.const_mul _) (hs.const_mul _),
      integral_const_mul, integral_const_mul, hmr, hms]
    simp
  · unfold scoreV
    rw [integral_div, integral_sub (hs.const_mul _) (hr.const_mul _),
      integral_const_mul, integral_const_mul, hmr, hms]
    simp

lemma cross_integralU (r s t : Z → ℝ) (htr : Integrable (fun z => t z * r z) π)
    (hts : Integrable (fun z => t z * s z) π) :
    (∫ z, t z * scoreU π r s z ∂π) =
      (uu π s * (∫ z, t z * r z ∂π) - uv π r s * (∫ z, t z * s z ∂π)) / det π r s := by
  have he : (fun z => t z * scoreU π r s z) =
      (fun z => (uu π s * (t z * r z) - uv π r s * (t z * s z)) / det π r s) := by
    funext z
    unfold scoreU
    ring
  rw [he, integral_div, integral_sub (htr.const_mul _) (hts.const_mul _),
    integral_const_mul, integral_const_mul]

lemma cross_integralV (r s t : Z → ℝ) (htr : Integrable (fun z => t z * r z) π)
    (hts : Integrable (fun z => t z * s z) π) :
    (∫ z, t z * scoreV π r s z ∂π) =
      (uu π r * (∫ z, t z * s z ∂π) - uv π r s * (∫ z, t z * r z ∂π)) / det π r s := by
  have he : (fun z => t z * scoreV π r s z) =
      (fun z => (uu π r * (t z * s z) - uv π r s * (t z * r z)) / det π r s) := by
    funext z
    unfold scoreV
    ring
  rw [he, integral_div, integral_sub (hts.const_mul _) (htr.const_mul _),
    integral_const_mul, integral_const_mul]

theorem score_cross_moments (r s : Z → ℝ)
    (hrr : Integrable (fun z => r z ^ 2) π)
    (hrs : Integrable (fun z => r z * s z) π)
    (hss : Integrable (fun z => s z ^ 2) π) (hdet : det π r s ≠ 0) :
    (∫ z, r z * scoreU π r s z ∂π) = 1 ∧
    (∫ z, s z * scoreU π r s z ∂π) = 0 ∧
    (∫ z, r z * scoreV π r s z ∂π) = 0 ∧
    (∫ z, s z * scoreV π r s z ∂π) = 1 := by
  have hrr' : Integrable (fun z => r z * r z) π := by simpa [pow_two] using hrr
  have hss' : Integrable (fun z => s z * s z) π := by simpa [pow_two] using hss
  have hsr : Integrable (fun z => s z * r z) π := by simpa [mul_comm] using hrs
  have hrri : (∫ z, r z * r z ∂π) = uu π r := by simp [uu, pow_two]
  have hssi : (∫ z, s z * s z ∂π) = uu π s := by simp [uu, pow_two]
  have hsri : (∫ z, s z * r z ∂π) = uv π r s := by simp [uv, mul_comm]
  rw [cross_integralU π r s r hrr' hrs, cross_integralU π r s s hsr hss',
    cross_integralV π r s r hrr' hrs, cross_integralV π r s s hsr hss',
    hrri, hssi, hsri]
  change (uu π s * uu π r - uv π r s * uv π r s) / det π r s = 1 ∧
    (uu π s * uv π r s - uv π r s * uu π s) / det π r s = 0 ∧
    (uu π r * uv π r s - uv π r s * uu π r) / det π r s = 0 ∧
    (uu π r * uu π s - uv π r s * uv π r s) / det π r s = 1
  constructor
  · apply (div_eq_one_iff_eq hdet).mpr
    unfold det
    ring
  constructor
  · simp [mul_comm]
  constructor
  · simp [mul_comm]
  · apply (div_eq_one_iff_eq hdet).mpr
    unfold det
    ring

theorem exists_bounded_scores [IsProbabilityMeasure π] (r s : Z → ℝ)
    (hr : Measurable r) (hs : Measurable s) (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ z, |r z| ≤ C) (hbs : ∀ z, |s z| ≤ C)
    (hmr : (∫ z, r z ∂π) = 0) (hms : (∫ z, s z ∂π) = 0)
    (hdet : det π r s ≠ 0) :
    ∃ su sv : Z → ℝ, ∃ B : ℝ,
      Measurable su ∧ Measurable sv ∧ 0 ≤ B ∧
      (∀ z, |su z| ≤ B) ∧ (∀ z, |sv z| ≤ B) ∧
      (∫ z, su z ∂π) = 0 ∧ (∫ z, sv z ∂π) = 0 ∧
      (∫ z, r z * su z ∂π) = 1 ∧ (∫ z, s z * su z ∂π) = 0 ∧
      (∫ z, r z * sv z ∂π) = 0 ∧ (∫ z, s z * sv z ∂π) = 1 := by
  have hmean := score_mean_zero π r s
    (bounded_integrable π r hr C hbr) (bounded_integrable π s hs C hbs) hmr hms
  have hcross := score_cross_moments π r s
    (square_integrable π r hr C hC hbr) (product_integrable π r s hr hs C hC hbr hbs)
    (square_integrable π s hs C hC hbs) hdet
  exact ⟨scoreU π r s, scoreV π r s, scoreBound π r s C,
    scoreU_measurable π r s hr hs, scoreV_measurable π r s hr hs,
    scoreBound_nonneg π r s C hC, scoreU_bound π r s C hC hbr hbs,
    scoreV_bound π r s C hC hbr hbs, hmean.1, hmean.2,
    hcross.1, hcross.2.1, hcross.2.2.1, hcross.2.2.2⟩

theorem exists_bounded_diagonal_score [IsProbabilityMeasure π] (r : Z → ℝ)
    (hr : Measurable r) (C : ℝ) (hC : 0 ≤ C) (hbr : ∀ z, |r z| ≤ C)
    (hmr : (∫ z, r z ∂π) = 0) (hvar : uu π r ≠ 0) :
    ∃ s : Z → ℝ, ∃ B : ℝ, Measurable s ∧ 0 ≤ B ∧ (∀ z, |s z| ≤ B) ∧
      (∫ z, s z ∂π) = 0 ∧ (∫ z, r z * s z ∂π) = 1 := by
  refine ⟨fun z => r z / uu π r, C / |uu π r|, hr.div_const _,
    div_nonneg hC (abs_nonneg _), ?_, ?_, ?_⟩
  · intro z
    rw [abs_div]
    exact div_le_div_of_nonneg_right (hbr z) (abs_nonneg _)
  · rw [integral_div, hmr, zero_div]
  · have he : (fun z => r z * (r z / uu π r)) = (fun z => r z ^ 2 / uu π r) := by
      funext z
      ring
    rw [he, integral_div]
    exact div_self hvar

end RoughRegime.MeasureScores
