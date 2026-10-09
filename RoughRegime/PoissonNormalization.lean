module

public import RoughRegime.PoissonPairProducts


@[expose] public section
/-! Actual field and measure normalization for a two-block pair. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X : Type*}

def AffinePhaseField.scale (F : AffinePhaseField H X) (a : ℝ) : AffinePhaseField H X :=
  ⟨fun h x => a * F.c h x, fun h x => a * F.a h x, fun h x => a * F.b h x,
    fun h x => a * F.hu h x, fun h x => a * F.hv h x⟩

theorem AffinePhaseField.unsigned_scale (F : AffinePhaseField H X) (a Au Av : ℝ)
    (l : Fin 3) (q : H × ℝ) (x : X) :
    (F.scale a).unsigned Au Av l q x = a * F.unsigned Au Av l q x := by
  unfold AffinePhaseField.unsigned AffinePhaseField.scale
  split_ifs <;> ring

theorem AffinePhaseField.feature_scale (F : AffinePhaseField H X) (a Au Av : ℝ)
    (l : Fin 3) (q : PhaseParameter H) (x : X) :
    (F.scale a).feature Au Av l q x = a * F.feature Au Av l q x := by
  simp only [AffinePhaseField.feature, F.unsigned_scale]
  ring

theorem AffinePhaseField.tensor_scale (F : AffinePhaseField H X) (a Au Av : ℝ)
    (k : ℕ) (labels : Fin k → Fin 3) (q : PhaseParameter H) (xs : Fin k → X) :
    labeledTensor ((F.scale a).feature Au Av) k labels q xs =
      a ^ k * labeledTensor (F.feature Au Av) k labels q xs := by
  simp only [labeledTensor, F.feature_scale, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

variable [MeasurableSpace H] [MeasurableSpace X]
variable (ν : Measure H) (μ : Measure X)

theorem AffinePhaseField.gammaNorm_scale (F : AffinePhaseField H X) (a Au Av : ℝ) (M j : ℕ) :
    (F.scale a).gammaNorm ν μ Au Av M j = a ^ (2 * (j + 2)) * F.gammaNorm ν μ Au Av M j := by
  unfold AffinePhaseField.gammaNorm labeledNormSquared labeledMixture
  simp_rw [F.tensor_scale]
  simp_rw [show ∀ q xs, phaseDifference M q * (a ^ (j + 2) *
      labeledTensor (F.feature Au Av) (j + 2) (leadingLabels j) q xs) =
      a ^ (j + 2) * (phaseDifference M q *
      labeledTensor (F.feature Au Av) (j + 2) (leadingLabels j) q xs) by intros; ring]
  simp_rw [integral_const_mul, mul_pow]
  rw [integral_const_mul]
  congr 1
  rw [← pow_mul, Nat.mul_comm]

theorem AffinePhaseField.scale_isMeasurable (F : AffinePhaseField H X) (hm : F.IsMeasurable) (a : ℝ) :
    (F.scale a).IsMeasurable := ⟨hm.c.const_mul a, hm.a.const_mul a,
      hm.b.const_mul a, hm.hu.const_mul a, hm.hv.const_mul a⟩

omit [MeasurableSpace H] [MeasurableSpace X] in
theorem AffinePhaseField.scale_bounded (F : AffinePhaseField H X) (a C : ℝ)
    (hb : F.Bounded C) : (F.scale a).Bounded (|a| * C) := by
  constructor
  all_goals intro h x; change |a * _| ≤ |a| * C; rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hb.c h x) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hb.a h x) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hb.b h x) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hb.hu h x) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hb.hv h x) (abs_nonneg a)

variable [SigmaFinite μ]

theorem pi_two_smul (k : ℕ) : Measure.pi (fun _ : Fin k => (2 : ENNReal) • μ) =
    (2 : ENNReal) ^ k • Measure.pi (fun _ : Fin k => μ) := by
  have : SigmaFinite ((2 : ENNReal) • μ) := by
    change SigmaFinite ((2 : ℝ≥0) • μ)
    infer_instance
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem AffinePhaseField.gammaNorm_two_smul (F : AffinePhaseField H X) (Au Av : ℝ) (M j : ℕ) :
    F.gammaNorm ν ((2 : ENNReal) • μ) Au Av M j = (2 : ℝ) ^ (j + 2) * F.gammaNorm ν μ Au Av M j := by
  unfold AffinePhaseField.gammaNorm labeledNormSquared
  rw [pi_two_smul, integral_smul_measure]
  simp

theorem AffinePhaseField.gammaNorm_normalized_le_physical (F : AffinePhaseField H X)
    (a A Au Av : ℝ) (hA : 0 ≤ A) (ha : a ^ 2 ≤ A) (M j : ℕ) :
    (F.scale a).gammaNorm ν μ Au Av M j ≤ A ^ (j + 2) *
      F.gammaNorm ν ((2 : ENNReal) • μ) Au Av M j := by
  rw [F.gammaNorm_scale, F.gammaNorm_two_smul ν μ Au Av M j]
  have hg := F.gammaNorm_nonneg ν μ Au Av M j
  have hpow : a ^ (2 * (j + 2)) ≤ A ^ (j + 2) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg a) ha _
  have htwo : (1 : ℝ) ≤ 2 ^ (j + 2) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ A ^ (j + 2) * F.gammaNorm ν μ Au Av M j := mul_le_mul_of_nonneg_right hpow hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith : F.gammaNorm ν μ Au Av M j ≤
      2 ^ (j + 2) * F.gammaNorm ν μ Au Av M j) (pow_nonneg hA _)

variable [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem AffinePhaseField.physical_gammaSeries_summable (F : AffinePhaseField H X)
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C) (hb : F.Bounded C)
    (M : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    Summable (fun j => z ^ j / j.factorial * F.gammaNorm ν ((2 : ENNReal) • μ) Au Av M j) := by
  have hs := (F.gammaSeries_summable ν μ Au Av C hAu hAv hC hb M (2 * z) (by positivity)).mul_left 4
  convert hs using 1
  ext j
  rw [F.gammaNorm_two_smul ν μ Au Av M j, pow_add, mul_pow]
  ring

end RoughRegime.PoissonMeasure
