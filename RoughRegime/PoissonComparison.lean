module

public import RoughRegime.PhaseNormBounds
public import RoughRegime.PoissonSeriesBounds


@[expose] public section
/-! General-measure affine-phase Poisson comparison with its actual leading
Gamma series and fourth-order remainder. All label selection and norm bounds
are proved from the genuine phase/sign priors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
variable (ν : Measure H) (μ : Measure X) (κ : Measure Z)
variable [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]

 def AffinePhaseField.markedFactor (F : AffinePhaseField H X) (Au Av : ℝ)
    (s : Fin 3 → Z → ℝ) (q : PhaseParameter H) (y : X × Z) : ℝ :=
      ∑ l : Fin 3, F.feature Au Av l q y.1 * s l y.2

 theorem AffinePhaseField.markedFactor_measurable (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av : ℝ) (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) :
    Measurable (Function.uncurry (F.markedFactor Au Av s)) := by
  unfold AffinePhaseField.markedFactor Function.uncurry
  apply Finset.measurable_sum
  intro l _
  exact ((F.feature_measurable hm Au Av l).comp (measurable_fst.prodMk measurable_snd.fst)).mul
    ((hs l).comp measurable_snd.snd)

omit [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z] in
 theorem AffinePhaseField.markedFactor_bound (F : AffinePhaseField H X)
    (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (_hS : 0 ≤ S) (hb : F.Bounded C) (s : Fin 3 → Z → ℝ)
    (hbs : ∀ l z, |s l z| ≤ S) (q : PhaseParameter H) (y : X × Z) :
    |F.markedFactor Au Av s q y| ≤ 9 * C * S := by
  unfold AffinePhaseField.markedFactor
  calc
    _ ≤ ∑ l : Fin 3, |F.feature Au Av l q y.1 * s l y.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, 3 * C * S := Finset.sum_le_sum fun l _ => by
      rw [abs_mul]
      exact mul_le_mul (F.feature_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb l q y.1)
        (hbs l y.2) (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

 theorem AffinePhaseField.tensorNorm_contribution (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S) (M k : ℕ) :
    tensorNormSquared (phaseBase ν) (μ.prod κ) (phaseDifference M) (F.markedFactor Au Av s) k ≤
      (9 * S ^ 2) ^ k * (F.leadingContribution ν μ Au Av M k + remainderContribution Au Av C M k) := by
  have hv : Measurable (phaseDifference (H := H) M) :=
    (phaseDensity_measurable M 1).sub (phaseDensity_measurable M (-1))
  have hi := marked_tensorNormSquared_labelings_le (phaseBase ν) μ κ (phaseDifference M)
    (F.feature Au Av) s hv (F.feature_measurable hm Au Av) hs 2 (3 * C) S (by norm_num)
    (by positivity) hS (phaseDifference_bound M)
    (F.feature_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb) hbs k
  have hj := F.labelingSum_contribution ν μ hm Au Av C hAu hAu1 hAv hAv1 hC hb M k
  have hh := hi.trans (mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ (3 * S ^ 2) ^ k))
  have he : (3 * S ^ 2) ^ k * (3 : ℝ) ^ k = (9 * S ^ 2) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, he] at hh
  exact hh

 theorem AffinePhaseField.poissonSeries_bound (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (M : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    Summable (fun k => z ^ k / k.factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) k) ∧
    (∑' k, z ^ k / k.factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) k) ≤
      (9 * S ^ 2 * z) ^ 2 * (∑' j, if M ≤ j then
        (9 * S ^ 2 * z) ^ j / j.factorial * F.gammaNorm ν μ Au Av M j else 0) +
      4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
        (81 * S ^ 2 * C ^ 2 * z) ^ 4 *
        ((81 * S ^ 2 * C ^ 2 * z) ^ M / M.factorial) * Real.exp (81 * S ^ 2 * C ^ 2 * z) := by
  let z₁ := 9 * S ^ 2 * z
  let z₂ := 81 * S ^ 2 * C ^ 2 * z
  let D := 4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2
  let a := fun k : ℕ => if M + 2 ≤ k then z₁ ^ k / k.factorial * F.gammaNorm ν μ Au Av M (k - 2) else 0
  let b := fun k : ℕ => if M + 4 ≤ k then z₂ ^ k / k.factorial else 0
  have hz₁ : 0 ≤ z₁ := by positivity
  have hz₂ : 0 ≤ z₂ := by positivity
  have hD : 0 ≤ D := by positivity
  have hsa := PoissonSeriesBounds.two_label_tail z₁ hz₁ M (F.gammaNorm ν μ Au Av M)
    (F.gammaNorm_nonneg ν μ Au Av M) (F.gammaSeries_summable ν μ Au Av C hAu hAv hC hb M z₁ hz₁)
  have hsb := PoissonSeriesBounds.fourth_label_tail z₂ hz₂ M
  have hp (k : ℕ) : z ^ k / k.factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) k ≤ a k + D * b k := by
    have hi := mul_le_mul_of_nonneg_left
      (F.tensorNorm_contribution ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs M k)
      (by positivity : 0 ≤ z ^ k / k.factorial)
    calc
      _ ≤ z ^ k / k.factorial * ((9 * S ^ 2) ^ k *
          (F.leadingContribution ν μ Au Av M k + remainderContribution Au Av C M k)) := hi
      _ = a k + D * b k := by
        unfold AffinePhaseField.leadingContribution remainderContribution a b D z₁ z₂
        split_ifs <;> simp only [mul_zero, add_zero, zero_add, mul_pow] <;> ring_nf <;>
          simp only [show (81 : ℝ) ^ k = 9 ^ k * 9 ^ k by rw [← mul_pow]; norm_num] <;> ring
  have hsright : Summable (fun k => a k + D * b k) := hsa.1.add (hsb.1.mul_left D)
  have hn (k : ℕ) : 0 ≤ z ^ k / k.factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) k :=
    mul_nonneg (by positivity) (tensorNormSquared_nonneg _ _ _ _ _)
  have hsum := Summable.of_nonneg_of_le hn hp hsright
  refine ⟨hsum, ?_⟩
  have hi := hsum.tsum_le_tsum hp hsright
  rw [hsa.1.tsum_add (hsb.1.mul_left D), tsum_mul_left] at hi
  have hj := add_le_add hsa.2 (mul_le_mul_of_nonneg_left hsb.2 hD)
  simpa [a, b, D, z₁, z₂, mul_assoc] using hi.trans hj


 theorem phaseDifference_integral (M : ℕ) : (∫ q : PhaseParameter H, phaseDifference M q ∂phaseBase ν) = 0 := by
  have hp := (phasePrior ν M 1 (by norm_num)).integrable
  have hm := (phasePrior ν M (-1) (by norm_num)).integrable
  change Integrable (phaseDensity (H := H) M 1) (phaseBase ν) at hp
  change Integrable (phaseDensity (H := H) M (-1)) (phaseBase ν) at hm
  change (∫ q, phaseDensity (H := H) M 1 q - phaseDensity M (-1) q ∂phaseBase ν) = 0
  rw [integral_sub hp hm]
  have h1 := (phasePrior ν M 1 (by norm_num)).integral_one
  have h2 := (phasePrior ν M (-1) (by norm_num)).integral_one
  change (∫ q, phaseDensity (H := H) M 1 q ∂phaseBase ν) = 1 at h1
  change (∫ q, phaseDensity (H := H) M (-1) q ∂phaseBase ν) = 1 at h2
  rw [h1, h2]
  norm_num

 theorem AffinePhaseField.pointDensity_mean (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ q, (∫ y, F.markedFactor Au Av s q y ∂μ.prod κ) = 0) :
    ∀ q, (∫ y, (1 + F.markedFactor Au Av s q y) ∂μ.prod κ) = 1 := by
  intro q
  have hi : Integrable (F.markedFactor Au Av s q) (μ.prod κ) := bounded_integrable _ _
    ((F.markedFactor_measurable hm Au Av s hs).comp (measurable_const.prodMk measurable_id))
    (9 * C * S) (F.markedFactor_bound Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hbs q)
  rw [integral_add (integrable_const 1) hi, hzero]
  simp

 def AffinePhaseField.poissonLaw (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ q, (∫ y, F.markedFactor Au Av s q y ∂μ.prod κ) = 0)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ q y, c ≤ 1 + F.markedFactor Au Av s q y)
    (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
    GeneralTesting.DensityLaw (referenceProcess (μ.prod κ) rate) :=
  markedMixtureLaw (μ.prod κ) (phaseBase ν)
    (phasePrior ν M (if positive then 1 else -1) (by cases positive <;> norm_num))
    (fun q y => 1 + F.markedFactor Au Av s q y)
    ((F.markedFactor_measurable hm Au Av s hs).const_add 1)
    2 (1 + 9 * C * S) (by norm_num) (by positivity)
    (fun q => (phaseDensity_bound M _ (by cases positive <;> norm_num) q).2)
    (fun q y => (abs_add_le 1 _).trans (by
      have hb' := F.markedFactor_bound Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hbs q y
      simpa only [abs_one, add_comm] using add_le_add_left hb' 1))
    (fun q y => le_trans (le_of_lt hc) (hlow q y))
    (F.pointDensity_mean μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero) rate

/-- The actual single-pair conclusion of Lemma11, with its leading Gamma
coefficient series and genuine fourth-order remainder. -/
 theorem AffinePhaseField.poisson_hellinger_bound (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C S : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hS : 0 ≤ S) (hb : F.Bounded C)
    (s : Fin 3 → Z → ℝ) (hs : ∀ l, Measurable (s l)) (hbs : ∀ l z, |s l z| ≤ S)
    (hzero : ∀ q, (∫ y, F.markedFactor Au Av s q y ∂μ.prod κ) = 0)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ q y, c ≤ 1 + F.markedFactor Au Av s q y)
    (M : ℕ) (rate : ℝ≥0) :
    GeneralTesting.hellingerSquared
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate true)
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate false) ≤
      (1 / 4) * Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
      ((9 * S ^ 2 * ((rate : ℝ) * c⁻¹)) ^ 2 * (∑' j, if M ≤ j then
        (9 * S ^ 2 * ((rate : ℝ) * c⁻¹)) ^ j / j.factorial * F.gammaNorm ν μ Au Av M j else 0) +
      4 * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 *
        (81 * S ^ 2 * C ^ 2 * ((rate : ℝ) * c⁻¹)) ^ 4 *
        ((81 * S ^ 2 * C ^ 2 * ((rate : ℝ) * c⁻¹)) ^ M / M.factorial) *
        Real.exp (81 * S ^ 2 * C ^ 2 * ((rate : ℝ) * c⁻¹))) := by
  let ψ := fun q y => 1 + F.markedFactor Au Av s q y
  have hψ : Measurable (Function.uncurry ψ) := measurable_const.add (F.markedFactor_measurable hm Au Av s hs)
  have hψb : ∀ q y, |ψ q y| ≤ 1 + 9 * C * S := fun q y => (abs_add_le 1 _).trans (by
    have hi := F.markedFactor_bound Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hbs q y
    simpa only [abs_one, add_comm] using add_le_add_left hi 1)
  have hψ0 : ∀ q y, 0 ≤ ψ q y := fun q y => le_trans (le_of_lt hc) (hlow q y)
  have hmean := F.pointDensity_mean μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero
  have hh := markedMixture_hellinger_chaos_le (μ.prod κ) (phaseBase ν)
    (phasePrior ν M 1 (by norm_num)) (phasePrior ν M (-1) (by norm_num)) ψ hψ
    2 (1 + 9 * C * S) (by norm_num) (by positivity)
    (fun q => (phaseDensity_bound M 1 (by norm_num) q).2)
    (fun q => (phaseDensity_bound M (-1) (by norm_num) q).2) hψb hψ0 hmean rate c hc hlow
  have he : (fun q y => ψ q y - 1) = F.markedFactor Au Av s := by
    funext q y
    dsimp [ψ]
    ring
  rw [he] at hh
  change GeneralTesting.hellingerSquared
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate true)
      (F.poissonLaw ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs hzero c hc hlow M rate false) ≤
      (1 / 4) * Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
      ∑' k, ((rate : ℝ) * c⁻¹) ^ (k + 1) / (k + 1).factorial *
        tensorNormSquared (phaseBase ν) (μ.prod κ) (phaseDifference M) (F.markedFactor Au Av s) (k + 1) at hh
  let z := (rate : ℝ) * c⁻¹
  have hz : 0 ≤ z := by positivity
  have hseries := F.poissonSeries_bound ν μ κ hm Au Av C S hAu hAu1 hAv hAv1 hC hS hb s hs hbs M z hz
  have hshift := PoissonSeriesBounds.tsum_supported_shift
    (fun k => z ^ k / k.factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) k) 1 hseries.1 (fun k hk => by
        have hk0 : k = 0 := by omega
        subst k
        rw [tensorNormSquared_zero _ _ _ _ (phaseDifference_integral ν M), mul_zero])
  change _ ≤ (1 / 4) * Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
    ∑' k, z ^ (k + 1) / (k + 1).factorial * tensorNormSquared (phaseBase ν) (μ.prod κ)
      (phaseDifference M) (F.markedFactor Au Av s) (k + 1) at hh
  rw [← hshift] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hseries.2 (by positivity))

end RoughRegime.PoissonMeasure
