module

public import RoughRegime.FuzzyTesting
public import RoughRegime.GlobalPriorTarget


@[expose] public section
/-! Actual independent-prior target variance and the C1 oscillation bound
used in the nonlinear lower-bound reduction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false

variable {ι W : Type*} [Fintype ι] [MeasurableSpace W]

 theorem independent_pair_variance (prior : ι → Measure W) [∀ i, IsProbabilityMeasure (prior i)]
    (F : ι → Bool → W → ℝ) (hF : ∀ i label, Measurable (F i label))
    (center : ι → ℝ) (amp : ℝ) (_hamp : 0 ≤ amp)
    (hb : ∀ i label w, |F i label w - center i| ≤ amp) (scale : ℝ) :
    variance (fun z : ι → W => scale * ∑ i, (F i false (z i) + F i true (z i)))
      (Measure.pi prior) ≤ scale ^ 2 * Fintype.card ι * (2 * amp) ^ 2 := by
  let X := fun i w => F i false w + F i true w
  have hm (i : ι) : Measurable (X i) := (hF i false).add (hF i true)
  have hbx (i : ι) (w : W) : |X i w - 2 * center i| ≤ 2 * amp := by
    have ht := abs_add_le (F i false w - center i) (F i true w - center i)
    have hbf := hb i false w
    have hbt := hb i true w
    dsimp [X]
    calc
      _ = |(F i false w - center i) + (F i true w - center i)| := by congr 1; ring
      _ ≤ _ := ht
      _ ≤ _ := by linarith
  have hnorm (i : ι) (w : W) : ‖X i w‖ ≤ 2 * amp + |2 * center i| := by
    rw [Real.norm_eq_abs]
    have ht := abs_add_le (X i w - 2 * center i) (2 * center i)
    have he : X i w - 2 * center i + 2 * center i = X i w := by ring
    rw [he] at ht
    linarith [hbx i w]
  have hmem (i : ι) : MemLp (X i) 2 (prior i) :=
    MemLp.of_bound (hm i).aestronglyMeasurable _ (Filter.Eventually.of_forall (hnorm i))
  have hv (i : ι) : variance (X i) (prior i) ≤ (2 * amp) ^ 2 := by
    have hh := variance_le_sq_of_bounded (μ := prior i) (X := X i)
      (a := 2 * center i - 2 * amp) (b := 2 * center i + 2 * amp)
      (Filter.Eventually.of_forall (fun w => by
        have hw := abs_le.mp (hbx i w)
        exact ⟨by linarith, by linarith⟩)) (hm i).aemeasurable
    convert hh using 1
    ring
  have he := variance_sum_pi hmem
  rw [variance_const_mul]
  have hfun : (fun z : ι → W => ∑ i, (F i false (z i) + F i true (z i))) =
      (∑ i, fun z : ι → W => X i (z i)) := by
    ext z
    simp [X]
  rw [hfun, he]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hv i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (sq_nonneg scale)

 theorem independent_pair_variance_amplitudes (prior : ι → Measure W)
    [∀ i, IsProbabilityMeasure (prior i)] (F : ι → Bool → W → ℝ)
    (hF : ∀ i label, Measurable (F i label)) (center : ι → ℝ) (L Au Av : ℝ)
    (hL : 0 ≤ L) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
    (hb : ∀ i label w, |F i label w - center i| ≤ L * (Au + Av)) (scale : ℝ) :
    variance (fun z : ι → W => scale * ∑ i, (F i false (z i) + F i true (z i)))
      (Measure.pi prior) ≤ 8 * scale ^ 2 * Fintype.card ι * L ^ 2 * (Au ^ 2 + Av ^ 2) := by
  have hh := independent_pair_variance prior F hF center (L * (Au + Av)) (by positivity) hb scale
  apply hh.trans
  have ha : (Au + Av) ^ 2 ≤ 2 * (Au ^ 2 + Av ^ 2) := by nlinarith [sq_nonneg (Au - Av)]
  have he : scale ^ 2 * Fintype.card ι * (2 * (L * (Au + Av))) ^ 2 =
      (4 * scale ^ 2 * Fintype.card ι * L ^ 2) * (Au + Av) ^ 2 := by ring
  rw [he]
  convert mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 4 * scale ^ 2 * Fintype.card ι * L ^ 2) using 1
  ring

 theorem local_response_oscillation (F : (ℝ × ℝ) → ℝ) (hF : DifferentiableAt ℝ F 0) :
    ∃ ε > 0, ∃ L > 0, ∀ u v : ℝ, |u| + |v| < ε →
      |F (u, v) - F 0| ≤ L * (|u| + |v|) := by
  obtain ⟨L, hL, hB⟩ := hF.isBigO_sub.exists_pos
  have hb := hB.bound
  obtain ⟨ε, he, hball⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨ε, he, L, hL, ?_⟩
  intro u v huv
  have hn : ‖(u, v)‖ ≤ |u| + |v| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg v)) (le_add_of_nonneg_left (abs_nonneg u))
  have hh := hball (y := (u, v)) (by simpa only [dist_eq_norm, sub_zero] using hn.trans_lt huv)
  rw [Real.norm_eq_abs, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hn hL.le)

/-- A bounded response perturbation has a bounded weighted integral. The
centering uses the true design-density mass, so density fluctuations cancel. -/
theorem weighted_response_oscillation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p f : X → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (hf : Measurable f) (center amp : ℝ) (_ha : 0 ≤ amp)
    (hb : ∀ x, |f x - center| ≤ amp) :
    |(∫ x, p x * f x ∂μ) - center * ∫ x, p x ∂μ| ≤ amp * ∫ x, p x ∂μ := by
  have hm : AEStronglyMeasurable (fun x => p x * (f x - center)) μ :=
    hp.aestronglyMeasurable.mul (hf.sub measurable_const).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ‖p x * (f x - center)‖ ≤ amp * p x := by
    filter_upwards [hp0] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x) hx
  have hi : Integrable (fun x => p x * (f x - center)) μ := (hp.const_mul amp).mono' hm hbound
  have hpf : Integrable (fun x => p x * f x) μ := by
    have hh := hi.add (hp.const_mul center)
    apply hh.congr
    exact Filter.Eventually.of_forall fun x => by dsimp; ring
  have hid : (∫ x, p x * f x ∂μ) - center * ∫ x, p x ∂μ =
      ∫ x, p x * (f x - center) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hpf (hp.const_mul center)]
    congr 1
    ext x
    ring
  rw [hid]
  have hh := (norm_integral_le_integral_norm (fun x => p x * (f x - center))).trans
    (integral_mono_ae hi.norm (hp.const_mul amp) hbound)
  simpa only [Real.norm_eq_abs, integral_const_mul] using hh

end RoughRegime.LowerMeasure

namespace RoughRegime.LatticePriors
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem independentPairTarget_variance_bound {D N : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ) (positive : Bool)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ label, Measurable (F label)) (center L Au Av ell : ℝ)
    (hL : 0 ≤ L) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
    (hb : ∀ label w, |F label w - center| ≤ L * (Au + Av)) :
    variance (independentPairTarget (D := D) (N := N) ell F) (globalBlockPrior μ M positive) ≤
      8 * (ell ^ (D + 1)) ^ 2 * Fintype.card (GridPair D N) * L ^ 2 * (Au ^ 2 + Av ^ 2) := by
  have he : independentPairTarget (D := D) (N := N) ell F =
      (fun z => ell ^ (D + 1) * ∑ i : GridPair D N, (F false (z i) + F true (z i))) := by
    ext z
    simp only [independentPairTarget, GridBlock, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rw [he]
  exact RoughRegime.LowerMeasure.independent_pair_variance_amplitudes
    (fun _ : GridPair D N => blockPrior μ M positive) (fun _ label => F label)
    (fun _ label => hF label) (fun _ => center) L Au Av hL hAu hAv (fun _ => hb) _

end RoughRegime.LatticePriors
