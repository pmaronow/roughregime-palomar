module

public import RoughRegime.Lower
public import Mathlib


@[expose] public section
/-! Arbitrary-measure marked-Poisson likelihood and tensor identities. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace RoughRegime.PoissonMeasure

set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (prior : Measure W) (μ : Measure Y) [IsProbabilityMeasure prior] [IsProbabilityMeasure μ]

theorem bounded_integrable {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [IsProbabilityMeasure ν] (f : S → ℝ) (hf : Measurable f) (B : ℝ)
    (hb : ∀ x, |f x| ≤ B) : Integrable f ν := by
  apply Integrable.of_bound hf.aestronglyMeasurable B
  exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x

/-- Fubini's square-of-mixture identity, with continuous parameter and mark
spaces allowed. Uniform boundedness supplies every integrability condition. -/
theorem square_mixture_gram (f : W → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w y, |f w y| ≤ B) :
    (∫ y, (∫ w, f w y ∂prior) ^ 2 ∂μ) =
      ∫ q : W × W, (∫ y, f q.1 y * f q.2 y ∂μ) ∂prior.prod prior := by
  have hpoint (y : Y) : (∫ w, f w y ∂prior) ^ 2 =
      ∫ q : W × W, f q.1 y * f q.2 y ∂prior.prod prior := by
    rw [integral_prod_mul (fun w => f w y) (fun w => f w y)]
    ring
  simp_rw [hpoint]
  apply integral_integral_swap
  apply bounded_integrable (μ.prod (prior.prod prior)) _
    ((hf.comp (measurable_snd.fst.prodMk measurable_fst)).mul
      (hf.comp (measurable_snd.snd.prodMk measurable_fst))) (B * B)
  rintro ⟨y, w, w'⟩
  dsimp
  rw [abs_mul]
  exact mul_le_mul (hb w y) (hb w' y) (abs_nonneg _) hB

def tensor (φ : W → Y → ℝ) (k : ℕ) (w : W) (xs : Fin k → Y) : ℝ :=
  ∏ i, φ w (xs i)

theorem tensor_measurable (φ : W → Y → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (k : ℕ) :
    Measurable (Function.uncurry (tensor φ k)) := by
  unfold tensor
  apply Finset.measurable_prod
  intro i _
  exact hφ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

omit [MeasurableSpace W] [MeasurableSpace Y] in
theorem tensor_bound (φ : W → Y → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hφ : ∀ w y, |φ w y| ≤ C) (k : ℕ) (w : W) (xs : Fin k → Y) :
    |tensor φ k w xs| ≤ C ^ k := by
  unfold tensor
  rw [Finset.abs_prod]
  convert Finset.prod_le_prod₀ (fun i _ => show 0 ≤ |φ w (xs i)| from abs_nonneg _) (fun i _ => hφ w (xs i)) using 1
  simp

def inner (φ : W → Y → ℝ) (w w' : W) : ℝ := ∫ y, φ w y * φ w' y ∂μ

def tensorMixture (v : W → ℝ) (φ : W → Y → ℝ) (k : ℕ) (xs : Fin k → Y) : ℝ :=
  ∫ w, v w * tensor φ k w xs ∂prior

def tensorNormSquared (v : W → ℝ) (φ : W → Y → ℝ) (k : ℕ) : ℝ :=
  ∫ xs : Fin k → Y, tensorMixture prior v φ k xs ^ 2 ∂Measure.pi (fun _ => μ)

/-- The Hilbert tensor Gram identity for arbitrary prior and mark measures. -/
theorem tensorNormSquared_gram (v : W → ℝ) (φ : W → Y → ℝ)
    (hv : Measurable v) (hφ : Measurable (Function.uncurry φ))
    (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbφ : ∀ w y, |φ w y| ≤ C) (k : ℕ) :
    tensorNormSquared prior μ v φ k =
      ∫ q : W × W, v q.1 * v q.2 * inner μ φ q.1 q.2 ^ k ∂prior.prod prior := by
  have hfm : Measurable (Function.uncurry (fun w xs => v w * tensor φ k w xs)) :=
    (hv.comp measurable_fst).mul (tensor_measurable φ hφ k)
  have hfb (w : W) (xs : Fin k → Y) : |v w * tensor φ k w xs| ≤ V * C ^ k := by
    rw [abs_mul]
    exact mul_le_mul (hbv w) (tensor_bound φ C hC hbφ k w xs) (abs_nonneg _) hV
  unfold tensorNormSquared tensorMixture
  rw [square_mixture_gram prior (Measure.pi (fun _ : Fin k => μ))
    (fun w xs => v w * tensor φ k w xs) hfm (V * C ^ k) (by positivity) hfb]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    change (∫ xs : Fin k → Y, (v q.1 * tensor φ k q.1 xs) *
        (v q.2 * tensor φ k q.2 xs) ∂Measure.pi (fun _ => μ)) =
      v q.1 * v q.2 * inner μ φ q.1 q.2 ^ k
    have he : (fun xs : Fin k → Y => (v q.1 * tensor φ k q.1 xs) *
        (v q.2 * tensor φ k q.2 xs)) =
        fun xs => (v q.1 * v q.2) * ∏ i, (φ q.1 (xs i) * φ q.2 (xs i)) := by
      funext xs
      simp [tensor, Finset.prod_mul_distrib]
      ring
    rw [he, integral_const_mul, integral_fin_nat_prod_eq_prod
      (μ := fun _ : Fin k => μ) (fun _ y => φ q.1 y * φ q.2 y)]
    simp [inner]

/-- A true Poisson count has the exponential generating function used for
marked point configurations. -/
theorem poisson_count_generating (rate : ℝ≥0) (h : ℝ) :
    (∫ n : ℕ, h ^ n ∂ProbabilityTheory.poissonMeasure rate) =
      Real.exp ((rate : ℝ) * (h - 1)) := by
  rw [ProbabilityTheory.poissonMeasure, integral_sum_dirac]
  · simp only [smul_eq_mul, ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ _ / (_ : ℕ).factorial)]
    exact (Lower.poisson_generating_hasSum rate h).tsum_eq
  · intro n
    exact ENNReal.ofReal_ne_top

/-- The conditional marked generating functional now uses arbitrary mark
measures, rather than a finite sum over a discretized observation space. -/
theorem marked_poisson_generating (rate : ℝ≥0) (h : Y → ℝ) :
    (∫ n : ℕ, (∫ xs : Fin n → Y, ∏ i, h (xs i) ∂Measure.pi (fun _ => μ))
      ∂ProbabilityTheory.poissonMeasure rate) = Real.exp ((rate : ℝ) * ((∫ y, h y ∂μ) - 1)) := by
  simp_rw [integral_fin_nat_prod_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact poisson_count_generating rate (∫ y, h y ∂μ)

theorem inner_measurable (φ : W → Y → ℝ) (hφ : Measurable (Function.uncurry φ)) :
    Measurable (Function.uncurry (inner μ φ)) := by
  have hm : Measurable (fun q : (W × W) × Y => φ q.1.1 q.2 * φ q.1.2 q.2) :=
    (hφ.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hφ.comp (measurable_fst.snd.prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace W] in
theorem inner_bound (φ : W → Y → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ w y, |φ w y| ≤ C) (w w' : W) : |inner μ φ w w'| ≤ C * C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun y => φ w y * φ w' y) (C := C * C)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb w y) (hb w' y) (abs_nonneg _) hC)
  simpa [Real.norm_eq_abs, inner] using h

/-- The exponential expansion may be interchanged with an integral over an
arbitrary probability space. The domination is an explicit exponential series. -/
theorem bounded_weighted_exp_hasSum {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (w K : S → ℝ)
    (hw : Measurable w) (hK : Measurable K)
    (B C c : ℝ) (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hbw : ∀ x, |w x| ≤ B) (hbK : ∀ x, |K x| ≤ C) :
    HasSum (fun n => c ^ n / n.factorial * ∫ x, w x * K x ^ n ∂ν)
      (∫ x, w x * Real.exp (c * K x) ∂ν) := by
  let F := fun n (x : S) => w x * ((c * K x) ^ n / n.factorial)
  let bound := fun n (_ : S) => B * ((|c| * C) ^ n / n.factorial)
  have hm (n : ℕ) : AEStronglyMeasurable (F n) ν := by
    exact (hw.mul (((hK.const_mul c).pow_const n).div_const _)).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂ν, ‖F n x‖ ≤ bound n x := by
    exact Filter.Eventually.of_forall fun x => by
      have hk : |c * K x| ≤ |c| * C := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbK x) (abs_nonneg c)
      have hp := pow_le_pow_left₀ (abs_nonneg (c * K x)) hk n
      have hmul := mul_le_mul (hbw x) hp (pow_nonneg (abs_nonneg _) n) hB
      dsimp [F, bound]
      rw [abs_mul, abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)]
      simpa [mul_div_assoc] using div_le_div_of_nonneg_right hmul
        (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)
  have hs (x : S) : Summable fun n => bound n x := by
    exact ((NormedSpace.expSeries_div_hasSum_exp (|c| * C)).mul_left B).summable
  have hi : Integrable (fun x : S => ∑' n, bound n x) ν := by
    dsimp [bound]
    exact integrable_const _
  have hlim : ∀ᵐ x ∂ν, HasSum (fun n => F n x) (w x * Real.exp (c * K x)) :=
    Filter.Eventually.of_forall fun x => by
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (c * K x)).mul_left (w x)
  have h := hasSum_integral_of_dominated_convergence bound hm hbound
    (Filter.Eventually.of_forall hs) hi hlim
  convert h using 1
  funext n
  have he : (fun x => F n x) = fun x => (c ^ n / n.factorial) * (w x * K x ^ n) := by
    funext x
    dsimp [F]
    rw [mul_pow]
    ring
  rw [he, integral_const_mul]

/-- The actual arbitrary-measure chaos expansion of the exponential kernel. -/
theorem exponential_kernel_chaos_hasSum (v : W → ℝ) (φ : W → Y → ℝ)
    (hv : Measurable v) (hφ : Measurable (Function.uncurry φ))
    (V C c : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbφ : ∀ w y, |φ w y| ≤ C) :
    HasSum (fun k => c ^ k / k.factorial * tensorNormSquared prior μ v φ k)
      (∫ q : W × W, v q.1 * v q.2 * Real.exp (c * inner μ φ q.1 q.2) ∂prior.prod prior) := by
  simp_rw [tensorNormSquared_gram prior μ v φ hv hφ V C hV hC hbv hbφ]
  apply bounded_weighted_exp_hasSum (prior.prod prior)
    (fun q : W × W => v q.1 * v q.2) (Function.uncurry (inner μ φ))
    ((hv.comp measurable_fst).mul (hv.comp measurable_snd)) (inner_measurable μ φ hφ)
    (V * V) (C * C) c (by positivity) (by positivity)
  · intro q
    rw [abs_mul]
    exact mul_le_mul (hbv q.1) (hbv q.2) (abs_nonneg _) hV
  · intro q
    exact inner_bound μ φ C hC hbφ q.1 q.2

/-- Count-conditioned squared mixture likelihood for arbitrary continuous
mark and parameter spaces, with every exchange proved by domination. -/
theorem poisson_likelihood_square_hasSum (v : W → ℝ) (ψ : W → Y → ℝ)
    (hv : Measurable v) (hψ : Measurable (Function.uncurry ψ))
    (V C rate c : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbψ : ∀ w y, |ψ w y| ≤ C) :
    HasSum (fun n => Lower.poissonMass rate n * (c⁻¹) ^ n * tensorNormSquared prior μ v ψ n)
      (∫ q : W × W, v q.1 * v q.2 *
        Real.exp (rate * (c⁻¹ * inner μ ψ q.1 q.2 - 1)) ∂prior.prod prior) := by
  have h := (exponential_kernel_chaos_hasSum prior μ v ψ hv hψ V C (rate * c⁻¹)
    hV hC hbv hbψ).mul_left (Real.exp (-rate))
  convert h using 1
  · funext n
    simp only [Lower.poissonMass, mul_pow]
    ring
  · rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      dsimp only
      rw [show Real.exp (rate * (c⁻¹ * inner μ ψ q.1 q.2 - 1)) =
        Real.exp (-rate) * Real.exp (rate * c⁻¹ * inner μ ψ q.1 q.2) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring

theorem centered_likelihood_inner (φ : W → Y → ℝ)
    (hφ : Measurable (Function.uncurry φ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ w y, |φ w y| ≤ C) (hmean : ∀ w, (∫ y, φ w y ∂μ) = 0) (w w' : W) :
    inner μ (fun w y => 1 + φ w y) w w' = 1 + inner μ φ w w' := by
  have hi (a : W) : Integrable (φ a) μ := bounded_integrable μ (φ a)
    (hφ.comp (measurable_const.prodMk measurable_id)) C (hb a)
  have hip : Integrable (fun y => φ w y * φ w' y) μ := bounded_integrable μ _
    ((hφ.comp (measurable_const.prodMk measurable_id)).mul
      (hφ.comp (measurable_const.prodMk measurable_id))) (C * C)
    (fun y => by rw [abs_mul]; exact mul_le_mul (hb w y) (hb w' y) (abs_nonneg _) hC)
  have he : (fun y => (1 + φ w y) * (1 + φ w' y)) =
      fun y => ((1 + φ w y) + φ w' y) + φ w y * φ w' y := by
    funext y
    ring
  have hi₁ : Integrable (fun y => 1 + φ w y) μ := (integrable_const 1).add (hi w)
  have hi₂ : Integrable (fun y => 1 + φ w y + φ w' y) μ := hi₁.add (hi w')
  unfold inner
  rw [he, integral_add hi₂ hip,
    integral_add hi₁ (hi w'),
    integral_add (integrable_const 1) (hi w), hmean, hmean]
  simp

/-- General-measure weighted Poisson chaos identity. On the left the count
is a genuine Poisson random variable and its marks have their actual product
measure. On the right the tensors use the same arbitrary mark/prior spaces. -/
theorem poisson_chaos_identity (v : W → ℝ) (φ : W → Y → ℝ)
    (hv : Measurable v) (hφ : Measurable (Function.uncurry φ))
    (V C : ℝ) (rate : ℝ≥0) (c : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbφ : ∀ w y, |φ w y| ≤ C)
    (hmean : ∀ w, (∫ y, φ w y ∂μ) = 0) :
    (∫ n : ℕ, (c⁻¹) ^ n * tensorNormSquared prior μ v (fun w y => 1 + φ w y) n
      ∂ProbabilityTheory.poissonMeasure rate) =
      Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
        ∑' k, ((rate : ℝ) * c⁻¹) ^ k / k.factorial * tensorNormSquared prior μ v φ k := by
  have hψ : Measurable (Function.uncurry (fun w y => 1 + φ w y)) := measurable_const.add hφ
  have hbψ (w : W) (y : Y) : |1 + φ w y| ≤ 1 + C := by
    calc
      _ ≤ |(1 : ℝ)| + |φ w y| := abs_add_le _ _
      _ ≤ 1 + C := by simpa using add_le_add_left (hbφ w y) 1
  have hh := poisson_likelihood_square_hasSum prior μ v (fun w y => 1 + φ w y) hv hψ
    V (1 + C) rate c hV (by positivity) hbv hbψ
  have hcount : (∫ n : ℕ, (c⁻¹) ^ n * tensorNormSquared prior μ v (fun w y => 1 + φ w y) n
      ∂ProbabilityTheory.poissonMeasure rate) =
      ∑' n, Lower.poissonMass rate n * (c⁻¹) ^ n *
        tensorNormSquared prior μ v (fun w y => 1 + φ w y) n := by
    rw [ProbabilityTheory.poissonMeasure, integral_sum_dirac]
    · simp only [smul_eq_mul, ENNReal.toReal_ofReal (by positivity :
        0 ≤ Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ _ / (_ : ℕ).factorial)]
      simp only [Lower.poissonMass, mul_assoc]
    · intro n
      exact ENNReal.ofReal_ne_top
  rw [hcount, hh.tsum_eq,
    (exponential_kernel_chaos_hasSum prior μ v φ hv hφ V C ((rate : ℝ) * c⁻¹)
      hV hC hbv hbφ).tsum_eq, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    dsimp only
    rw [centered_likelihood_inner μ φ hφ C hC hbφ hmean]
    rw [show Real.exp ((rate : ℝ) * (c⁻¹ * (1 + inner μ φ q.1 q.2) - 1)) =
      Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
        Real.exp ((rate : ℝ) * c⁻¹ * inner μ φ q.1 q.2) by
          rw [← Real.exp_add]
          congr 1
          ring]
    ring

omit [IsProbabilityMeasure prior] [IsProbabilityMeasure μ] in
theorem tensorNormSquared_nonneg (v : W → ℝ) (φ : W → Y → ℝ) (k : ℕ) :
    0 ≤ tensorNormSquared prior μ v φ k :=
  integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure prior] [IsProbabilityMeasure μ] in
theorem tensorNormSquared_zero (v : W → ℝ) (φ : W → Y → ℝ)
    (hv : (∫ w, v w ∂prior) = 0) : tensorNormSquared prior μ v φ 0 = 0 := by
  simp [tensorNormSquared, tensorMixture, tensor, hv]

/-- Positive-order form of the general chaos identity, as in equation (5.8).
The zero-order term vanishes because the signed prior has total mass zero. -/
theorem poisson_chaos_identity_positive_orders (v : W → ℝ) (φ : W → Y → ℝ)
    (hv : Measurable v) (hφ : Measurable (Function.uncurry φ))
    (V C : ℝ) (rate : ℝ≥0) (c : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbv : ∀ w, |v w| ≤ V) (hbφ : ∀ w y, |φ w y| ≤ C)
    (hmean : ∀ w, (∫ y, φ w y ∂μ) = 0) (hv0 : (∫ w, v w ∂prior) = 0) :
    (∫ n : ℕ, (c⁻¹) ^ n * tensorNormSquared prior μ v (fun w y => 1 + φ w y) n
      ∂ProbabilityTheory.poissonMeasure rate) =
      Real.exp ((rate : ℝ) * (c⁻¹ - 1)) *
        ∑' k, ((rate : ℝ) * c⁻¹) ^ (k + 1) / (k + 1).factorial *
          tensorNormSquared prior μ v φ (k + 1) := by
  have hs := exponential_kernel_chaos_hasSum prior μ v φ hv hφ V C ((rate : ℝ) * c⁻¹)
    hV hC hbv hbφ
  have h := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, tensorNormSquared_zero prior μ v φ hv0,
    mul_zero, sub_zero] at h
  rw [h.tsum_eq]
  rw [poisson_chaos_identity prior μ v φ hv hφ V C rate c hV hC hbv hbφ hmean, hs.tsum_eq]

end RoughRegime.PoissonMeasure
