module

public import RoughRegime.RhoPerturbation
public import RoughRegime.ReductionTestingScale


@[expose] public section
/-! The source nonlinear Taylor error is negligible at the actual nearest-even
frequency and shrinking density margin. -/
noncomputable section
open Filter
namespace RoughRegime.ReductionScales

/-- Actual bounded amplitudes beat every fixed exponential frequency loss. -/
theorem amplitude_square_exponential_tendsto (θ τ a b C : ℝ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (ha : 0<a) (hb : 0<b)
    (Au Av : ℝ → ℝ)
    (hAu : ∀ᶠ n in atTop, |Au n|≤n^(-a))
    (hAv : ∀ᶠ n in atTop, |Av n|≤n^(-b)) :
    Tendsto (fun n => ((Au n)^2+(Av n)^2)*Real.exp (C*frequency n θ τ)) atTop (nhds 0) := by
  have hu := frequency_exponential_linear_loss_tendsto_zero θ τ (2*a) C hθ hθhalf hτ (by positivity)
  have hv := frequency_exponential_linear_loss_tendsto_zero θ τ (2*b) C hθ hθhalf hτ (by positivity)
  have hsum := hu.add hv
  simp only [add_zero] at hsum
  apply squeeze_zero' (g := fun n : ℝ => n^(-(2*a))*Real.exp (C*frequency n θ τ)+
    n^(-(2*b))*Real.exp (C*frequency n θ τ)) (Filter.Eventually.of_forall fun n => by positivity)
  · filter_upwards [hAu,hAv,eventually_gt_atTop (0 : ℝ)] with n hu hv hn
    have hus : (Au n)^2≤(n^(-a))^2 := by nlinarith [sq_abs (Au n),abs_nonneg (Au n),Real.rpow_pos_of_pos hn (-a)]
    have hvs : (Av n)^2≤(n^(-b))^2 := by nlinarith [sq_abs (Av n),abs_nonneg (Av n),Real.rpow_pos_of_pos hn (-b)]
    have hpow (r : ℝ) : (n^(-r))^2=n^(-(2*r)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hn.le]
      congr 1
      norm_num; ring
    rw [hpow a] at hus
    rw [hpow b] at hvs
    calc
      _ ≤ (n^(-(2*a))+n^(-(2*b)))*Real.exp (C*frequency n θ τ) :=
        mul_le_mul_of_nonneg_right (add_le_add hus hvs) (Real.exp_pos _).le
      _ = _ := by ring
  · exact hsum

/-- Inverting the unperturbed spectral power is the exact exponential cost. -/
lemma rho_power_inverse_exp (rho : ℝ) (hrho : 0<rho) (M : ℕ) :
    (rho^M)⁻¹=Real.exp ((-Real.log rho)*(M : ℝ)) := by
  rw [mul_comm,Real.exp_nat_mul,Real.exp_neg,Real.exp_log hrho,inv_pow]

/-- The actual narrowed spectral penalty still dominates the nonlinear
amplitude remainder. -/
theorem nonlinear_remainder_ratio_tendsto (θ τ a b lo hi : ℝ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (ha : 0<a) (hb : 0<b)
    (hlo : 0<lo) (hlt : lo<hi) (Au Av : ℝ → ℝ)
    (hAu : ∀ᶠ n in atTop, |Au n|≤n^(-a))
    (hAv : ∀ᶠ n in atTop, |Av n|≤n^(-b)) :
    Tendsto (fun n => ((Au n)^2+(Av n)^2)/
      (Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)))^(frequency n θ τ)) atTop (nhds 0) := by
  let rho := Upper.intervalRho lo hi
  have hrho : 0<rho := Upper.intervalRho_pos lo hi hlo hlt
  have hnum := amplitude_square_exponential_tendsto θ τ a b (-Real.log rho)
    hθ hθhalf hτ ha hb Au Av hAu hAv
  have hratio := Upper.narrowedRho_power_ratio_tendsto atTop lo hi hlo hlt
    (fun n : ℝ => (Real.log n)^(-2 : ℝ)) (fun n => frequency n θ τ)
    logarithmicMargin_tendsto_zero (frequencyTimesMargin_tendsto_zero θ τ hθ hθhalf hτ)
  have hlim := hnum.div hratio (by norm_num : (1 : ℝ)≠0)
  simp only [zero_div] at hlim
  have hpos : ∀ᶠ n : ℝ in atTop,
      0<Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ)) :=
    ((Upper.narrowedRho_differentiableAt lo hi hlo hlt).continuousAt.tendsto.comp
      logarithmicMargin_tendsto_zero).eventually
      (eventually_gt_nhds (by simpa [Upper.narrowedRho] using hrho))
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [hpos] with n hn
  change (((Au n)^2+(Av n)^2)*Real.exp ((-Real.log rho)*(frequency n θ τ : ℝ)))/
    (Upper.narrowedRho lo hi ((Real.log n)^(-2 : ℝ))^(frequency n θ τ)/rho^(frequency n θ τ)) = _
  rw [←rho_power_inverse_exp rho hrho]
  field_simp [pow_ne_zero _ hrho.ne',pow_ne_zero _ hn.ne']

end RoughRegime.ReductionScales
