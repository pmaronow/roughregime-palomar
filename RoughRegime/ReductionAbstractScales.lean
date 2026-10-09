module

public import RoughRegime.ReductionRawHardness
public import RoughRegime.TaylorSeparationScales


@[expose] public section
/-! The numerical reduction in Proposition 12 for arbitrary admissible
resolution and multiplier sequences. No particular lattice construction or
largest-level choice is used. Every limit is derived from the original
numerical constraints and the actual rounded even-side block count. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.ReductionScales
set_option maxHeartbeats 900000

structure AbstractScaleParameters where
  d : ℕ
  hd : 0 < d
  a : ℝ
  b : ℝ
  lo : ℝ
  hi : ℝ
  v0 : ℝ
  epsilonU : ℝ
  epsilonV : ℝ
  Cstar : ℝ
  CΓ : ℝ
  CE : ℝ
  cstar : ℝ
  c0 : ℝ
  ha : 0 < a
  hb : 0 < b
  hhalf : a+b < 1/2
  hlo : 0 < lo
  hlt : lo < hi
  hv : 0 < v0
  hεu : 0 < epsilonU
  hεu1 : epsilonU ≤ 1
  hεv : 0 < epsilonV
  hεv1 : epsilonV ≤ 1
  hCstar : 1 ≤ Cstar
  hCΓ : 1 ≤ CΓ
  hCE : 0 ≤ CE
  hcstar : 0 < cstar
  hmargin : 1+Real.log (2*v0*Cstar*CΓ)+CE < c0

namespace AbstractScaleParameters
abbrev theta (A : AbstractScaleParameters) : ℝ := A.a+A.b
abbrev tau (A : AbstractScaleParameters) : ℝ := RoughRegime.Rates.tau A.lo A.hi
theorem theta_pos (A : AbstractScaleParameters) : 0 < A.theta := add_pos A.ha A.hb
theorem tau_pos (A : AbstractScaleParameters) : 0 < A.tau :=
  RoughRegime.Rates.tau_pos A.lo A.hi A.hlo A.hlt
theorem C1_pos (A : AbstractScaleParameters) : 0 < 2*A.v0*A.Cstar*A.CΓ := by
  have hv := A.hv
  have hC := zero_lt_one.trans_le A.hCstar
  have hΓ := zero_lt_one.trans_le A.hCΓ
  positivity
end AbstractScaleParameters

structure AbstractScaleChoice (A : AbstractScaleParameters) where
  R : ℝ → ℝ
  m : ℝ → ℝ
  hRpos : ∀ᶠ n in atTop, 1 ≤ R n
  hmpos : ∀ᶠ n in atTop, 1 ≤ m n
  hR : (fun n => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n A.theta A.tau))
  hmM : ∀ᶠ n in atTop, m n ≤ A.cstar*frequency n A.theta A.tau
  hma : ∀ᶠ n in atTop, m n ≤ (R n)^A.a
  hmb : ∀ᶠ n in atTop, m n ≤ (R n)^A.b

namespace AbstractScaleChoice
variable {A : AbstractScaleParameters}
abbrev B (S : AbstractScaleChoice A) (n : ℝ) : ℕ := selectedBlockCount A.theta A.tau A.c0 S.R A.d n
def Lambda (S : AbstractScaleChoice A) (n : ℝ) : ℝ := 2*A.v0/blockInflation A.theta A.tau A.c0 S.R A.d n
def Au (S : AbstractScaleChoice A) (n : ℝ) : ℝ := amplitude A.epsilonU (S.B n) (S.R n) A.a (S.m n)
def Av (S : AbstractScaleChoice A) (n : ℝ) : ℝ := amplitude A.epsilonV (S.B n) (S.R n) A.b (S.m n)
def gap (S : AbstractScaleChoice A) (n : ℝ) : ℝ :=
  S.Au n*S.Av n*Upper.narrowedRho A.lo A.hi ((Real.log n)^(-2 : ℝ))^(frequency n A.theta A.tau)
def rawI (S : AbstractScaleChoice A) (n : ℝ) : ℝ :=
  rawLeadingHardness n (S.B n) A.theta A.v0 (A.epsilonU*A.epsilonV)
    (S.R n) (S.m n) A.CE (2*A.v0*A.Cstar*A.CΓ) (frequency n A.theta A.tau)
def poissonMajorant (S : AbstractScaleChoice A) (n : ℝ) : ℝ :=
  A.Cstar*A.CΓ*S.rawI n*Real.exp (A.CΓ*A.Cstar*S.Lambda n*(S.R n)^Real.sqrt (frequency n A.theta A.tau))+
  S.rawI n*remainderRatio A.Cstar (S.Lambda n) (S.Au n) (S.Av n) (S.R n) A.CE A.CΓ (frequency n A.theta A.tau)
def gapConstant (A : AbstractScaleParameters) : ℝ :=
  A.epsilonU*A.epsilonV*separationConstant A.theta A.tau A.c0/4

theorem gapConstant_pos (A : AbstractScaleParameters) : 0 < gapConstant A := by
  unfold gapConstant
  exact div_pos (mul_pos (mul_pos A.hεu A.hεv)
    (separationConstant_positive A.theta A.tau A.c0 A.theta_pos A.hhalf A.tau_pos)) (by norm_num)

theorem block_superlog (S : AbstractScaleChoice A) (q : ℝ) :
    Tendsto (fun n : ℝ => (S.B n : ℝ)/(n*(Real.log n)^q)) atTop atTop := by
  simpa only [blockInflation,div_div] using blockInflation_div_logPower_tendsto
    A.theta A.tau A.c0 q A.theta_pos A.hhalf A.tau_pos S.R S.hRpos S.hR A.d A.hd

theorem amplitude_bounds (S : AbstractScaleChoice A) :
    ∀ᶠ n : ℝ in atTop,
      0 < S.Au n ∧ 0 < S.Av n ∧
      S.Au n ≤ A.epsilonU*(S.B n : ℝ)^(-A.a) ∧
      S.Av n ≤ A.epsilonV*(S.B n : ℝ)^(-A.b) ∧
      |S.Au n| ≤ n^(-A.a) ∧ |S.Av n| ≤ n^(-A.b) := by
  have hu := selected_amplitude_eventually_le_sample A.theta A.tau A.c0 A.epsilonU A.a
    A.theta_pos A.hhalf A.tau_pos A.hεu.le A.hεu1 A.ha.le S.R S.m S.hRpos S.hR S.hma A.d A.hd
  have hv := selected_amplitude_eventually_le_sample A.theta A.tau A.c0 A.epsilonV A.b
    A.theta_pos A.hhalf A.tau_pos A.hεv.le A.hεv1 A.hb.le S.R S.m S.hRpos S.hR S.hmb A.d A.hd
  filter_upwards [S.hRpos,S.hmpos,S.hma,S.hmb,hu,hv,eventually_gt_atTop (0 : ℝ)]
    with n hR hm hma hmb hu hv hn
  have hRp : 0 < S.R n := zero_lt_one.trans_le hR
  have hBp : 0 < (S.B n : ℝ) := by exact_mod_cast blockCount_positive n (S.R n) _ A.d hn hRp
  have hmp : 0 < S.m n := zero_lt_one.trans_le hm
  have hup := amplitude_positive A.epsilonU (S.B n) (S.R n) A.a (S.m n) A.hεu hBp hRp hmp
  have hvp := amplitude_positive A.epsilonV (S.B n) (S.R n) A.b (S.m n) A.hεv hBp hRp hmp
  refine ⟨hup,hvp,amplitude_le_block _ _ _ _ _ A.hεu.le hBp hRp hma,
    amplitude_le_block _ _ _ _ _ A.hεv.le hBp hRp hmb,?_,?_⟩
  · simpa only [Au,abs_of_pos hup] using hu
  · simpa only [Av,abs_of_pos hvp] using hv

theorem rawI_eq_physical (S : AbstractScaleChoice A) (n : ℝ) (hn : 0 < n) (hR : 0 < S.R n) :
    S.rawI n = (S.B n : ℝ)*(S.Lambda n)^2*(S.Au n)^2*(S.Av n)^2*
      (S.R n)^(1-(frequency n A.theta A.tau : ℝ))*Real.exp (A.CE*frequency n A.theta A.tau)*
      (A.Cstar*A.CΓ*S.Lambda n)^(frequency n A.theta A.tau)/(frequency n A.theta A.tau).factorial := by
  have hB : 0 < (S.B n : ℝ) := by exact_mod_cast blockCount_positive n (S.R n) _ A.d hn hR
  have hΛ : S.Lambda n = 2*A.v0*n/(S.B n : ℝ) := by
    unfold Lambda blockInflation
    rw [div_div_eq_mul_div]
  have hy : A.Cstar*A.CΓ*(2*A.v0*n/(S.B n : ℝ)) = (2*A.v0*A.Cstar*A.CΓ)*n/(S.B n : ℝ) := by ring
  rw [hΛ,hy]
  have hraw := rawLeadingHardness_eq n (S.B n) A.theta A.v0 (A.epsilonU*A.epsilonV)
    (S.R n) (S.m n) A.CE (2*A.v0*A.Cstar*A.CΓ) (frequency n A.theta A.tau) hn hB hR
  have hamp := rawLeadingHardness_amplitudes_eq n (S.B n) A.a A.b A.theta A.v0 A.epsilonU A.epsilonV
    (S.R n) (S.m n) A.CE (2*A.v0*A.Cstar*A.CΓ) (frequency n A.theta A.tau) hn hB hR rfl
  exact hraw.trans (hamp.symm.trans (by dsimp [Au,Av]; ring))

theorem rawI_tendsto_zero (S : AbstractScaleChoice A) : Tendsto S.rawI atTop (nhds 0) := by
  have hε : A.epsilonU*A.epsilonV ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul A.hεu1 A.hεv1 A.hεv.le (by norm_num)
      _ = _ := by norm_num
  exact selected_rawLeadingHardness_tendsto_zero A.theta A.tau A.c0 A.v0 (A.epsilonU*A.epsilonV)
    A.CE (2*A.v0*A.Cstar*A.CΓ) A.cstar A.theta_pos A.hhalf A.tau_pos A.hv
    (mul_pos A.hεu A.hεv) hε A.C1_pos A.hcstar A.hmargin
    S.R S.m S.hRpos S.hmpos S.hR S.hmM A.d A.hd

theorem poissonMajorant_tendsto_zero (S : AbstractScaleChoice A) :
    Tendsto S.poissonMajorant atTop (nhds 0) := by
  have hI := S.rawI_tendsto_zero
  have hrem := selected_remainderRatio_tendsto_zero A.theta A.tau A.c0 A.epsilonU A.epsilonV
    A.a A.b A.Cstar A.v0 A.CE A.CΓ A.theta_pos A.hhalf A.tau_pos A.ha A.hb
    A.hεu A.hεu1 A.hεv A.hεv1 (zero_le_one.trans A.hCstar) A.hv A.hCE A.hCΓ
    S.R S.m S.hRpos S.hmpos S.hR S.hma S.hmb A.d A.hd
  have ht := tilted_tail_ratio_tendsto_zero A.theta A.tau A.c0 (2*A.v0*A.Cstar*A.CΓ)
    A.theta_pos A.hhalf A.tau_pos A.C1_pos S.R S.hRpos S.hR A.d A.hd
  have ht' : Tendsto (fun n : ℝ => A.CΓ*A.Cstar*S.Lambda n*(S.R n)^Real.sqrt (frequency n A.theta A.tau))
      atTop (nhds 0) := by
    apply Filter.Tendsto.congr' _ ht
    exact Eventually.of_forall (fun n => by unfold Lambda; ring)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp ht'
  simp only [Real.exp_zero] at hexp
  have hf := (hI.mul hexp).const_mul (A.Cstar*A.CΓ)
  have hs := hI.mul hrem
  simp only [zero_mul,mul_zero] at hf hs
  have hsum := hf.add hs
  simp only [zero_add] at hsum
  apply Filter.Tendsto.congr' _ hsum
  exact Eventually.of_forall (fun n => by simp only [Function.comp_apply]; unfold poissonMajorant Au Av Lambda; ring)

theorem intervalRho_pow_eq_exp_tau (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : ℕ) :
    Upper.intervalRho lo hi ^ M = Real.exp (-RoughRegime.Rates.tau lo hi*M) := by
  have hρ := RoughRegime.Rates.rho_pos lo hi hlo hlt
  change RoughRegime.Rates.rho lo hi ^ M = _
  unfold RoughRegime.Rates.tau
  rw [neg_neg,mul_comm,Real.exp_nat_mul,Real.exp_log hρ]

theorem gap_eventually_lower (S : AbstractScaleChoice A) :
    ∀ᶠ n : ℝ in atTop, gapConstant A*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau ≤ S.gap n := by
  have hp := selected_amplitude_product_eventually_lower A.theta A.tau A.c0 A.epsilonU A.epsilonV
    A.a A.b A.theta_pos A.hhalf A.tau_pos A.hεu.le A.hεv.le rfl S.R S.m S.hRpos S.hR A.d A.hd
  have hr := Upper.narrowedRho_power_ratio_tendsto atTop A.lo A.hi A.hlo A.hlt
    (fun n : ℝ => (Real.log n)^(-2 : ℝ)) (fun n => frequency n A.theta A.tau)
    logarithmicMargin_tendsto_zero (frequencyTimesMargin_tendsto_zero A.theta A.tau A.theta_pos A.hhalf A.tau_pos)
  have hhalf := hr.eventually_const_le (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [hp,hhalf,S.amplitude_bounds] with n hp hr hab
  have hρ := Upper.intervalRho_pos A.lo A.hi A.hlo A.hlt
  have heq : S.gap n = (S.Au n*S.Av n*Real.exp (-A.tau*frequency n A.theta A.tau))*
      (Upper.narrowedRho A.lo A.hi ((Real.log n)^(-2 : ℝ))^(frequency n A.theta A.tau)/
        Upper.intervalRho A.lo A.hi^(frequency n A.theta A.tau)) := by
    rw [← intervalRho_pow_eq_exp_tau A.lo A.hi A.hlo A.hlt]
    unfold gap
    field_simp [pow_ne_zero _ hρ.ne']
  rw [heq]
  calc
    _ = (1/2 : ℝ)*((A.epsilonU*A.epsilonV*separationConstant A.theta A.tau A.c0/2)*
        (S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) := by unfold gapConstant; ring
    _ ≤ (1/2 : ℝ)*(S.Au n*S.Av n*Real.exp (-A.tau*frequency n A.theta A.tau)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hr (mul_pos (mul_pos hab.1 hab.2.1) (Real.exp_pos _)).le using 1; ring

theorem gap_eventually_pos (S : AbstractScaleChoice A) : ∀ᶠ n : ℝ in atTop, 0 < S.gap n := by
  filter_upwards [S.gap_eventually_lower,S.hmpos,eventually_gt_atTop (1 : ℝ)] with n hg hm hn
  exact (mul_pos (mul_pos (gapConstant_pos A) (pow_pos (zero_lt_one.trans_le hm) _))
    (RoughRegime.Rates.scale_pos n A.theta A.tau hn)).trans_le hg

theorem prior_variance_ratio_tendsto_zero (S : AbstractScaleChoice A) :
    Tendsto (fun n : ℝ => (1/(S.B n : ℝ))/(S.gap n)^2) atTop (nhds 0) := by
  have hB := (S.block_superlog 0).eventually_ge_atTop 1
  simp only [Real.rpow_zero,mul_one] at hB
  have hl := subcritical_testing_scale_tendsto A.theta A.tau A.hhalf
  have hlim := (tendsto_inv_atTop_zero.comp hl).const_mul (gapConstant A^2)⁻¹
  simp only [mul_zero] at hlim
  apply squeeze_zero' (g := fun n : ℝ => (gapConstant A^2)⁻¹*(n*RoughRegime.Rates.subcriticalScale n A.theta A.tau^2)⁻¹) _ _ hlim
  · exact Eventually.of_forall (fun n => by positivity)
  · filter_upwards [S.gap_eventually_lower,S.hmpos,hB,eventually_gt_atTop (1 : ℝ)] with n hg hm hb hn
    have hnp : 0 < n := zero_lt_one.trans hn
    have hs := RoughRegime.Rates.scale_pos n A.theta A.tau hn
    have hc := gapConstant_pos A
    have hBn : n ≤ (S.B n : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hnp).mp hb
    have hbase : gapConstant A*RoughRegime.Rates.subcriticalScale n A.theta A.tau ≤ S.gap n := by
      apply (show gapConstant A*RoughRegime.Rates.subcriticalScale n A.theta A.tau ≤
          gapConstant A*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau from ?_).trans hg
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc.le (one_le_pow₀ hm)) hs.le
    have hsquare : gapConstant A^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau^2 ≤ (S.gap n)^2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (mul_pos hc hs).le hbase 2
    have hden := mul_le_mul hBn hsquare (by positivity) (hnp.trans_le hBn).le
    calc
      _ = 1/((S.B n : ℝ)*(S.gap n)^2) := by rw [div_div]
      _ ≤ 1/(n*(gapConstant A^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau^2)) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by ring

theorem scaled_prior_variance_ratio_tendsto_zero (S : AbstractScaleChoice A) (Cvar cgap : ℝ) (hcgap : cgap ≠ 0) :
    Tendsto (fun n : ℝ => (Cvar/(S.B n : ℝ))/(cgap*S.gap n)^2) atTop (nhds 0) := by
  have he := S.prior_variance_ratio_tendsto_zero.const_mul (Cvar/cgap^2)
  simp only [mul_zero] at he
  apply Filter.Tendsto.congr' _ he
  exact Eventually.of_forall (fun n => by field_simp [hcgap])

theorem Taylor_error_ratio_tendsto_zero (S : AbstractScaleChoice A) (Cerror : ℝ) :
    Tendsto (fun n : ℝ => Cerror*S.Au n*S.Av n*((S.Au n)^2+(S.Av n)^2)/S.gap n) atTop (nhds 0) := by
  have hu : ∀ᶠ n in atTop, |S.Au n| ≤ n^(-A.a) := S.amplitude_bounds.mono (fun _ h => h.2.2.2.2.1)
  have hv : ∀ᶠ n in atTop, |S.Av n| ≤ n^(-A.b) := S.amplitude_bounds.mono (fun _ h => h.2.2.2.2.2)
  have he := (nonlinear_remainder_ratio_tendsto A.theta A.tau A.a A.b A.lo A.hi
    A.theta_pos A.hhalf A.tau_pos A.ha A.hb A.hlo A.hlt S.Au S.Av hu hv).const_mul Cerror
  simp only [mul_zero] at he
  apply Filter.Tendsto.congr' _ he
  filter_upwards [S.amplitude_bounds] with n hn
  unfold gap
  by_cases hρ : Upper.narrowedRho A.lo A.hi ((Real.log n)^(-2 : ℝ))^(frequency n A.theta A.tau) = 0
  · simp only [hρ,mul_zero,div_zero]
  · field_simp [hn.1.ne',hn.2.1.ne',hρ]

end AbstractScaleChoice
end RoughRegime.ReductionScales
