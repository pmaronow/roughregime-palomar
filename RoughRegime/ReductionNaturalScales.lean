module

public import RoughRegime.ReductionAbstractScales
public import RoughRegime.ReductionLogScales


@[expose] public section
/-! Proposition 12's numerical reduction for arbitrary sequences indexed by
the natural sample size. The floor extension is proved admissible and agrees
exactly with the original sequence at each natural sample size. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.ReductionScales
set_option maxHeartbeats 900000

theorem frequency_mono {n N θ τ : ℝ} (hn : 0 < n) (hN : n ≤ N)
    (hθ : 0 < θ) (hθhalf : θ < 1/2) (hτ : 0 < τ) : frequency n θ τ ≤ frequency N θ τ := by
  have hΔ : 0 ≤ θ*(1-2*θ) := by nlinarith
  have hi : idealFrequency n θ τ ≤ idealFrequency N θ τ := by
    unfold idealFrequency
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log hn hN) hΔ) hτ.le)
  unfold frequency nearestEven
  exact Nat.mul_le_mul_left 2 (Nat.floor_mono (by linarith))

structure NaturalScaleChoice (A : AbstractScaleParameters) where
  R : ℕ → ℝ
  m : ℕ → ℝ
  hRpos : ∀ᶠ n in atTop, 1 ≤ R n
  hmpos : ∀ᶠ n in atTop, 1 ≤ m n
  hR : (fun n : ℕ => Real.log (R n)) =O[atTop] (fun n => Real.log (frequency n A.theta A.tau))
  hmM : ∀ᶠ n in atTop, m n ≤ A.cstar*frequency n A.theta A.tau
  hma : ∀ᶠ n in atTop, m n ≤ (R n)^A.a
  hmb : ∀ᶠ n in atTop, m n ≤ (R n)^A.b

namespace NaturalScaleChoice
variable {A : AbstractScaleParameters}

def realExtension (S : NaturalScaleChoice A) : AbstractScaleChoice A where
  R := fun n => S.R (Nat.floor n)
  m := fun n => S.m (Nat.floor n)
  hRpos := tendsto_nat_floor_atTop.eventually S.hRpos
  hmpos := tendsto_nat_floor_atTop.eventually S.hmpos
  hma := tendsto_nat_floor_atTop.eventually S.hma
  hmb := tendsto_nat_floor_atTop.eventually S.hmb
  hmM := by
    filter_upwards [tendsto_nat_floor_atTop.eventually S.hmM,
      (tendsto_nat_floor_atTop : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop).eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with n hm hn hnp
    have hfloorp : (0 : ℝ) < Nat.floor n := by exact_mod_cast hn
    exact hm.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast frequency_mono hfloorp (Nat.floor_le hnp.le) A.theta_pos A.hhalf A.tau_pos) A.hcstar.le)
  hR := by
    have hMf := (frequency_tendsto A.theta A.tau A.theta_pos A.hhalf A.tau_pos).comp
      ((tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp
        (tendsto_nat_floor_atTop : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop))
    have hbound : (fun n : ℝ => Real.log (frequency (Nat.floor n) A.theta A.tau)) =O[atTop]
        (fun n => Real.log (frequency n A.theta A.tau)) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [hMf.eventually_ge_atTop 1,
        (tendsto_nat_floor_atTop : Tendsto (Nat.floor : ℝ → ℕ) atTop atTop).eventually_ge_atTop 1,
        eventually_gt_atTop (0 : ℝ)] with n hMf hnf hn
      have hfloorp : (0 : ℝ) < Nat.floor n := by exact_mod_cast hnf
      have hM : frequency (Nat.floor n) A.theta A.tau ≤ frequency n A.theta A.tau :=
        frequency_mono hfloorp (Nat.floor_le hn.le) A.theta_pos A.hhalf A.tau_pos
      have hMcast : (frequency (Nat.floor n) A.theta A.tau : ℝ) ≤ frequency n A.theta A.tau := by exact_mod_cast hM
      have hlogf : 0 ≤ Real.log (frequency (Nat.floor n) A.theta A.tau) := Real.log_nonneg hMf
      have hlog : 0 ≤ Real.log (frequency n A.theta A.tau) := Real.log_nonneg (hMf.trans hMcast)
      simp only [Real.norm_eq_abs,abs_of_nonneg hlogf,abs_of_nonneg hlog,one_mul]
      exact Real.log_le_log (zero_lt_one.trans_le hMf) hMcast
    exact (S.hR.comp_tendsto tendsto_nat_floor_atTop).trans hbound

@[simp] theorem realExtension_R_nat (S : NaturalScaleChoice A) (n : ℕ) : S.realExtension.R n = S.R n := by
  simp only [realExtension,Nat.floor_natCast]
@[simp] theorem realExtension_m_nat (S : NaturalScaleChoice A) (n : ℕ) : S.realExtension.m n = S.m n := by
  simp only [realExtension,Nat.floor_natCast]

abbrev B (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.B n
abbrev Lambda (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.Lambda n
abbrev Au (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.Au n
abbrev Av (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.Av n
abbrev gap (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.gap n
abbrev rawI (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.rawI n
abbrev poissonMajorant (S : NaturalScaleChoice A) (n : ℕ) := S.realExtension.poissonMajorant n

theorem B_eq_selected (S : NaturalScaleChoice A) (n : ℕ) :
    S.B n = blockCount n (S.R n) (logResolution n A.theta A.tau A.c0) A.d := by
  simp only [B,AbstractScaleChoice.B,selectedBlockCount,realExtension_R_nat]

theorem Au_eq (S : NaturalScaleChoice A) (n : ℕ) : S.Au n = amplitude A.epsilonU (S.B n) (S.R n) A.a (S.m n) := by
  simp only [Au,AbstractScaleChoice.Au,realExtension_R_nat,realExtension_m_nat]
theorem Av_eq (S : NaturalScaleChoice A) (n : ℕ) : S.Av n = amplitude A.epsilonV (S.B n) (S.R n) A.b (S.m n) := by
  simp only [Av,AbstractScaleChoice.Av,realExtension_R_nat,realExtension_m_nat]

theorem Lambda_eq (S : NaturalScaleChoice A) (n : ℕ) : S.Lambda n = 2*A.v0*(n : ℝ)/(S.B n : ℝ) := by
  unfold Lambda AbstractScaleChoice.Lambda blockInflation
  rw [div_div_eq_mul_div]

theorem gap_eq (S : NaturalScaleChoice A) (n : ℕ) : S.gap n = S.Au n*S.Av n*
    Upper.narrowedRho A.lo A.hi ((Real.log n)^(-2 : ℝ))^(frequency n A.theta A.tau) := rfl

theorem rawI_eq_physical (S : NaturalScaleChoice A) (n : ℕ) (hn : 0 < n) (hR : 0 < S.R n) :
    S.rawI n = (S.B n : ℝ)*(S.Lambda n)^2*(S.Au n)^2*(S.Av n)^2*
      (S.R n)^(1-(frequency n A.theta A.tau : ℝ))*Real.exp (A.CE*frequency n A.theta A.tau)*
      (A.Cstar*A.CΓ*S.Lambda n)^(frequency n A.theta A.tau)/(frequency n A.theta A.tau).factorial := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simpa only [realExtension_R_nat] using S.realExtension.rawI_eq_physical n hn'
    (by simpa only [realExtension_R_nat] using hR)

theorem poissonMajorant_eq (S : NaturalScaleChoice A) (n : ℕ) :
    S.poissonMajorant n = A.Cstar*A.CΓ*S.rawI n*
      Real.exp (A.CΓ*A.Cstar*S.Lambda n*(S.R n)^Real.sqrt (frequency n A.theta A.tau))+
      S.rawI n*remainderRatio A.Cstar (S.Lambda n) (S.Au n) (S.Av n) (S.R n) A.CE A.CΓ (frequency n A.theta A.tau) := by
  simp only [poissonMajorant,AbstractScaleChoice.poissonMajorant,realExtension_R_nat]

theorem block_superlog (S : NaturalScaleChoice A) (q : ℝ) :
    Tendsto (fun n : ℕ => (S.B n : ℝ)/((n : ℝ)*(Real.log n)^q)) atTop atTop :=
  (S.realExtension.block_superlog q).comp tendsto_natCast_atTop_atTop

theorem amplitude_bounds (S : NaturalScaleChoice A) :
    ∀ᶠ n : ℕ in atTop, 0 < S.Au n ∧ 0 < S.Av n ∧
      S.Au n ≤ A.epsilonU*(S.B n : ℝ)^(-A.a) ∧ S.Av n ≤ A.epsilonV*(S.B n : ℝ)^(-A.b) ∧
      |S.Au n| ≤ (n : ℝ)^(-A.a) ∧ |S.Av n| ≤ (n : ℝ)^(-A.b) :=
  tendsto_natCast_atTop_atTop.eventually S.realExtension.amplitude_bounds

theorem Au_tendsto_zero (S : NaturalScaleChoice A) : Tendsto S.Au atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => (n : ℝ)^(-A.a))
    (S.amplitude_bounds.mono (fun _ h => h.1.le))
    (S.amplitude_bounds.mono (fun _ h => (le_abs_self _).trans h.2.2.2.2.1))
  exact (tendsto_rpow_neg_atTop A.ha).comp tendsto_natCast_atTop_atTop

theorem Av_tendsto_zero (S : NaturalScaleChoice A) : Tendsto S.Av atTop (nhds 0) := by
  apply squeeze_zero' (g := fun n : ℕ => (n : ℝ)^(-A.b))
    (S.amplitude_bounds.mono (fun _ h => h.2.1.le))
    (S.amplitude_bounds.mono (fun _ h => (le_abs_self _).trans h.2.2.2.2.2))
  exact (tendsto_rpow_neg_atTop A.hb).comp tendsto_natCast_atTop_atTop

theorem amplitude_small_budget (S : NaturalScaleChoice A) (C budget : ℝ) (hbudget : 0 < budget) :
    ∀ᶠ n : ℕ in atTop, C*(S.Au n+S.Av n) ≤ budget := by
  have he := (S.Au_tendsto_zero.add S.Av_tendsto_zero).const_mul C
  simp only [zero_add,mul_zero] at he
  exact he.eventually_le_const hbudget

theorem log_block_linear_isBigO (S : NaturalScaleChoice A) :
    (fun n : ℕ => Real.log ((S.B n : ℝ)/n)-(A.tau/A.theta)*frequency n A.theta A.tau) =O[atTop]
      (fun n => Real.log (frequency n A.theta A.tau)) := by
  exact (log_blockInflation_linear_isBigO A.theta A.tau A.c0 A.theta_pos A.hhalf A.tau_pos
    S.realExtension.R S.realExtension.hRpos S.realExtension.hR A.d A.hd).comp_tendsto tendsto_natCast_atTop_atTop

theorem log_Lambda_linear_isBigO (S : NaturalScaleChoice A) :
    (fun n : ℕ => Real.log (S.Lambda n)+(A.tau/A.theta)*frequency n A.theta A.tau) =O[atTop]
      (fun n => Real.log (frequency n A.theta A.tau)) := by
  exact (log_lambda_linear_isBigO A.theta A.tau A.c0 A.v0 A.theta_pos A.hhalf A.tau_pos A.hv
    S.realExtension.R S.realExtension.hRpos S.realExtension.hR A.d A.hd).comp_tendsto tendsto_natCast_atTop_atTop

theorem poissonMajorant_tendsto_zero (S : NaturalScaleChoice A) : Tendsto S.poissonMajorant atTop (nhds 0) :=
  S.realExtension.poissonMajorant_tendsto_zero.comp tendsto_natCast_atTop_atTop

theorem gap_eventually_lower (S : NaturalScaleChoice A) :
    ∀ᶠ n : ℕ in atTop, AbstractScaleChoice.gapConstant A*(S.m n)^2*
      RoughRegime.Rates.subcriticalScale n A.theta A.tau ≤ S.gap n := by
  simpa only [realExtension_m_nat] using tendsto_natCast_atTop_atTop.eventually S.realExtension.gap_eventually_lower

theorem gap_eventually_pos (S : NaturalScaleChoice A) : ∀ᶠ n : ℕ in atTop, 0 < S.gap n :=
  tendsto_natCast_atTop_atTop.eventually S.realExtension.gap_eventually_pos

theorem scaled_prior_variance_ratio_tendsto_zero (S : NaturalScaleChoice A) (Cvar cgap : ℝ) (hcgap : cgap ≠ 0) :
    Tendsto (fun n : ℕ => (Cvar/(S.B n : ℝ))/(cgap*S.gap n)^2) atTop (nhds 0) :=
  (S.realExtension.scaled_prior_variance_ratio_tendsto_zero Cvar cgap hcgap).comp tendsto_natCast_atTop_atTop

theorem Taylor_error_ratio_tendsto_zero (S : NaturalScaleChoice A) (Cerror : ℝ) :
    Tendsto (fun n : ℕ => Cerror*S.Au n*S.Av n*((S.Au n)^2+(S.Av n)^2)/S.gap n) atTop (nhds 0) :=
  (S.realExtension.Taylor_error_ratio_tendsto_zero Cerror).comp tendsto_natCast_atTop_atTop

theorem gap_minus_Taylor_eventually_lower (S : NaturalScaleChoice A)
    (clead Cerror : ℝ) (hclead : 0 < clead) :
    ∀ᶠ n : ℕ in atTop, (clead/2)*S.gap n ≤
      clead*S.gap n-Cerror*S.Au n*S.Av n*((S.Au n)^2+(S.Av n)^2) := by
  have he := (S.Taylor_error_ratio_tendsto_zero Cerror).eventually_le_const (by linarith : (0 : ℝ) < clead/2)
  filter_upwards [he,S.gap_eventually_pos] with n he hg
  have he' := (div_le_iff₀ hg).mp he
  linarith

theorem prior_variance_eventually_budget (S : NaturalScaleChoice A)
    (Cvar cgap budget : ℝ) (hcgap : 0 < cgap) (hbudget : 0 < budget) :
    ∀ᶠ n : ℕ in atTop, Cvar/(S.B n : ℝ) ≤ budget*(cgap*S.gap n)^2 := by
  have he := (S.scaled_prior_variance_ratio_tendsto_zero Cvar cgap hcgap.ne').eventually_le_const hbudget
  filter_upwards [he,S.gap_eventually_pos] with n he hg
  exact (div_le_iff₀ (pow_pos (mul_pos hcgap hg) _)).mp he

end NaturalScaleChoice
end RoughRegime.ReductionScales
