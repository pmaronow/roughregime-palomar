module

public import RoughRegime.SourceTaylorScales


@[expose] public section
/-! Fixed testing budgets for the original selected source scales. These are
consequences of the proved selected-scale limits, with no separation or
concentration estimate supplied as a hypothesis. -/
noncomputable section
open Filter
open scoped Topology
namespace RoughRegime.LatticePriors
open RoughRegime.ReductionScales
set_option maxHeartbeats 800000

def selectedSourceTaylorRemainder (A : Model.Parameters) (d : ℕ)
    (θ τ c0 epsilonU epsilonV C n : ℝ) : ℝ :=
  C * selectedSourceAmplitude A d θ τ c0 epsilonU A.α n *
    selectedSourceAmplitude A d θ τ c0 epsilonV A.β n *
    ((selectedSourceAmplitude A d θ τ c0 epsilonU A.α n)^2 +
     (selectedSourceAmplitude A d θ τ c0 epsilonV A.β n)^2)

theorem selectedSourceGapScale_eventually_pos (A : Model.Parameters) (d : ℕ)
    (θ c0 epsilonU epsilonV lo hi : ℝ) (hεu : 0 < epsilonU) (hεv : 0 < epsilonV)
    (hlo : 0 < lo) (hlt : lo < hi) :
    ∀ᶠ n : ℝ in atTop,
      0 < selectedSourceGapScale A d θ (Rates.tau lo hi) c0 epsilonU epsilonV lo hi n := by
  let τ := Rates.tau lo hi
  have hρ := ((Upper.narrowedRho_differentiableAt lo hi hlo hlt).continuousAt.tendsto.comp
    logarithmicMargin_tendsto_zero).eventually
    (eventually_gt_nhds (by simpa [Upper.narrowedRho] using Upper.intervalRho_pos lo hi hlo hlt))
  filter_upwards [hρ,eventually_gt_atTop (0 : ℝ)] with n hρn hn
  have hR : 0 < selectedSourceVolume A d θ τ n :=
    zero_lt_one.trans_le (selectedSourceVolume_ge_one A d θ τ n)
  have hB : 0 < (selectedBlockCount θ τ c0 (selectedSourceVolume A d θ τ) d n : ℝ) := by
    unfold selectedBlockCount
    exact_mod_cast blockCount_positive n _ _ d hn hR
  have hm : 0 < selectedSourceMultiplier A d θ τ n :=
    zero_lt_one.trans_le (selectedSourceMultiplier_ge_one A d θ τ n)
  have hu : 0 < selectedSourceAmplitude A d θ τ c0 epsilonU A.α n :=
    amplitude_positive epsilonU _ _ _ _ hεu hB hR hm
  have hv : 0 < selectedSourceAmplitude A d θ τ c0 epsilonV A.β n :=
    amplitude_positive epsilonV _ _ _ _ hεv hB hR hm
  exact mul_pos (mul_pos hu hv) (pow_pos hρn _)

theorem selectedSource_gap_minus_Taylor_eventually_lower
    (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
    (θ c0 epsilonU epsilonV lo hi C clead : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1/2)
    (hεu : 0 < epsilonU) (hεu1 : epsilonU ≤ 1)
    (hεv : 0 < epsilonV) (hεv1 : epsilonV ≤ 1)
    (hlo : 0 < lo) (hlt : lo < hi) (hclead : 0 < clead) :
    ∀ᶠ n : ℝ in atTop,
      (clead/2) * selectedSourceGapScale A d θ (Rates.tau lo hi) c0 epsilonU epsilonV lo hi n ≤
      clead * selectedSourceGapScale A d θ (Rates.tau lo hi) c0 epsilonU epsilonV lo hi n -
        selectedSourceTaylorRemainder A d θ (Rates.tau lo hi) c0 epsilonU epsilonV C n := by
  have hlim := selectedSource_scaled_TaylorError_gapRatio_tendsto_zero A d hd θ c0 epsilonU epsilonV
    lo hi C hθ hθhalf hεu hεu1 hεv hεv1 hlo hlt
  have hsmall := hlim.eventually_le_const (show (0 : ℝ) < clead/2 by positivity)
  filter_upwards [hsmall,selectedSourceGapScale_eventually_pos A d θ c0 epsilonU epsilonV lo hi
    hεu hεv hlo hlt] with n hn hp
  change selectedSourceTaylorRemainder A d θ (Rates.tau lo hi) c0 epsilonU epsilonV C n /
    selectedSourceGapScale A d θ (Rates.tau lo hi) c0 epsilonU epsilonV lo hi n ≤ clead/2 at hn
  have hh := (div_le_iff₀ hp).mp hn
  nlinarith

theorem selectedSource_prior_variance_eventually_budget
    (A : Model.Parameters) (d : ℕ) (hd : 0 < d)
    (θ c0 epsilonU epsilonV lo hi Cvar cgap budget : ℝ)
    (hθ : 0 < θ) (hθhalf : θ < 1/2)
    (hεu : 0 < epsilonU) (hεv : 0 < epsilonV) (hlo : 0 < lo) (hlt : lo < hi)
    (hab : A.α/d + A.β/d = θ) (hcgap : 0 < cgap) (hbudget : 0 < budget) :
    ∀ᶠ n : ℝ in atTop,
      Cvar / (selectedBlockCount θ (Rates.tau lo hi) c0
        (selectedSourceVolume A d θ (Rates.tau lo hi)) d n : ℝ) ≤
      budget * (cgap * selectedSourceGapScale A d θ (Rates.tau lo hi) c0 epsilonU epsilonV lo hi n)^2 := by
  have hlim := selectedSource_scaled_prior_variance_ratio_tendsto_zero A d hd θ c0 epsilonU epsilonV
    lo hi Cvar cgap hθ hθhalf hεu hεv hlo hlt hab hcgap.ne'
  filter_upwards [hlim.eventually_le_const hbudget,
    selectedSourceGapScale_eventually_pos A d θ c0 epsilonU epsilonV lo hi hεu hεv hlo hlt]
    with n hn hp
  exact (div_le_iff₀ (pow_pos (mul_pos hcgap hp) 2)).mp hn

end RoughRegime.LatticePriors
