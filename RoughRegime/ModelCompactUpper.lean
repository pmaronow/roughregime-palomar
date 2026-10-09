module

public import RoughRegime.ModelCompactUpperCore
public import RoughRegime.CompactModelPolynomialControls
public import RoughRegime.CompactProjectionBias


@[expose] public section
/-! The source compact density-endpoint uniformity assertion. All constants
and tuning are chosen before the endpoint pair, the response space, the
admissible observable functions, and the genuine statistical model. Each
pair retains its original sharp rho, tau and subcritical rate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.LiftVariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem compact_uniform_productEstimator_population_risk
    (A:Parameters)(hαβ:A.α≤A.β)(G:Set (ℝ×ℝ))(hG:IsCompact G)
    (hdom:G⊆densityIntervalDomain) :
    ∃Cb Cv Cproj:ℝ,1≤Cb ∧ 1≤Cv ∧ 0<Cproj ∧
      CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj := by
  obtain ⟨Cp,hCp,hcontrols⟩:=compact_uniform_polynomial_controls.{u} A hαβ G hG hdom
  obtain ⟨CoD,hCoD,hobs⟩:=compact_dyadicDesignConstant_bound A (holderOrder A.β) G hG hdom
  let Co:=max CoD (baseDesignConstant A (holderOrder A.β))
  obtain ⟨Cproj,hCproj,hproj⟩:=compact_uniform_projection_telescope_resolution_bias.{u} A hαβ G hG hdom
  let Cv:=varianceConstant (max Cp Co)
  have hCv:1≤Cv:=varianceConstant_ge_one _ (hCp.trans (le_max_left _ _))
  refine ⟨Cp,Cv,Cproj,hCp,hCv,hCproj,?_⟩
  apply compact_productRisk_from_controls.{u} A hαβ G hdom Cp Co Cproj hCp hCproj
  · intro I hI
    exact (hobs I hI).trans (le_max_left _ _)
  · exact le_max_right _ _
  · exact fun I hI=>(hcontrols I hI).1
  · exact fun I hI=>(hcontrols I hI).2
  · exact hproj

/-- Theorem 1(a)'s sharp upper assertion with a common constant and cutoff
for every original density interval in an arbitrary compact admissible set. -/
theorem compact_uniformUpperClaim_ordered (A:Parameters)(hαβ:A.α≤A.β)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  obtain ⟨Cb,Cv,Cproj,hCb,hCv,hCproj,hfinite⟩:=
    compact_uniform_productEstimator_population_risk.{u} A hαβ G hG hdom
  exact compact_uniformUpperClaim_ordered_of_finite A hαβ G hG hdom
    Cb Cv Cproj hCb hCv hCproj hfinite L MW

/-- All smoothness orderings are included; the same common constant remains
before the entire density-endpoint family and the entire observable family. -/
theorem compact_uniformUpperClaim (A:Parameters)(G:Set (ℝ×ℝ))(hG:IsCompact G)
    (hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    CompactUniformUpperClaim.{u} A G hdom L MW := by
  by_cases hαβ:A.α≤A.β
  · exact compact_uniformUpperClaim_ordered A hαβ G hG hdom L MW
  · apply compact_uniformUpperClaim_of_swap A G hdom L MW
    exact compact_uniformUpperClaim_ordered A.swap (le_of_lt (lt_of_not_ge hαβ)) G hG hdom L MW

/-- The literal source basic rate, with common constants on a compact
endpoint family, before all response spaces and all bounded observables. -/
theorem compact_eventual_basic_minimax_ordered (A:Parameters)(hαβ:A.α≤A.β)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B),
      |F.lam|=L→(∀z,|F.W z|≤MW)→minimaxRMSE n (target B F) (modelClass B F)≤
        ENNReal.ofReal (C*((n:ℝ)^(-(1/2:ℝ))+(n:ℝ)^(-A.theta))) := by
  obtain ⟨Cb,Cv,Cproj,hCb,hCv,hCproj,hfinite⟩:=
    compact_uniform_productEstimator_population_risk.{u} A hαβ G hG hdom
  exact compact_eventual_basic_minimax_of_finite A hαβ G hG hdom
    Cb Cv Cproj hCb hCv hCproj hfinite L MW

theorem compact_eventual_basic_minimax (A:Parameters)(G:Set (ℝ×ℝ))(hG:IsCompact G)
    (hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B),
      |F.lam|=L→(∀z,|F.W z|≤MW)→minimaxRMSE n (target B F) (modelClass B F)≤
        ENNReal.ofReal (C*((n:ℝ)^(-(1/2:ℝ))+(n:ℝ)^(-A.theta))) := by
  by_cases hαβ:A.α≤A.β
  · exact compact_eventual_basic_minimax_ordered A hαβ G hG hdom L MW
  · obtain ⟨C,hC,he⟩:=compact_eventual_basic_minimax_ordered A.swap
      (le_of_lt (lt_of_not_ge hαβ)) G hG hdom L MW
    refine ⟨C,hC,he.mono ?_⟩
    intro n hn I hI
    dsimp only
    intro Z mZ F hL hMW
    have ht:=hn I hI Z F.swap hL hMW
    have heq:target (densityParameters A I (hdom hI)).swap F.swap=
        target (densityParameters A I (hdom hI)) F:=funext (target_swap F)
    change minimaxRMSE n (target (densityParameters A I (hdom hI)).swap F.swap)
      (modelClass (densityParameters A I (hdom hI)).swap F.swap)≤_ at ht
    rw [heq,modelClass_swap] at ht
    simpa only [Parameters.swap_theta] using ht

end RoughRegime.Model
