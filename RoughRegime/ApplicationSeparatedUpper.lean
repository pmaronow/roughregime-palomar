module

public import RoughRegime.ApplicationSeparatedMinimax
public import RoughRegime.PilotRateBounds
public import RoughRegime.ModelUpperConsequences


@[expose] public section
/-! The full qualified upper bracket on the literal separated-density MAR
class. Its estimator is the measurable clipped two-block polynomial rule. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace RoughRegime.Applications.SeparatedMAR
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def enlargedBracketParameters (A : Model.Parameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    Model.BracketParameters :=
  (normalizedParameters A ζ hζ hζ1 1 (by norm_num)).bracketParameters

@[simp] theorem enlargedBracketParameters_theta (A : Model.Parameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    (enlargedBracketParameters A ζ hζ hζ1).theta=A.theta := rfl

@[simp] theorem enlargedBracketParameters_lo (A : Model.Parameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    (enlargedBracketParameters A ζ hζ hζ1).lo=(1-ζ)*A.gminus := rfl

@[simp] theorem enlargedBracketParameters_hi (A : Model.Parameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    (enlargedBracketParameters A ζ hζ hζ1).hi=(1+ζ)*A.gplus := rfl

namespace PilotSetup
variable {A : Model.Parameters} {ζ : ℝ} {hζ : 0<ζ} {hζ1 : ζ<1} {hδ : A.δ≤1/2}

theorem parameters_bracketParameters (S : PilotSetup A ζ hζ hζ1 hδ) :
    S.parameters.bracketParameters=enlargedBracketParameters A ζ hζ hζ1 := rfl

theorem parameters_nu (S : PilotSetup A ζ hζ hζ1 hδ) : S.parameters.nu=A.nu := rfl

theorem half_minimax_bound (S : PilotSetup A ζ hζ hζ1 hδ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      Model.minimaxRMSE n (target A.d) (modelClass A)≤
        ENNReal.ofReal (C*Model.upperBracketScale S.parameters.bracketParameters
          (S.parameters.nu:ℝ) (n-n/2)+Real.sqrt (S.c⁻¹*Real.exp (-S.c*(n/2:ℕ)))) := by
  by_cases hrough : S.parameters.theta<1/2
  · obtain ⟨C,hC,he⟩ := S.subcriticalHalf_minimax_bound hrough
    refine ⟨C,hC,?_⟩
    filter_upwards [he,eventually_ge_atTop (4:ℕ)] with n hn hn4
    have hm : (1:ℝ)<(n-n/2:ℕ) := by exact_mod_cast (show 1<n-n/2 by omega)
    have hr := UpperSubcritical.rate_eq_paper_scale (n-n/2:ℕ) S.parameters.theta
      (Rates.tau S.parameters.gminus S.parameters.gplus) S.parameters.nu hm
    simpa only [Model.upperBracketScale,Model.Parameters.bracketParameters,ite_eq_left hrough,hr,mul_assoc] using hn
  · obtain ⟨C,hC,he⟩ := S.parametricHalf_minimax_bound (le_of_not_gt hrough)
    refine ⟨C,hC,?_⟩
    filter_upwards [he] with n hn
    have hp : ((n-n/2:ℕ):ℝ)^(-(1/2:ℝ))=1/Real.sqrt (n-n/2:ℕ) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _) (1/2),←Real.sqrt_eq_rpow]
      simp only [one_div]
    simpa only [Model.upperBracketScale,Model.Parameters.bracketParameters,ite_eq_right hrough,hp,mul_one_div] using hn

theorem upperBracket (S : PilotSetup A ζ hζ hζ1 hδ) :
    Model.UpperBracket (target A.d) (modelClass A)
      (enlargedBracketParameters A ζ hζ hζ1) (A.nu:ℝ) := by
  obtain ⟨C,hC,he⟩ := S.half_minimax_bound
  let K := C*halfRateConstant S.parameters.theta (Rates.tau S.parameters.gminus S.parameters.gplus)+1
  have hK : 0<K := by
    dsimp only [K]
    exact add_pos (mul_pos hC (halfRateConstant_pos _ _)) zero_lt_one
  have hb := sqrt_pilot_tail_eventually_le_upperBracketScale S.parameters.bracketParameters
    (S.parameters.nu:ℝ) S.c S.hc
  have hbound : ∀ᶠ n : ℕ in atTop,
      Model.minimaxRMSE n (target A.d) (modelClass A)≤
        ENNReal.ofReal (K*Model.upperBracketScale S.parameters.bracketParameters (S.parameters.nu:ℝ) n) := by
    filter_upwards [he,hb,eventually_ge_atTop (4:ℕ)] with n hn hbad hn4
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    have hhalf := upperBracketScale_estimation_half_bound S.parameters.bracketParameters
      (S.parameters.nu:ℝ) (by exact_mod_cast (Nat.zero_le _)) n hn4
    calc
      _ ≤ C*(halfRateConstant S.parameters.theta (Rates.tau S.parameters.gminus S.parameters.gplus)*
          Model.upperBracketScale S.parameters.bracketParameters (S.parameters.nu:ℝ) n)+
            Model.upperBracketScale S.parameters.bracketParameters (S.parameters.nu:ℝ) n :=
        add_le_add (mul_le_mul_of_nonneg_left hhalf hC.le) hbad
      _ = _ := by dsimp only [K,Model.Parameters.bracketParameters]; ring
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hbound
  refine ⟨by exact_mod_cast A.nu_ge_two,K,hK,max 3 n0,le_max_left _ _,?_⟩
  intro n hn
  have hh := hn0 n ((le_max_right _ _).trans hn)
  rw [S.parameters_bracketParameters,S.parameters_nu] at hh
  exact hh

end PilotSetup

theorem Witness.delta_le_half (A : Model.Parameters)
    (P : ProbabilityMeasure (Model.Covariate A.d×Response)) (W : Witness A P) : A.δ≤1/2 := by
  obtain ⟨x,hx⟩ := W.overlap.exists
  linarith [hx.1,hx.2]

theorem modelClass_empty_of_large_delta (A : Model.Parameters) (hδ : ¬A.δ≤1/2) :
    modelClass A=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨W⟩ := hP
  exact hδ (W.delta_le_half A P)

theorem separated_upperBracket (A : Model.Parameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    Model.UpperBracket (target A.d) (modelClass A)
      (enlargedBracketParameters A ζ hζ hζ1) (A.nu:ℝ) := by
  by_cases hδ : A.δ≤1/2
  · obtain ⟨S⟩ := exists_pilotSetup A ζ hζ hζ1 hδ
    exact S.upperBracket
  · refine ⟨by exact_mod_cast A.nu_ge_two,1,zero_lt_one,3,le_rfl,?_⟩
    intro n _
    rw [modelClass_empty_of_large_delta A hδ,Model.minimaxRMSE_empty]
    exact bot_le

end RoughRegime.Applications.SeparatedMAR
