module

public import RoughRegime.BracketRateConsequences


@[expose] public section
/-! The parametric branch of the introduction's logarithmic refinement.
The rough branch is `Bracket.log_refinement`. Both refer to the actual
randomized minimax risk, rather than a substituted numerical rate. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace RoughRegime.Rates

theorem tau_eq_log_sqrt_ratio (lo hi:ℝ) :
    tau lo hi=Real.log ((Real.sqrt hi+Real.sqrt lo)/(Real.sqrt hi-Real.sqrt lo)) := by
  rw [tau,←Real.log_inv]
  congr 1
  simp only [rho,inv_div]

theorem intro_correction_identity (d s τ L : ℝ) (hd : 0 < d) (hs : 0 ≤ s)
    (hrough : s ≤ d / 4) (hτ : 0 ≤ τ) :
    kappa (2*s/d) τ*Real.sqrt L=
      (2/d)*Real.sqrt (2*s*(d-4*s)*L*τ) := by
  have hds : 0 ≤ d - 4*s := by linarith
  have hn : 0≤2*s*(d-4*s)*τ := by positivity
  have ha : (2*s/d)*(1-2*(2*s/d))*τ=(2*s*(d-4*s)*τ)/d^2 := by
    field_simp [hd.ne']
    ring
  rw [kappa,ha,Real.sqrt_div hn,Real.sqrt_sq_eq_abs,abs_of_pos hd]
  have he : 2*s*(d-4*s)*L*τ=(2*s*(d-4*s)*τ)*L := by ring
  rw [he,Real.sqrt_mul hn]
  ring

end RoughRegime.Rates

namespace RoughRegime.RateConsequences

theorem parametric_log_of_nat_bracket (R : ℕ → ℝ) (c C : ℝ)
    (hc : 0<c) (hC : 0<C)
    (hb : ∀ᶠ n:ℕ in atTop,
      c*(n:ℝ)^(-(1/2:ℝ))≤R n ∧ R n≤C*(n:ℝ)^(-(1/2:ℝ))) :
    (fun n:ℕ=>Real.log (R n)+(1/2:ℝ)*Real.log n)=O[atTop] (fun _:ℕ=>(1:ℝ)) := by
  apply isBigO_iff.mpr
  refine ⟨|Real.log c|+|Real.log C|,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn0
  have hp : 0<(n:ℝ)^(-(1/2:ℝ)) := Real.rpow_pos_of_pos hnr _
  have hR := (mul_pos hc hp).trans_le hn.1
  have hl := Real.log_le_log (mul_pos hc hp) hn.1
  have hu := Real.log_le_log hR hn.2
  rw [Real.log_mul hc.ne' hp.ne',Real.log_rpow hnr] at hl
  rw [Real.log_mul hC.ne' hp.ne',Real.log_rpow hnr] at hu
  rw [Real.norm_eq_abs,norm_one,mul_one]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log c),abs_nonneg (Real.log C)]
  · linarith [le_abs_self (Real.log C),abs_nonneg (Real.log c)]

end RoughRegime.RateConsequences

namespace RoughRegime.Model

theorem Bracket.intro_real_parametric_bounds {Ω:Type*} [MeasurableSpace Ω]
    {T:ProbabilityMeasure Ω→ℝ} {C:Set (ProbabilityMeasure Ω)}
    {S:BracketParameters} {ν:ℝ} (hbr:Bracket T C S ν) (hcritical:1/2≤S.theta) :
    ∃c K:ℝ,0<c ∧ 0<K ∧ ∀ᶠ n:ℕ in atTop,
      c*(n:ℝ)^(-(1/2:ℝ))≤(minimaxRMSE n T C).toReal ∧
      (minimaxRMSE n T C).toReal≤K*(n:ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨c,hc,n0,_,hl⟩:=hbr.1
  obtain ⟨_,K,hK,n1,_,hu⟩:=hbr.2
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [eventually_ge_atTop n0,eventually_ge_atTop n1,eventually_ge_atTop (3:ℕ)]
    with n hn0 hn1 hn3
  have hn : 0<(n:ℝ) := by exact_mod_cast (by omega:0<n)
  have hp := Real.rpow_pos_of_pos hn (-(1/2:ℝ))
  have hlo := (hl n hn0).1
  have hhi := hu n hn1
  simp only [lowerBracketScale,upperBracketScale,ite_eq_right (not_lt.mpr hcritical)] at hlo hhi
  have hfinite : minimaxRMSE n T C≠⊤ := ne_of_lt (hhi.trans_lt ENNReal.ofReal_lt_top)
  constructor
  · have h := ENNReal.toReal_mono hfinite hlo
    rw [ENNReal.toReal_ofReal (mul_pos hc hp).le] at h
    exact h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hhi
    rw [ENNReal.toReal_ofReal (mul_pos hK hp).le] at h
    exact h

theorem Bracket.parametric_log_refinement {Ω:Type*} [MeasurableSpace Ω]
    {T:ProbabilityMeasure Ω→ℝ} {C:Set (ProbabilityMeasure Ω)}
    {S:BracketParameters} {ν:ℝ} (hbr:Bracket T C S ν) (hcritical:1/2≤S.theta) :
    (fun n:ℕ=>Real.log (minimaxRMSE n T C).toReal+(1/2:ℝ)*Real.log n)
      =O[atTop] (fun _:ℕ=>(1:ℝ)) := by
  obtain ⟨c,K,hc,hK,hb⟩:=hbr.intro_real_parametric_bounds hcritical
  exact RateConsequences.parametric_log_of_nat_bracket _ c K hc hK hb

theorem main_parametric_log_risk (A:Parameters) {Z:Type*} [MeasurableSpace Z]
    (F:Observables Z A) (π:ProbabilityMeasure Z) (r:ℝ)
    (hnd:Nondegenerate A F π) (hr:0<r)
    (C:Set (ProbabilityMeasure (Observation A Z)))
    (hC:localClass A F π r⊆C) (hCM:C⊆modelClass A F) (hcritical:1/2≤A.theta) :
    (fun n:ℕ=>Real.log (minimaxRMSE n (target A F) C).toReal+(1/2:ℝ)*Real.log n)
      =O[atTop] (fun _:ℕ=>(1:ℝ)) :=
  (model_bracket A F π r hnd hr C hC hCM).parametric_log_refinement hcritical

end RoughRegime.Model
