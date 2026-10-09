module

public import RoughRegime.ModelMainLowerConsequences
public import RoughRegime.RateConsequences


@[expose] public section
/-! Logarithmic consequences of actual minimax brackets on natural sample
sizes, including the original main risk and divergence beyond the common scale. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology
namespace RoughRegime.RateConsequences
open RoughRegime.Rates
theorem log_refinement_of_nat_bracket (R : ℕ → ℝ) (θ τ ν c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ n : ℕ in atTop,
      c * subcriticalScale n θ τ * Real.log n ≤ R n ∧
      R n ≤ C * subcriticalScale n θ τ * (Real.log n) ^ (ν / 2 + 1 / 4)) :
    (fun n ↦ Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n))
      =O[atTop] (fun n ↦ Real.log (Real.log n)) := by
  let a := θ / 2 + 1
  let b := θ / 2 + ν / 2 + 1 / 4
  let M := |Real.log c| + |Real.log C| + |a| + |b|
  apply isBigO_iff.mpr
  refine ⟨M, ?_⟩
  have hloglog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (Real.log n) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually (eventually_ge_atTop 1)
  filter_upwards [hb, eventually_gt_atTop (1 : ℕ), hloglog] with n hn hn1 hll
  have hnr : 1 < (n : ℝ) := by exact_mod_cast hn1
  obtain ⟨hl, hu⟩ := log_bracket n θ τ ν c C (R n) hnr hc hC hn.1 hn.2
  have hlow : Real.log c + a * Real.log (Real.log n) ≤
      Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n) := by
    dsimp [a]
    linarith
  have hupp : Real.log (R n) + θ * Real.log n + kappa θ τ * Real.sqrt (Real.log n) ≤
      Real.log C + b * Real.log (Real.log n) := by
    dsimp [b]
    linarith
  have hL : 0 ≤ Real.log (Real.log n) := by linarith
  have hca : -(|Real.log c| + |a|) * Real.log (Real.log n) ≤
      Real.log c + a * Real.log (Real.log n) := by
    have hc0 := neg_abs_le (Real.log c)
    have ha0 := neg_abs_le a
    nlinarith [abs_nonneg (Real.log c),
      mul_le_mul_of_nonneg_right ha0 hL]
  have hCb : Real.log C + b * Real.log (Real.log n) ≤
      (|Real.log C| + |b|) * Real.log (Real.log n) := by
    have hc0 := le_abs_self (Real.log C)
    have hb0 := le_abs_self b
    nlinarith [abs_nonneg (Real.log C),
      mul_le_mul_of_nonneg_right hb0 hL]
  have hMa : |Real.log c| + |a| ≤ M := by
    dsimp [M]
    linarith [abs_nonneg (Real.log C), abs_nonneg b]
  have hMb : |Real.log C| + |b| ≤ M := by
    dsimp [M]
    linarith [abs_nonneg (Real.log c), abs_nonneg a]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL]
  apply abs_le.mpr
  constructor
  · nlinarith [hlow, hca, mul_le_mul_of_nonneg_right hMa hL]
  · exact hupp.trans (hCb.trans (mul_le_mul_of_nonneg_right hMb hL))

theorem nat_scale_ratio_diverges (R : ℕ → ℝ) (θ τ c : ℝ) (hc : 0 < c)
    (hl : ∀ᶠ n : ℕ in atTop, c * subcriticalScale n θ τ * Real.log n ≤ R n) :
    Tendsto (fun n ↦ R n / subcriticalScale n θ τ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hlog : ∀ᶠ n : ℕ in atTop, B / c ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (B / c))
  filter_upwards [hl, eventually_gt_atTop (1 : ℕ), hlog] with n hn hn1 hln
  have hnr : 1 < (n : ℝ) := by exact_mod_cast hn1
  have hs := scale_pos n θ τ hnr
  have hBc : B ≤ c * Real.log n := by
    exact (div_le_iff₀ hc).mp hln |>.trans_eq (mul_comm _ _)
  apply (le_div_iff₀ hs).mpr
  calc
    B * subcriticalScale n θ τ ≤ c * Real.log n * subcriticalScale n θ τ :=
      mul_le_mul_of_nonneg_right hBc hs.le
    _ = c * subcriticalScale n θ τ * Real.log n := by ring
    _ ≤ R n := hn

end RoughRegime.RateConsequences

namespace RoughRegime.Model

theorem Bracket.real_subcritical_bounds {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hbr : Bracket T C S ν) (hrough : S.theta<1/2) :
    ∃ c K : ℝ,0<c ∧ 0<K ∧ ∀ᶠ n : ℕ in atTop,
      c*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)*Real.log n≤(minimaxRMSE n T C).toReal ∧
      (minimaxRMSE n T C).toReal≤K*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)*
        (Real.log n)^(ν/2+1/4) := by
  obtain ⟨c,hc,n0,_,hl⟩ := hbr.1
  obtain ⟨_,K,hK,n1,_,hu⟩ := hbr.2
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [eventually_ge_atTop n0,eventually_ge_atTop n1,eventually_ge_atTop (3:ℕ)]
    with n hn0 hn1 hn3
  have hn : 1<(n:ℝ) := by exact_mod_cast (by omega : 1<n)
  have hs := Rates.scale_pos n S.theta (Rates.tau S.lo S.hi) hn
  have hlo := (hl n hn0).1
  have hhi := hu n hn1
  simp only [lowerBracketScale,upperBracketScale,if_pos hrough] at hlo hhi
  have hfinite : minimaxRMSE n T C≠⊤ := ne_of_lt (hhi.trans_lt ENNReal.ofReal_lt_top)
  have hpL : 0≤c*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)*Real.log n :=
    (mul_pos (mul_pos hc hs) (Real.log_pos hn)).le
  have hpU : 0≤K*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)*(Real.log n)^(ν/2+1/4) :=
    (mul_pos (mul_pos hK hs) (Real.rpow_pos_of_pos (Real.log_pos hn) _)).le
  constructor
  · have h := ENNReal.toReal_mono hfinite hlo
    rw [←mul_assoc,ENNReal.toReal_ofReal hpL] at h
    exact h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hhi
    rw [←mul_assoc,ENNReal.toReal_ofReal hpU] at h
    exact h

theorem Bracket.log_refinement {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hbr : Bracket T C S ν) (hrough : S.theta<1/2) :
    (fun n : ℕ => Real.log (minimaxRMSE n T C).toReal+S.theta*Real.log n+
      Rates.kappa S.theta (Rates.tau S.lo S.hi)*Real.sqrt (Real.log n))
      =O[atTop] (fun n : ℕ => Real.log (Real.log n)) := by
  obtain ⟨c,K,hc,hK,hb⟩ := hbr.real_subcritical_bounds hrough
  exact RateConsequences.log_refinement_of_nat_bracket _ S.theta (Rates.tau S.lo S.hi) ν c K hc hK hb

theorem Bracket.scale_ratio_diverges {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hbr : Bracket T C S ν) (hrough : S.theta<1/2) :
    Tendsto (fun n : ℕ => (minimaxRMSE n T C).toReal/
      Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)) atTop atTop := by
  obtain ⟨c,K,hc,hK,hb⟩ := hbr.real_subcritical_bounds hrough
  exact RateConsequences.nat_scale_ratio_diverges _ _ _ c hc (hb.mono (fun _ h=>h.1))

theorem main_log_risk (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
    (hnd : Nondegenerate A F π) (hr : 0<r)
    (C : Set (ProbabilityMeasure (Observation A Z)))
    (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F) (hrough : A.theta<1/2) :
    (fun n : ℕ => Real.log (minimaxRMSE n (target A F) C).toReal+A.theta*Real.log n+
      Rates.kappa A.theta (Rates.tau A.gminus A.gplus)*Real.sqrt (Real.log n))
      =O[atTop] (fun n : ℕ => Real.log (Real.log n)) :=
  (model_bracket A F π r hnd hr C hC hCM).log_refinement hrough

theorem main_scale_ratio_diverges (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
    (hnd : Nondegenerate A F π) (hr : 0<r)
    (C : Set (ProbabilityMeasure (Observation A Z)))
    (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F) (hrough : A.theta<1/2) :
    Tendsto (fun n : ℕ => (minimaxRMSE n (target A F) C).toReal/
      Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)) atTop atTop :=
  (model_bracket A F π r hnd hr C hC hCM).scale_ratio_diverges hrough

end RoughRegime.Model
