module

public import RoughRegime.ModelPredicates
public import RoughRegime.RateConsequences


@[expose] public section
/-! The logarithmic assertion for separated-density classes.  Bounds for every
fixed enlarged density interval are first squeezed numerically, then applied
to the actual extended-real minimax risk. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace RoughRegime.RateConsequences
open RoughRegime.Rates

lemma loglog_nat_isLittleO_sqrtlog :
    (fun n : ℕ => Real.log (Real.log n)) =o[atTop]
      (fun n : ℕ => Real.sqrt (Real.log n)) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp_tendsto
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, ← Real.sqrt_eq_rpow] using h

lemma affine_loglog_nat_isLittleO_sqrtlog (c a : ℝ) :
    (fun n : ℕ => c+a*Real.log (Real.log n)) =o[atTop]
      (fun n : ℕ => Real.sqrt (Real.log n)) := by
  have hconst : (fun _ : ℕ => c) =o[atTop]
      (fun n : ℕ => Real.sqrt (Real.log n)) := by
    apply isLittleO_const_left.mpr
    right
    change Tendsto (fun n : ℕ => |Real.sqrt (Real.log n)|) atTop atTop
    simpa only [Function.comp_def, abs_of_nonneg (Real.sqrt_nonneg _)] using
      (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  exact hconst.add (loglog_nat_isLittleO_sqrtlog.const_mul_left a)

theorem log_littleO_of_enlarged_brackets (R : ℕ → ℝ) (θ τ ν c : ℝ)
    (hc : 0<c) (τ' : ℝ → ℝ) (hτ : ContinuousAt τ' 0) (hτ0 : τ' 0=τ)
    (hl : ∀ᶠ n : ℕ in atTop,
      c*subcriticalScale n θ τ*Real.log n ≤ R n)
    (hu : ∀ ζ : ℝ, 0<ζ → ζ<1 → ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      R n ≤ K*subcriticalScale n θ (τ' ζ)*(Real.log n)^(ν/2+1/4)) :
    (fun n : ℕ => Real.log (R n)+θ*Real.log n+kappa θ τ*Real.sqrt (Real.log n))
      =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  apply isLittleO_iff.mpr
  intro ε hε
  have hκ : ContinuousAt (fun ζ => kappa θ (τ' ζ)) 0 := by
    unfold kappa
    exact continuousAt_const.mul ((continuousAt_const.mul hτ).sqrt)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hκ (ε/2) (by positivity)
  let ζ := min (δ/2) (1/2)
  have hζ : 0<ζ := lt_min (by positivity) (by norm_num)
  have hζ1 : ζ<1 := (min_le_right _ _).trans_lt (by norm_num)
  have hζδ : ζ<δ := (min_le_left _ _).trans_lt (by linarith)
  have hκclose : |kappa θ (τ' ζ)-kappa θ τ|<ε/2 := by
    have h := hclose (x:=ζ) (by simpa [Real.dist_eq,abs_of_pos hζ] using hζδ)
    simpa only [Real.dist_eq,hτ0] using h
  obtain ⟨K,hK,hU⟩ := hu ζ hζ hζ1
  have hsmallL := (affine_loglog_nat_isLittleO_sqrtlog (Real.log c) (θ/2+1)).bound
    (by positivity : 0<ε/2)
  have hsmallU := (affine_loglog_nat_isLittleO_sqrtlog (Real.log K) (θ/2+ν/2+1/4)).bound
    (by positivity : 0<ε/2)
  filter_upwards [hl,hU,hsmallL,hsmallU,eventually_gt_atTop (1:ℕ)] with n hL hU hSL hSU hn
  have hnR : 1<(n:ℝ) := by exact_mod_cast hn
  have hln := Real.log_pos hnR
  have hs := scale_pos n θ τ hnR
  have hs' := scale_pos n θ (τ' ζ) hnR
  have hR : 0<R n := lt_of_lt_of_le (mul_pos (mul_pos hc hs) hln) hL
  have hlogL := Real.log_le_log (mul_pos (mul_pos hc hs) hln) hL
  rw [Real.log_mul (mul_pos hc hs).ne' hln.ne',
    Real.log_mul hc.ne' hs.ne',log_scale n θ τ hnR] at hlogL
  have hlogU := Real.log_le_log hR hU
  rw [Real.log_mul (mul_pos hK hs').ne' (Real.rpow_pos_of_pos hln _).ne',
    Real.log_mul hK.ne' hs'.ne',log_scale n θ (τ' ζ) hnR,Real.log_rpow hln] at hlogU
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hSL hSU ⊢
  obtain ⟨hSLl,hSLu⟩ := abs_le.mp hSL
  obtain ⟨hSUl,hSUu⟩ := abs_le.mp hSU
  obtain ⟨hκl,hκu⟩ := abs_lt.mp hκclose
  have hsqrt := Real.sqrt_nonneg (Real.log (n:ℝ))
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hκl.le hsqrt]

end RoughRegime.RateConsequences

namespace RoughRegime.Model

/-- The density interval used by the pilot normalization in Corollary 3. -/
def widenedBracketParameters (S : BracketParameters) (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    BracketParameters where
  theta := S.theta
  lo := (1-ζ)*S.lo
  hi := (1+ζ)*S.hi
  htheta := S.htheta
  hlo := mul_pos (by linarith) S.hlo
  hinterval := by
    have hhi := S.hlo.trans S.hinterval
    nlinarith [S.hinterval,mul_pos hζ S.hlo,mul_pos hζ hhi]

lemma widened_tau_continuousAt (S : BracketParameters) :
    ContinuousAt (fun ζ : ℝ => Rates.tau ((1-ζ)*S.lo) ((1+ζ)*S.hi)) 0 := by
  have hl : ContinuousAt (fun ζ : ℝ => Real.sqrt ((1-ζ)*S.lo)) 0 := by fun_prop
  have hh : ContinuousAt (fun ζ : ℝ => Real.sqrt ((1+ζ)*S.hi)) 0 := by fun_prop
  have hden : Real.sqrt ((1+(0:ℝ))*S.hi)+Real.sqrt ((1-(0:ℝ))*S.lo)≠0 := by
    simp only [add_zero,sub_zero,one_mul]
    exact (add_pos (Real.sqrt_pos.mpr (S.hlo.trans S.hinterval))
      (Real.sqrt_pos.mpr S.hlo)).ne'
  have hρ : ContinuousAt (fun ζ : ℝ => Rates.rho ((1-ζ)*S.lo) ((1+ζ)*S.hi)) 0 :=
    (hh.sub hl).div (hh.add hl) hden
  exact (hρ.log (by simpa using (Rates.rho_pos S.lo S.hi S.hlo S.hinterval).ne')).neg

theorem separated_log_risk {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hrough : S.theta<1/2)
    (hl : LowerBracket T C S)
    (hu : ∀ ζ : ℝ, ∀ hζ : 0<ζ, ∀ hζ1 : ζ<1,
      UpperBracket T C (widenedBracketParameters S ζ hζ hζ1) ν) :
    (fun n : ℕ => Real.log (minimaxRMSE n T C).toReal+S.theta*Real.log n+
      Rates.kappa S.theta (Rates.tau S.lo S.hi)*Real.sqrt (Real.log n))
      =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  obtain ⟨c,hc,n0,_,hL⟩ := hl
  have upper : ∀ ζ : ℝ, 0<ζ → ζ<1 → ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      (minimaxRMSE n T C).toReal≤K*Rates.subcriticalScale n S.theta
        (Rates.tau ((1-ζ)*S.lo) ((1+ζ)*S.hi))*(Real.log n)^(ν/2+1/4) := by
    intro ζ hζ hζ1
    obtain ⟨_,K,hK,n1,_,hU⟩ := hu ζ hζ hζ1
    refine ⟨K,hK,?_⟩
    filter_upwards [eventually_ge_atTop n1,eventually_ge_atTop (3:ℕ)] with n hn1 hn3
    have hn : 1<(n:ℝ) := by exact_mod_cast (by omega : 1<n)
    have hs := Rates.scale_pos n S.theta (Rates.tau ((1-ζ)*S.lo) ((1+ζ)*S.hi)) hn
    have h := hU n hn1
    simp only [upperBracketScale,widenedBracketParameters] at h
    rw [if_pos hrough] at h
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [←mul_assoc,ENNReal.toReal_ofReal (mul_pos (mul_pos hK hs)
      (Real.rpow_pos_of_pos (Real.log_pos hn) _)).le] at hh
    exact hh
  obtain ⟨_,_,_,n1,_,hU⟩ := hu (1/2) (by norm_num) (by norm_num)
  have lower : ∀ᶠ n : ℕ in atTop,
      c*Rates.subcriticalScale n S.theta (Rates.tau S.lo S.hi)*Real.log n≤
        (minimaxRMSE n T C).toReal := by
    filter_upwards [eventually_ge_atTop n0,eventually_ge_atTop n1,
      eventually_ge_atTop (3:ℕ)] with n hn0 hn1 hn3
    have hn : 1<(n:ℝ) := by exact_mod_cast (by omega : 1<n)
    have hs := Rates.scale_pos n S.theta (Rates.tau S.lo S.hi) hn
    have hfinite : minimaxRMSE n T C≠⊤ := ne_of_lt ((hU n hn1).trans_lt ENNReal.ofReal_lt_top)
    have h := (hL n hn0).1
    simp only [lowerBracketScale,if_pos hrough] at h
    have hh := ENNReal.toReal_mono hfinite h
    rw [←mul_assoc,ENNReal.toReal_ofReal (mul_pos (mul_pos hc hs) (Real.log_pos hn)).le] at hh
    exact hh
  exact RateConsequences.log_littleO_of_enlarged_brackets _ S.theta (Rates.tau S.lo S.hi) ν c hc
    (fun ζ => Rates.tau ((1-ζ)*S.lo) ((1+ζ)*S.hi)) (widened_tau_continuousAt S)
    (by simp) lower upper

end RoughRegime.Model
