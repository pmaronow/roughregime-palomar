module

public import RoughRegime.BracketRateConsequences
public import RoughRegime.SeparatedLogRisk


@[expose] public section
/-! Polynomial exponents and exclusion of the faster HOIF exponent, for both
proved ordinary brackets and qualified separated-density brackets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace RoughRegime.RateConsequences

lemma sqrtlog_nat_div_log_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log n)/Real.log n) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hs : Real.sqrt (Real.log (n:ℝ))≠0 := (Real.sqrt_pos.mpr hl).ne'
  change (Real.sqrt (Real.log (n:ℝ)))⁻¹=Real.sqrt (Real.log n)/Real.log n
  apply (eq_div_iff hl.ne').mpr
  calc
    _ = (Real.sqrt (Real.log (n:ℝ)))⁻¹*(Real.sqrt (Real.log n))^2 := by rw [Real.sq_sqrt hl.le]
    _ = _ := by field_simp

lemma sqrtlog_nat_isLittleO_log :
    (fun n : ℕ => Real.sqrt (Real.log n)) =o[atTop] (fun n : ℕ => Real.log n) := by
  apply isLittleO_of_tendsto' _ sqrtlog_nat_div_log_tendsto_zero
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn)
  exact fun h => False.elim (hl.ne' h)

theorem polynomial_exponent_of_log_refinement (R : ℕ→ℝ) (θ κ : ℝ)
    (hlog : (fun n : ℕ => Real.log (R n)+θ*Real.log n+κ*Real.sqrt (Real.log n))
      =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n))) :
    Tendsto (fun n : ℕ => Real.log (R n)/Real.log n) atTop (𝓝 (-θ)) := by
  have he := ((hlog.trans sqrtlog_nat_isLittleO_log).sub
    (sqrtlog_nat_isLittleO_log.const_mul_left κ)).tendsto_div_nhds_zero
  have hlim := he.sub_const θ
  norm_num only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  have hl : Real.log (n:ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp [hl]
  <;> ring

theorem parametric_polynomial_exponent (R : ℕ→ℝ) (c K : ℝ) (hc : 0<c) (hK : 0<K)
    (hb : ∀ᶠ n : ℕ in atTop,
      c*(n:ℝ)^(-(1/2:ℝ))≤R n ∧ R n≤K*(n:ℝ)^(-(1/2:ℝ))) :
    Tendsto (fun n : ℕ => Real.log (R n)/Real.log n) atTop (𝓝 (-(1/2:ℝ))) := by
  have hcl := ((Real.isLittleO_const_log_atTop (c:=Real.log c)).comp_tendsto
    tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero.sub_const (1/2)
  have hKl := ((Real.isLittleO_const_log_atTop (c:=Real.log K)).comp_tendsto
    tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero.sub_const (1/2)
  norm_num only [zero_sub] at hcl hKl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcl hKl
  · filter_upwards [hb,eventually_gt_atTop (1:ℕ)] with n hn hn1
    have hnR : 1<(n:ℝ) := by exact_mod_cast hn1
    have hn0 : 0<(n:ℝ) := by linarith
    have hp := Real.rpow_pos_of_pos hn0 (-(1/2:ℝ))
    have hl := Real.log_le_log (mul_pos hc hp) hn.1
    rw [Real.log_mul hc.ne' hp.ne',Real.log_rpow hn0] at hl
    apply (le_div_iff₀ (Real.log_pos hnR)).mpr
    simp only [Function.comp_apply]
    have heq : (Real.log c/Real.log (n:ℝ)-1/2)*Real.log n=
        Real.log c-(1/2)*Real.log n := by field_simp [(Real.log_pos hnR).ne']
    rw [heq]
    linarith
  · filter_upwards [hb,eventually_gt_atTop (1:ℕ)] with n hn hn1
    have hnR : 1<(n:ℝ) := by exact_mod_cast hn1
    have hn0 : 0<(n:ℝ) := by linarith
    have hp := Real.rpow_pos_of_pos hn0 (-(1/2:ℝ))
    have hR : 0<R n := (mul_pos hc hp).trans_le hn.1
    have hu := Real.log_le_log hR hn.2
    rw [Real.log_mul hK.ne' hp.ne',Real.log_rpow hn0] at hu
    apply (div_le_iff₀ (Real.log_pos hnR)).mpr
    simp only [Function.comp_apply]
    have heq : (Real.log K/Real.log (n:ℝ)-1/2)*Real.log n=
        Real.log K-(1/2)*Real.log n := by field_simp [(Real.log_pos hnR).ne']
    rw [heq]
    linarith

theorem not_faster_polynomial_upper (R : ℕ→ℝ) (θ γ K : ℝ)
    (hγ : θ<γ) (hK : 0<K) (hpos : ∀ᶠ n : ℕ in atTop,0<R n)
    (hR : Tendsto (fun n : ℕ => Real.log (R n)/Real.log n) atTop (𝓝 (-θ)))
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) :
    ¬∀ᶠ n : ℕ in atTop,R n≤K*(n:ℝ)^(-γ+e n) := by
  intro hu
  have hKlog := ((Real.isLittleO_const_log_atTop (c:=Real.log K)).comp_tendsto
    tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
  have hdiff := hR.sub ((hKlog.sub_const γ).add he)
  have hpositive : 0 < -θ-((0-γ)+0) := by linarith
  have hev := hdiff.eventually_const_lt hpositive
  obtain ⟨n,⟨⟨⟨hn,hp⟩,hpR⟩,hn1⟩⟩ :=
    (hev.and hu |>.and hpos |>.and (eventually_gt_atTop (1:ℕ))).exists
  have hnR : 1<(n:ℝ) := by exact_mod_cast hn1
  have hn0 : 0<(n:ℝ) := by linarith
  have hbound := Real.log_le_log hpR hp
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hn0 _).ne',Real.log_rpow hn0] at hbound
  have hln := Real.log_pos hnR
  have hdiv := (div_le_div_of_nonneg_right hbound hln.le)
  have hne := hln.ne'
  have heq : (Real.log K+(-γ+e n)*Real.log (n:ℝ))/Real.log n=
      Real.log K/Real.log n-γ+e n := by field_simp [hne]; ring
  rw [heq] at hdiv
  simp only [Function.comp_apply] at hn
  linarith

end RoughRegime.RateConsequences

namespace RoughRegime.Model

theorem holderOrder_eq_zero_of_le_one (t : ℝ) (ht : t≤1) : holderOrder t=0 := by
  exact Nat.sub_eq_zero_of_le (Nat.ceil_le.mpr (show t≤((1:ℕ):ℝ) by simpa using ht))

theorem Parameters.nu_eq_two_of_le_one (A : Parameters) (hα : A.α≤1) (hβ : A.β≤1) :
    A.nu=2 := by
  simp [Parameters.nu,holderOrder_eq_zero_of_le_one A.α hα,holderOrder_eq_zero_of_le_one A.β hβ]

theorem UpperBracket.eventually_minimax_finite {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hu : UpperBracket T C S ν) :
    ∀ᶠ n : ℕ in atTop,minimaxRMSE n T C≠⊤ := by
  obtain ⟨_,K,_,n0,_,hb⟩ := hu
  filter_upwards [eventually_ge_atTop n0] with n hn
  exact ne_of_lt ((hb n hn).trans_lt ENNReal.ofReal_lt_top)

theorem LowerBracket.eventually_minimax_toReal_pos {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} (hl : LowerBracket T C S)
    (hfinite : ∀ᶠ n : ℕ in atTop,minimaxRMSE n T C≠⊤) :
    ∀ᶠ n : ℕ in atTop,0<(minimaxRMSE n T C).toReal := by
  obtain ⟨c,hc,n0,_,hb⟩ := hl
  filter_upwards [hfinite,eventually_ge_atTop n0,eventually_gt_atTop (1:ℕ)] with n hf hn0 hn1
  have hn : 1<(n:ℝ) := by exact_mod_cast hn1
  have hs : 0<lowerBracketScale S n := by
    unfold lowerBracketScale
    split_ifs
    · exact mul_pos (Rates.scale_pos n S.theta (Rates.tau S.lo S.hi) hn) (Real.log_pos hn)
    · exact Real.rpow_pos_of_pos (by linarith) _
  have h := ENNReal.toReal_mono hf (hb n hn0).1
  rw [ENNReal.toReal_ofReal (mul_pos hc hs).le] at h
  exact (mul_pos hc hs).trans_le h

theorem Bracket.real_parametric_bounds {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hb : Bracket T C S ν) (hparam : 1/2≤S.theta) :
    ∃ c K : ℝ,0<c ∧ 0<K ∧ ∀ᶠ n : ℕ in atTop,
      c*(n:ℝ)^(-(1/2:ℝ))≤(minimaxRMSE n T C).toReal ∧
      (minimaxRMSE n T C).toReal≤K*(n:ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨c,hc,n0,_,hL⟩ := hb.1
  obtain ⟨_,K,hK,n1,_,hU⟩ := hb.2
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [eventually_ge_atTop n0,eventually_ge_atTop n1,eventually_gt_atTop (1:ℕ)]
    with n hn0 hn1 hn
  have hn0R : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hs := Real.rpow_pos_of_pos hn0R (-(1/2:ℝ))
  have hfinite := ne_of_lt ((hU n hn1).trans_lt ENNReal.ofReal_lt_top)
  have hl := (hL n hn0).1
  have hu := hU n hn1
  simp only [lowerBracketScale,upperBracketScale,ite_eq_right (not_lt.mpr hparam)] at hl hu
  have hlr := ENNReal.toReal_mono hfinite hl
  have hur := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal (mul_pos hc hs).le] at hlr
  rw [ENNReal.toReal_ofReal (mul_pos hK hs).le] at hur
  exact ⟨hlr,hur⟩

theorem Bracket.log_polynomial_exponent {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hb : Bracket T C S ν) :
    Tendsto (fun n : ℕ => Real.log (minimaxRMSE n T C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) S.theta)) := by
  by_cases hrough : S.theta<1/2
  · rw [min_eq_right hrough.le]
    exact RateConsequences.polynomial_exponent_of_log_refinement _ S.theta _
      ((hb.log_refinement hrough).trans_isLittleO RateConsequences.loglog_nat_isLittleO_sqrtlog)
  · rw [min_eq_left (le_of_not_gt hrough)]
    obtain ⟨c,K,hc,hK,hreal⟩ := hb.real_parametric_bounds (le_of_not_gt hrough)
    exact RateConsequences.parametric_polynomial_exponent _ c K hc hK hreal

theorem separated_log_polynomial_exponent {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hl : LowerBracket T C S)
    (hu : ∀ ζ : ℝ, ∀ hζ : 0<ζ, ∀ hζ1 : ζ<1,
      UpperBracket T C (widenedBracketParameters S ζ hζ hζ1) ν) :
    Tendsto (fun n : ℕ => Real.log (minimaxRMSE n T C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) S.theta)) := by
  by_cases hrough : S.theta<1/2
  · rw [min_eq_right hrough.le]
    exact RateConsequences.polynomial_exponent_of_log_refinement _ S.theta _
      (separated_log_risk T C S ν hrough hl hu)
  · have hupper : UpperBracket T C S ν := by
      obtain ⟨hν,K,hK,n0,hn0,hb⟩ := hu (1/2) (by norm_num) (by norm_num)
      refine ⟨hν,K,hK,n0,hn0,?_⟩
      intro n hn
      simpa only [upperBracketScale,widenedBracketParameters,ite_eq_right hrough] using hb n hn
    exact (show Bracket T C S ν from ⟨hl,hupper⟩).log_polynomial_exponent

/-- The exponent claimed by HOIF-type polynomial rates, in the paper's theta
notation: `2 theta/(2 theta+1) = 4 s/(4 s+d)`. -/
def hoifExponent (θ : ℝ) : ℝ := 2*θ/(2*θ+1)

theorem hoifExponent_gt (θ : ℝ) (hθ : 0<θ) (hrough : θ<1/2) : θ<hoifExponent θ := by
  unfold hoifExponent
  apply (lt_div_iff₀ (by linarith : 0<2*θ+1)).mpr
  nlinarith

theorem hoifExponent_eq_source (s d : ℝ) (hs : 0<s) (hd : 0<d) :
    hoifExponent (2*s/d)=4*s/(4*s+d) := by
  have hden : 4*s+d≠0 := (by positivity : 0<4*s+d).ne'
  unfold hoifExponent
  field_simp [hd.ne',hden]
  <;> ring

theorem not_hoif_upper_of_polynomial_exponent {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (hrough : S.theta<1/2)
    (hpos : ∀ᶠ n : ℕ in atTop,0<(minimaxRMSE n T C).toReal)
    (hlog : Tendsto (fun n : ℕ => Real.log (minimaxRMSE n T C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) S.theta)))
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,minimaxRMSE n T C≤
      ENNReal.ofReal (K*(n:ℝ)^(-hoifExponent S.theta+e n)) := by
  intro hupper
  have hreal : ∀ᶠ n : ℕ in atTop,(minimaxRMSE n T C).toReal≤
      K*(n:ℝ)^(-hoifExponent S.theta+e n) := by
    filter_upwards [hupper,eventually_gt_atTop (1:ℕ)] with n hn hn1
    have hnR : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    rw [ENNReal.toReal_ofReal (mul_pos hK (Real.rpow_pos_of_pos hnR _)).le] at h
    exact h
  rw [min_eq_right hrough.le] at hlog
  exact RateConsequences.not_faster_polynomial_upper _ S.theta (hoifExponent S.theta) K
    (hoifExponent_gt S.theta S.htheta hrough) hK hpos hlog e he hreal

theorem Bracket.not_hoif_upper {Ω : Type*} [MeasurableSpace Ω]
    {T : ProbabilityMeasure Ω→ℝ} {C : Set (ProbabilityMeasure Ω)}
    {S : BracketParameters} {ν : ℝ} (hb : Bracket T C S ν) (hrough : S.theta<1/2)
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,minimaxRMSE n T C≤
      ENNReal.ofReal (K*(n:ℝ)^(-hoifExponent S.theta+e n)) :=
  not_hoif_upper_of_polynomial_exponent T C S hrough
    (hb.1.eventually_minimax_toReal_pos hb.2.eventually_minimax_finite)
    hb.log_polynomial_exponent e he K hK

theorem separated_not_hoif_upper {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (S : BracketParameters) (ν : ℝ) (hl : LowerBracket T C S)
    (hu : ∀ ζ : ℝ, ∀ hζ : 0<ζ, ∀ hζ1 : ζ<1,
      UpperBracket T C (widenedBracketParameters S ζ hζ hζ1) ν)
    (hrough : S.theta<1/2) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,minimaxRMSE n T C≤
      ENNReal.ofReal (K*(n:ℝ)^(-hoifExponent S.theta+e n)) :=
  not_hoif_upper_of_polynomial_exponent T C S hrough
    (hl.eventually_minimax_toReal_pos (hu (1/2) (by norm_num) (by norm_num)).eventually_minimax_finite)
    (separated_log_polynomial_exponent T C S ν hl hu) e he K hK

theorem main_log_polynomial_exponent (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
    (hnd : Nondegenerate A F π) (hr : 0<r)
    (C : Set (ProbabilityMeasure (Observation A Z)))
    (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F) :
    Tendsto (fun n : ℕ => Real.log (minimaxRMSE n (target A F) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) A.theta)) :=
  (model_bracket A F π r hnd hr C hC hCM).log_polynomial_exponent

theorem main_not_hoif_upper (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (r : ℝ)
    (hnd : Nondegenerate A F π) (hr : 0<r)
    (C : Set (ProbabilityMeasure (Observation A Z)))
    (hC : localClass A F π r⊆C) (hCM : C⊆modelClass A F)
    (hrough : A.theta<1/2) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,minimaxRMSE n (target A F) C≤
      ENNReal.ofReal (K*(n:ℝ)^(-hoifExponent A.theta+e n)) :=
  (model_bracket A F π r hnd hr C hC hCM).not_hoif_upper hrough e he K hK

end RoughRegime.Model
