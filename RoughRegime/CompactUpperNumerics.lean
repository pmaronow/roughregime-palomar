module

public import RoughRegime.UpperSubcriticalTuning
public import RoughRegime.CompactDensityParameters


@[expose] public section
/-! Common numerical tuning on a compact range of density conditioning
constants. Each interval keeps its own tau and its own sharp rate. -/
noncomputable section
open Filter Set
namespace RoughRegime.UpperSubcritical
open RoughRegime.UpperDegreeRules RoughRegime.UpperParametric
set_option maxHeartbeats 1000000

lemma tuningValid_of_numeric_thresholds (n θ τ A Cv : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (hA : 0≤A) (hCv : 1≤Cv)
    (hn : 0<n) (hL : 1≤Real.log n)
    (hLC : Cv*highDegreeConstant θ τ A ν≤Real.log n)
    (hLg : Cv*globalDegreeConstant θ τ A ν≤Real.log n)
    (hLκ : (4*RoughRegime.Rates.kappa θ τ/(1-2*θ))^2≤Real.log n)
    (hLX : (2*windowConstant θ τ Cv (highDegreeConstant θ τ A ν)*((ν:ℝ)+3)/(1-2*θ))^2≤Real.log n)
    (hSq : (Real.log n)^2/n≤1)
    (hSz : (2*globalDegreeConstant θ τ A ν)*(Real.log n/n)≤1) :
    TuningValid n θ τ A Cv ν := by
  let Δ := 1 - 2 * θ
  let κ := RoughRegime.Rates.kappa θ τ
  let CR := highDegreeConstant θ τ A ν
  let CX := windowConstant θ τ Cv CR
  let Cg := globalDegreeConstant θ τ A ν
  have hΔ : 0 < Δ := by dsimp [Δ]; linarith
  have hκ : 0 < κ := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hCvp : 0 < Cv := zero_lt_one.trans_le hCv
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCR : 0 ≤ CR := by unfold CR highDegreeConstant; positivity
  have hCX : 0 ≤ CX := by unfold CX windowConstant; positivity
  have hCg : 0 ≤ Cg := by unfold Cg globalDegreeConstant levelCountConstant; positivity
  have hLp : 0 < Real.log n := zero_lt_one.trans_le hL
  have hsp : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hLp
  have hs := Real.sq_sqrt hLp.le
  have hsle : Real.sqrt (Real.log n) ≤ Real.log n := by nlinarith [Real.sqrt_nonneg (Real.log n)]
  have hnSq : (Real.log n) ^ 2 ≤ n := (div_le_one hn).mp hSq
  have hR := highDegreeEnvelope_bound n θ τ A ν hL hθ hθhalf hτ hA
  have hRs : Cv * highDegreeEnvelope n θ τ A ν ≤ (Real.log n) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hR hCvp.le
    have h2 := mul_le_mul_of_nonneg_right hLC hsp.le
    have h3 := mul_le_mul_of_nonneg_left hsle hLp.le
    nlinarith
  have hκs : 4 * κ / Δ ≤ Real.sqrt (Real.log n) := by
    have h := Real.sqrt_le_sqrt hLκ
    change Real.sqrt ((4*κ/Δ)^2)≤Real.sqrt (Real.log n) at h
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 4 * κ / Δ)] using h
  have hκmul := (div_le_iff₀ hΔ).mp hκs
  have hBhalf : Δ * Real.log n / 2 ≤ budget n θ τ := by
    have hm := mul_le_mul_of_nonneg_right hκmul hsp.le
    dsimp [budget, Δ, κ] at *
    nlinarith
  have hBp : 0 < budget n θ τ := (by positivity : 0 < Δ * Real.log n / 2).trans_le hBhalf
  have hXs : 2 * CX * ((ν : ℝ) + 3) / Δ ≤ Real.sqrt (Real.log n) := by
    have h := Real.sqrt_le_sqrt hLX
    change Real.sqrt ((2*CX*((ν:ℝ)+3)/Δ)^2)≤Real.sqrt (Real.log n) at h
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2 * CX * ((ν : ℝ) + 3) / Δ)] using h
  have hXmul := (div_le_iff₀ hΔ).mp hXs
  have hXenv := windowEndpoint_bound n θ τ A Cv ν hL hθ hθhalf hτ hA hCvp
  have hXp := windowEndpoint_positive n θ τ A Cv ν hL hθ hθhalf hτ hA hCv
  have hfloor : (ν : ℝ) + 3 ≤ budget n θ τ / windowEndpoint (terminal n θ τ) Cv (highDegreeEnvelope n θ τ A ν) n := by
    apply (le_div_iff₀ hXp).mpr
    have hm := mul_le_mul_of_nonneg_left hXenv (show 0 ≤ (ν : ℝ) + 3 by positivity)
    have hx := mul_le_mul_of_nonneg_right hXmul hsp.le
    dsimp [CX, CR] at hx
    nlinarith
  have hsize : 2 * Cg * Real.log n ≤ n := by
    have h := (div_le_one hn).mp (show 2 * Cg * Real.log n / n ≤ 1 by convert hSz using 1; ring)
    simpa only [one_mul] using h
  refine ⟨hn, hL, hnSq, hRs, hBp, hfloor, hLg, ?_⟩
  intro j
  have hd := chosenDegree_global_bound n θ τ A Cv ν hL hθ hθhalf hτ hA j
  have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [Cg] at hsize
  exact hm.trans (by convert hsize using 1; ring)


def tuningThresholdEnvelope (θ τ A Cv : ℝ) (ν : ℕ) : ℝ :=
  max (Cv*highDegreeConstant θ τ A ν)
    (max (Cv*globalDegreeConstant θ τ A ν)
      (max ((4*RoughRegime.Rates.kappa θ τ/(1-2*θ))^2)
        ((2*windowConstant θ τ Cv (highDegreeConstant θ τ A ν)*((ν:ℝ)+3)/(1-2*θ))^2)))

lemma highDegreeConstant_positive_all (θ τ A : ℝ) (ν : ℕ) (hθ : 0<θ) (hA : 0≤A) :
    0<highDegreeConstant θ τ A ν := by
  unfold highDegreeConstant RoughRegime.Rates.kappa
  have hlog2:=Real.log_pos (by norm_num : (1:ℝ)<2)
  positivity

lemma tuningThresholdEnvelope_continuous (θ A Cv : ℝ) (ν : ℕ) (hθ : 0<θ) (hA : 0≤A) :
    Continuous (fun τ=>tuningThresholdEnvelope θ τ A Cv ν) := by
  have hκ : Continuous (fun τ=>RoughRegime.Rates.kappa θ τ) := by
    unfold RoughRegime.Rates.kappa
    fun_prop
  have hCR : Continuous (fun τ=>highDegreeConstant θ τ A ν) := by
    unfold highDegreeConstant RoughRegime.Rates.kappa
    fun_prop
  have hlogCR : Continuous (fun τ=>Real.log (highDegreeConstant θ τ A ν)) :=
    hCR.log (fun τ=>(highDegreeConstant_positive_all θ τ A ν hθ hA).ne')
  unfold tuningThresholdEnvelope windowConstant globalDegreeConstant levelCountConstant
  fun_prop

/-- One sample cutoff validates all actual source degrees on an arbitrary
fixed positive compact tau range. The degree slope and variance constant
are common, while terminal resolution and cap use each interval's tau. -/
theorem tuning_valid_eventually_uniform (θ τlo τhi A Cv : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτlo : 0<τlo) (hA : 0≤A) (hCv : 1≤Cv) :
    ∀ᶠn:ℝ in atTop,∀τ∈Icc τlo τhi,TuningValid n θ τ A Cv ν := by
  obtain ⟨B,hB,hbound⟩:=((isCompact_Icc : IsCompact (Icc τlo τhi)).bddAbove_image
    (tuningThresholdEnvelope_continuous θ A Cv ν hθ hA).continuousOn).exists_ge (1:ℝ)
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (2*B)
  simp only [mul_zero] at hsmall
  filter_upwards [eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop B,
    logSquare_div_sample_tendsto_zero.eventually_le_const (by norm_num : (0:ℝ)<1),
    hsmall.eventually_le_const (by norm_num : (0:ℝ)<1)] with n hn hL hLB hSq hSz
  intro τ hτ
  have hτp:=hτlo.trans_le hτ.1
  have hbτ:tuningThresholdEnvelope θ τ A Cv ν≤B:=hbound _ ⟨τ,hτ,rfl⟩
  have hb1:Cv*highDegreeConstant θ τ A ν≤B := (le_max_left _ _).trans hbτ
  have hb2:Cv*globalDegreeConstant θ τ A ν≤B :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hbτ
  have hb3:(4*RoughRegime.Rates.kappa θ τ/(1-2*θ))^2≤B :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hbτ
  have hb4:(2*windowConstant θ τ Cv (highDegreeConstant θ τ A ν)*((ν:ℝ)+3)/(1-2*θ))^2≤B :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hbτ
  have hg:0≤globalDegreeConstant θ τ A ν := by
    unfold globalDegreeConstant levelCountConstant RoughRegime.Rates.kappa
    have:=Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  have hgB:globalDegreeConstant θ τ A ν≤B :=
    (le_mul_of_one_le_left hg hCv).trans hb2
  apply tuningValid_of_numeric_thresholds n θ τ A Cv ν hθ hθhalf hτp hA hCv hn hL
    (hb1.trans hLB) (hb2.trans hLB) (hb3.trans hLB) (hb4.trans hLB) hSq
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgB (by norm_num))
    (div_nonneg (zero_le_one.trans hL) hn.le)).trans hSz


lemma kappa_mono_tau (θ τ τ' : ℝ) (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : τ≤τ') :
    RoughRegime.Rates.kappa θ τ≤RoughRegime.Rates.kappa θ τ' := by
  unfold RoughRegime.Rates.kappa
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
  exact mul_le_mul_of_nonneg_left hτ (by nlinarith)

lemma lowVariance_relative_rate_uniform (θ τhi : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hθhalf : θ<1/2) :
    ∀ᶠn:ℝ in atTop,∀τ,τ≤τhi→
      (Real.log n)^(3/2:ℝ)/Real.sqrt n≤rate n θ τ ν := by
  have he:=(lowVariance_relative_rate_tendsto_zero θ τhi ν hθhalf).eventually_le_const
    (by norm_num : (0:ℝ)<1)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with n hn hn1
  intro τ hτ
  have hnp:0<n:=zero_lt_one.trans hn1
  have hLp:=Real.log_pos hn1
  have hratep:=rate_positive n θ τhi ν hn1
  have h := (div_le_one hratep).mp hn
  apply h.trans
  have hk:=kappa_mono_tau θ τ τhi hθ hθhalf hτ
  have hx:=Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg (Real.log n))))
  unfold rate
  exact mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using hx) (by positivity)

lemma riskConstant_continuous_tau (θ A Cv C0 Cproj : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hA : 0≤A) :
    Continuous (fun τ=>riskConstant θ τ A Cv C0 Cproj ν) := by
  have hκ : Continuous (fun τ=>RoughRegime.Rates.kappa θ τ) := by
    unfold RoughRegime.Rates.kappa
    fun_prop
  have hCR : Continuous (fun τ=>highDegreeConstant θ τ A ν) := by
    unfold highDegreeConstant
    fun_prop
  have hlogCR : Continuous (fun τ=>Real.log (highDegreeConstant θ τ A ν)) :=
    hCR.log (fun τ=>(highDegreeConstant_positive_all θ τ A ν hθ hA).ne')
  have hCX : Continuous (fun τ=>windowConstant θ τ Cv (highDegreeConstant θ τ A ν)) := by
    unfold windowConstant
    fun_prop
  have hrpow : Continuous (fun τ=>(Cv*highDegreeConstant θ τ A ν)^θ) :=
    (continuous_const.mul hCR).rpow_const (fun _=>Or.inr hθ.le)
  unfold riskConstant capConstant RoughRegime.UpperRates.cappedBiasConstant
    globalDegreeConstant levelCountConstant
  fun_prop

lemma chosen_total_error_bound_of_valid (n θ τ A Cv C0 Cproj q : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) (hA : 0≤A) (hCv : 1≤Cv)
    (hC0 : 0≤C0) (hCproj : 0≤Cproj) (hq : 0≤q) (hν : 2≤ν)
    (hdecay : θ*Real.log 2+1≤τ*A) (hn : TuningValid n θ τ A Cv ν)
    (hlRate : (Real.log n)^(3/2:ℝ)/Real.sqrt n≤rate n θ τ ν)
    (v : Fin (terminal n θ τ+1)→ℝ)
    (hv : ∀j,v j≤Cv*(parentCells (terminal n θ τ) j:ℝ)^(-2*q)/n+
      ∑k∈Finset.range (chosenDegree n θ τ A Cv ν j-1),
        RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k+2)) :
    Cproj*((2:ℝ)^terminal n θ τ)^(-θ)+
      C0*(∑j:Fin (terminal n θ τ+1),approximationWeight (parentCells (terminal n θ τ) j)
        θ τ ν (chosenOrder n θ τ A Cv ν j))+
      (∑j:Fin (terminal n θ τ+1),Real.sqrt (v j))≤
        riskConstant θ τ A Cv C0 Cproj ν*rate n θ τ ν := by
  have hnp:=hn.sample_positive
  have hs := chosen_standard_deviation_sum_bound n θ τ A Cv q ν hn.sample_positive hn.log_sample_one hθ hθhalf hτ hA
    (zero_lt_one.trans_le hCv) hq hn.log_square_le_sample hn.budget_positive.le hn.low_degree_small hn.floor_large v hv
  have hb := chosen_bias_sum_bound n θ τ A Cv ν hn.sample_positive hn.log_sample_one hθ hθhalf hτ hA hCv hdecay
    hn.log_square_le_sample hn.resolution_small hn.budget_positive hn.floor_large
  have ht := terminal_bias_bound n θ τ hn.log_sample_one hn.sample_positive hθ hθhalf hτ
  have hp := highVariance_logPower_bound n θ τ ν hn.sample_positive hn.log_sample_one hθ.le hν
  have hpower : 1 ≤ (Real.log n) ^ (θ / 2 + (ν : ℝ) / 2 + 1 / 4) := Real.one_le_rpow hn.log_sample_one (by positivity)
  have htRate : ((2 : ℝ) ^ terminal n θ τ) ^ (-θ) ≤ rate n θ τ ν := by
    apply ht.trans
    unfold rate
    convert mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ n ^ (-θ) * Real.exp (-RoughRegime.Rates.kappa θ τ * Real.sqrt (Real.log n)) by positivity) using 1 <;> ring
  have hk := RoughRegime.Rates.kappa_pos θ τ hθ hθhalf hτ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCJ : 0 ≤ levelCountConstant θ τ := by unfold levelCountConstant; positivity
  have hsdRate : (∑ j : Fin (terminal n θ τ + 1), Real.sqrt (v j)) ≤
      (levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν) +
        levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν)) * rate n θ τ ν := by
    refine hs.trans ?_
    convert add_le_add (mul_le_mul_of_nonneg_left hlRate (by positivity : 0 ≤ levelCountConstant θ τ * Real.sqrt (Cv * globalDegreeConstant θ τ A ν)))
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ levelCountConstant θ τ * Real.sqrt (Cv * highDegreeConstant θ τ A ν))) using 1 <;> ring
  unfold riskConstant
  convert add_le_add (add_le_add (mul_le_mul_of_nonneg_left htRate hCproj) (mul_le_mul_of_nonneg_left hb hC0)) hsdRate using 1; ring


/-- The full sharp finite bias-plus-standard-deviation estimate uses one
constant and one sample cutoff throughout a compact positive tau range. -/
theorem chosen_total_error_bound_eventually_uniform
    (θ τlo τhi A Cv C0 Cproj q : ℝ) (ν : ℕ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτlo : 0<τlo) (hA : 0≤A) (hCv : 1≤Cv)
    (hC0 : 0≤C0) (hCproj : 0≤Cproj) (hq : 0≤q) (hν : 2≤ν)
    (hdecay : θ*Real.log 2+1≤τlo*A) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℝ in atTop,∀τ∈Icc τlo τhi,
      ∀v:Fin (terminal n θ τ+1)→ℝ,
      (∀j,v j≤Cv*(parentCells (terminal n θ τ) j:ℝ)^(-2*q)/n+
        ∑k∈Finset.range (chosenDegree n θ τ A Cv ν j-1),
          RoughRegime.LiftVariance.varianceTerm Cv (parentCells (terminal n θ τ) j) n (k+2))→
      Cproj*((2:ℝ)^terminal n θ τ)^(-θ)+
        C0*(∑j:Fin (terminal n θ τ+1),approximationWeight (parentCells (terminal n θ τ) j)
          θ τ ν (chosenOrder n θ τ A Cv ν j))+
        (∑j:Fin (terminal n θ τ+1),Real.sqrt (v j))≤C*rate n θ τ ν := by
  obtain ⟨C,hC,hbound⟩:=((isCompact_Icc : IsCompact (Icc τlo τhi)).bddAbove_image
    (riskConstant_continuous_tau θ A Cv C0 Cproj ν hθ hA).continuousOn).exists_ge (1:ℝ)
  refine ⟨C,zero_lt_one.trans_le hC,?_⟩
  filter_upwards [tuning_valid_eventually_uniform θ τlo τhi A Cv ν hθ hθhalf hτlo hA hCv,
    lowVariance_relative_rate_uniform θ τhi ν hθ hθhalf,eventually_gt_atTop (1:ℝ)]
    with n hn hl hn1
  intro τ hτ v hv
  have hdecayτ : θ*Real.log 2+1≤τ*A :=
    hdecay.trans (mul_le_mul_of_nonneg_right hτ.1 hA)
  apply (chosen_total_error_bound_of_valid n θ τ A Cv C0 Cproj q ν hθ hθhalf
    (hτlo.trans_le hτ.1) hA hCv hC0 hCproj hq hν hdecayτ (hn τ hτ) (hl τ hτ.2) v hv).trans
  exact mul_le_mul_of_nonneg_right (hbound _ ⟨τ,hτ,rfl⟩) (rate_positive n θ τ ν hn1).le

end RoughRegime.UpperSubcritical
