module

public import RoughRegime.ApplicationsRisk
public import RoughRegime.ModelParametricEstimator


@[expose] public section
/-! Risk assembly on two independent sample blocks. A measurable clipped
 estimator inherits its conditional good-pilot bound, with the square root
 of the actual bad-pilot probability as the additional error. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Applications
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

 def clipUnit (t : ℝ) : ℝ := (Set.projIcc 0 1 (by norm_num) t:ℝ)

 theorem clipUnit_measurable : Measurable clipUnit :=
   continuous_subtype_val.measurable.comp continuous_projIcc.measurable

 theorem clipUnit_error_le (t target : ℝ) (ht : target∈Icc (0:ℝ) 1) :
     |clipUnit t-target|≤|t-target| := by
   have h := Set.abs_projIcc_sub_projIcc (a:=0) (b:=1) (by norm_num) (c:=t) (d:=target)
   simpa only [Set.projIcc_of_mem (by norm_num) ht,clipUnit] using h

 theorem clipUnit_error_bound (t target : ℝ) (ht : target∈Icc (0:ℝ) 1) :
     |clipUnit t-target|≤1 := by
   have hc := (Set.projIcc 0 1 (by norm_num) t).property
   dsimp only [clipUnit]
   rw [abs_le]
   constructor <;> linarith [hc.1,hc.2,ht.1,ht.2]

 theorem clipped_conditional_eLpNorm {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
     (μ : Measure P) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
     (E : P×Ω→ℝ) (hE : Measurable E) (good : Set P) (hgood : MeasurableSet good)
     (target r b : ℝ) (ht : target∈Icc (0:ℝ) 1) (hr : 0≤r) (hb : 0≤b)
     (hbad : μ goodᶜ≤ENNReal.ofReal b)
     (hconditional : ∀ p ∈ good, eLpNorm (fun y => E (p,y)-target) 2 ν ≤ ENNReal.ofReal r) :
     eLpNorm (fun q=>clipUnit (E q)-target) 2 (μ.prod ν)≤ENNReal.ofReal (r+Real.sqrt b) := by
   let err : P×Ω→ℝ := fun q=>clipUnit (E q)-target
   have hm : Measurable err := (clipUnit_measurable.comp hE).sub measurable_const
   have hsection (p : P) : Measurable (fun y=>err (p,y)) := hm.comp measurable_prodMk_left
   have hsqgood (p : P) (hp : p∈good) :
       (∫⁻ y,ENNReal.ofReal ((err (p,y))^2) ∂ν)≤ENNReal.ofReal (r^2) := by
     have he : eLpNorm (fun y=>err (p,y)) 2 ν≤ENNReal.ofReal r :=
       (eLpNorm_mono_ae (hsection p).aestronglyMeasurable (ae_of_all ν (fun y=>by
         simpa only [Real.norm_eq_abs] using clipUnit_error_le (E (p,y)) target ht))).trans (hconditional p hp)
     rw [eLpNorm_two_eq_squaredIntegral ν _ (hsection p)] at he
     have hp := ENNReal.rpow_le_rpow he (by norm_num : (0:ℝ)≤2)
     rw [←ENNReal.rpow_mul] at hp
     norm_num only [one_div_mul_cancel,ENNReal.rpow_one,ENNReal.rpow_two] at hp
     simpa only [←ENNReal.ofReal_pow hr 2] using hp
   have hsqall (p : P) : (∫⁻ y,ENNReal.ofReal ((err (p,y))^2) ∂ν)≤1 := by
     calc
       _ ≤ ∫⁻ _y:Ω,(1:ℝ≥0∞) ∂ν := lintegral_mono (fun y=>by
         apply (ENNReal.ofReal_le_ofReal _).trans_eq (by norm_num : ENNReal.ofReal (1:ℝ)=1)
         have ha := clipUnit_error_bound (E (p,y)) target ht
         have hs := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr ha
         simpa only [sq_abs,one_pow] using hs)
       _ = 1 := by simp
   have hlin : (∫⁻ q,ENNReal.ofReal ((err q)^2) ∂μ.prod ν)≤ENNReal.ofReal (r^2)+ENNReal.ofReal b := by
     rw [lintegral_prod _ ((hm.pow_const 2).ennreal_ofReal.aemeasurable)]
     calc
       _ ≤ ∫⁻ p,ENNReal.ofReal (r^2)+goodᶜ.indicator (fun _=>(1:ℝ≥0∞)) p ∂μ := by
         apply lintegral_mono
         intro p
         dsimp only
         by_cases hp : p∈good
         · simpa only [indicator_of_notMem (by simpa using hp : p∉goodᶜ),add_zero] using hsqgood p hp
         · rw [indicator_of_mem (by simpa using hp : p∈goodᶜ)]
           exact (hsqall p).trans le_add_self
       _ = ENNReal.ofReal (r^2)+μ goodᶜ := by
         rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
         congr 1
         simpa only [Pi.one_def] using lintegral_indicator_one (μ:=μ) hgood.compl
       _ ≤ _ := add_le_add_right hbad _
   have hn : r^2+b≤(r+Real.sqrt b)^2 := by
     nlinarith [Real.sq_sqrt hb,mul_nonneg hr (Real.sqrt_nonneg b)]
   have hlin' : (∫⁻ q,ENNReal.ofReal ((err q)^2) ∂μ.prod ν)≤ENNReal.ofReal ((r+Real.sqrt b)^2) := by
     rw [←ENNReal.ofReal_add (sq_nonneg r) hb] at hlin
     exact hlin.trans (ENNReal.ofReal_le_ofReal hn)
   rw [eLpNorm_two_eq_squaredIntegral _ _ hm]
   have hh := ENNReal.rpow_le_rpow hlin' (by norm_num : (0:ℝ)≤1/2)
   rw [ENNReal.ofReal_pow (add_nonneg hr (Real.sqrt_nonneg b)) 2,←ENNReal.rpow_two,
     ←ENNReal.rpow_mul] at hh
   norm_num only [mul_one_div_cancel,ENNReal.rpow_one] at hh
   exact hh

end RoughRegime.Applications
